// Lean compiler output
// Module: Lean.Elab.Quotation.Precheck
// Imports: Lean.KeyedDeclsAttribute Lean.Parser.Command Lean.Elab.Term Lean.Elab.Quotation.Util
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
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2___closed__1;
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__3;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__1;
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__2;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__5;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2___at_Lean_Elab_Term_Quotation_precheckChoice___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__2;
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__3;
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__6;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__5;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__2;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2;
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_withNewLocals___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___closed__3;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute;
static lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__2;
static double l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__4;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__2;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Term_Quotation_precheckChoice___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckUnop___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__9;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__5;
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___closed__2;
lean_object* l_Lean_Elab_addConstInfo___at_Lean_KeyedDeclsAttribute_Def_evalKey___default___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2___at_Lean_Elab_Term_Quotation_precheckChoice___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__10;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckBinop___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__5;
lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1(lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_withNewLocals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
static lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__4;
static lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__2;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheck___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__3;
lean_object* l_Lean_Elab_realizeGlobalNameWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__6;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__5;
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__4;
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__1;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
extern lean_object* l_Lean_inheritedTraceOptions;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__5;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_runPrecheck___closed__2;
LEAN_EXPORT lean_object* l_observing___at_Lean_Elab_Term_Quotation_precheckChoice___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__3;
static lean_object* l_Lean_Elab_Term_Quotation_runPrecheck___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Term_Quotation_precheckChoice___spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__3;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__4;
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__7;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1;
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10;
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__3;
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__7;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__3;
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__1;
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__12;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__4;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__5;
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_Elab_Term_Quotation_hygiene;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__4;
uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__6;
static lean_object* l_Lean_Elab_Term_Quotation_precheckRightact___closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1;
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_1, x_11);
x_13 = lean_apply_8(x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_withNewLocal___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_withNewLocals___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_box(0);
x_8 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_6, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
x_16 = lean_apply_8(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_withNewLocals___spec__1(x_1, x_17, x_18, x_3);
x_20 = lean_apply_8(x_2, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_withNewLocals___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_withNewLocals___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_withNewLocals___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Quotation_withNewLocals___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quotPrecheck", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Enable eager name analysis on notations in order to find unbound identifiers early.\nNote that type-sensitive syntax (\"elaborators\") needs special support for this kind of check, so it might need to be turned off when using such syntax.", 235, 235);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Quotation", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__2;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__5;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__10;
x_5 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("allowSectionVars", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__1;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Allow occurrences of section variables in checked quotations, it is useful when declaring local notation.", 105, 105);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__1;
x_6 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__1;
x_7 = l_Lean_Name_mkStr6(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__2;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__4;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__5;
x_5 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_7____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Attribute_Builtin_getIdent(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Syntax_getId(x_7);
x_10 = lean_st_ref_get(x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_4, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 6);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Environment_contains(x_13, x_9);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_3);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_18, sizeof(void*)*2);
lean_dec(x_18);
if (x_20 == 0)
{
lean_dec(x_7);
lean_dec(x_3);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_14);
x_21 = lean_box(0);
lean_inc(x_9);
x_22 = l_Lean_Elab_addConstInfo___at_Lean_KeyedDeclsAttribute_Def_evalKey___default___spec__1(x_7, x_9, x_21, x_3, x_4, x_17);
lean_dec(x_3);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
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
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_14, 0);
x_32 = lean_ctor_get(x_14, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_14);
x_33 = lean_ctor_get(x_31, 6);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Environment_contains(x_13, x_9);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_33);
lean_dec(x_7);
lean_dec(x_3);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_9);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_ctor_get_uint8(x_33, sizeof(void*)*2);
lean_dec(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_7);
lean_dec(x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_box(0);
lean_inc(x_9);
x_39 = l_Lean_Elab_addConstInfo___at_Lean_KeyedDeclsAttribute_Def_evalKey___default___spec__1(x_7, x_9, x_38, x_3, x_4, x_32);
lean_dec(x_3);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_9);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_6);
if (x_47 == 0)
{
return x_6;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_6);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("builtin_quot_precheck", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("quot_precheck", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Precheck", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__5;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Register a double backtick syntax quotation pre-check.\n\n[quot_precheck k] registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the `SyntaxNodeKind` `k`.\nIt should implement eager name analysis on the passed syntax by throwing an exception on unbound identifiers,\nand calling `precheck` recursively on nested terms, potentially with an extended local context (`withNewLocal`).\nMacros without registered precheck hook are unfolded, and identifier-less syntax is ultimately assumed to be well-formed.", 516, 516);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__3___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__2;
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__4;
x_3 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__7;
x_4 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__6;
x_5 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__8;
x_6 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__9;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckAttribute", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__11;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10;
x_3 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__12;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__2(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__3(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
uint8_t x_2; 
lean_dec(x_1);
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
lean_inc(x_1);
x_3 = l_Lean_Syntax_isAnyAntiquot(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_Syntax_getArgs(x_1);
lean_dec(x_1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___spec__1(x_4, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_1);
x_12 = 0;
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2___closed__1;
x_11 = lean_st_ref_get(x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_7, 2);
x_15 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_13, x_14, x_1);
lean_dec(x_13);
x_16 = lean_box(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_ctor_get(x_7, 2);
x_20 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption(x_17, x_19, x_1);
lean_dec(x_17);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
static double _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_take(x_9, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; double x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_17, 3);
x_21 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1;
x_22 = 0;
x_23 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3;
x_24 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_float(x_24, sizeof(void*)*2, x_21);
lean_ctor_set_float(x_24, sizeof(void*)*2 + 8, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 16, x_22);
x_25 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
x_26 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_13);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_11);
lean_ctor_set(x_15, 1, x_26);
lean_ctor_set(x_15, 0, x_11);
x_27 = l_Lean_PersistentArray_push___rarg(x_20, x_15);
lean_ctor_set(x_17, 3, x_27);
x_28 = lean_st_ref_set(x_9, x_17, x_19);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; double x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_35 = lean_ctor_get(x_15, 1);
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
x_38 = lean_ctor_get(x_17, 2);
x_39 = lean_ctor_get(x_17, 3);
x_40 = lean_ctor_get(x_17, 4);
x_41 = lean_ctor_get(x_17, 5);
x_42 = lean_ctor_get(x_17, 6);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_43 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1;
x_44 = 0;
x_45 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3;
x_46 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_float(x_46, sizeof(void*)*2, x_43);
lean_ctor_set_float(x_46, sizeof(void*)*2 + 8, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*2 + 16, x_44);
x_47 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
x_48 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_13);
lean_ctor_set(x_48, 2, x_47);
lean_inc(x_11);
lean_ctor_set(x_15, 1, x_48);
lean_ctor_set(x_15, 0, x_11);
x_49 = l_Lean_PersistentArray_push___rarg(x_39, x_15);
x_50 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_50, 0, x_36);
lean_ctor_set(x_50, 1, x_37);
lean_ctor_set(x_50, 2, x_38);
lean_ctor_set(x_50, 3, x_49);
lean_ctor_set(x_50, 4, x_40);
lean_ctor_set(x_50, 5, x_41);
lean_ctor_set(x_50, 6, x_42);
x_51 = lean_st_ref_set(x_9, x_50, x_35);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; double x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_15);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_56, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 5);
lean_inc(x_63);
x_64 = lean_ctor_get(x_56, 6);
lean_inc(x_64);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 x_65 = x_56;
} else {
 lean_dec_ref(x_56);
 x_65 = lean_box(0);
}
x_66 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1;
x_67 = 0;
x_68 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3;
x_69 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set_float(x_69, sizeof(void*)*2, x_66);
lean_ctor_set_float(x_69, sizeof(void*)*2 + 8, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*2 + 16, x_67);
x_70 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
x_71 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_13);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_11);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_11);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_PersistentArray_push___rarg(x_61, x_72);
if (lean_is_scalar(x_65)) {
 x_74 = lean_alloc_ctor(0, 7, 0);
} else {
 x_74 = x_65;
}
lean_ctor_set(x_74, 0, x_58);
lean_ctor_set(x_74, 1, x_59);
lean_ctor_set(x_74, 2, x_60);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 4, x_62);
lean_ctor_set(x_74, 5, x_63);
lean_ctor_set(x_74, 6, x_64);
x_75 = lean_st_ref_set(x_9, x_74, x_57);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_14);
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_1 = x_13;
x_9 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_15);
x_23 = l_Lean_MessageData_ofFormat(x_22);
x_24 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3(x_14, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_1 = x_13;
x_9 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 5);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_8, 5, x_13);
x_14 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
x_24 = lean_ctor_get(x_8, 9);
x_25 = lean_ctor_get(x_8, 10);
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_27 = lean_ctor_get(x_8, 11);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_29 = l_Lean_replaceRef(x_1, x_20);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_16);
lean_ctor_set(x_30, 2, x_17);
lean_ctor_set(x_30, 3, x_18);
lean_ctor_set(x_30, 4, x_19);
lean_ctor_set(x_30, 5, x_29);
lean_ctor_set(x_30, 6, x_21);
lean_ctor_set(x_30, 7, x_22);
lean_ctor_set(x_30, 8, x_23);
lean_ctor_set(x_30, 9, x_24);
lean_ctor_set(x_30, 10, x_25);
lean_ctor_set(x_30, 11, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*12, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*12 + 1, x_28);
x_31 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_30, x_9, x_10);
lean_dec(x_30);
return x_31;
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__2;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg), 1, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_16);
lean_dec(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_20, x_3, x_16);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_22);
lean_dec(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_27, x_3, x_22);
lean_dec(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_34, x_3, x_31);
lean_dec(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_40, x_3, x_36);
lean_dec(x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_7, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 10);
lean_inc(x_19);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_20, 0, x_13);
lean_inc(x_17);
x_21 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_21, 0, x_17);
lean_inc(x_13);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_22, 0, x_13);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_13);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_23, 0, x_13);
lean_closure_set(x_23, 1, x_17);
lean_closure_set(x_23, 2, x_18);
lean_inc(x_13);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_24, 0, x_13);
lean_closure_set(x_24, 1, x_17);
lean_closure_set(x_24, 2, x_18);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_21);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
x_26 = lean_st_ref_get(x_8, x_12);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_environment_main_module(x_13);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_19);
lean_ctor_set(x_32, 3, x_14);
lean_ctor_set(x_32, 4, x_15);
lean_ctor_set(x_32, 5, x_16);
x_33 = lean_box(0);
lean_ctor_set(x_26, 1, x_33);
lean_ctor_set(x_26, 0, x_30);
x_34 = lean_apply_2(x_1, x_32, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_st_ref_take(x_8, x_29);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_39, 1);
lean_dec(x_42);
lean_ctor_set(x_39, 1, x_37);
x_43 = lean_st_ref_set(x_8, x_39, x_40);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = l_List_reverse___rarg(x_45);
x_47 = l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_7);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_35);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_35);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 2);
x_54 = lean_ctor_get(x_39, 3);
x_55 = lean_ctor_get(x_39, 4);
x_56 = lean_ctor_get(x_39, 5);
x_57 = lean_ctor_get(x_39, 6);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
x_58 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_37);
lean_ctor_set(x_58, 2, x_53);
lean_ctor_set(x_58, 3, x_54);
lean_ctor_set(x_58, 4, x_55);
lean_ctor_set(x_58, 5, x_56);
lean_ctor_set(x_58, 6, x_57);
x_59 = lean_st_ref_set(x_8, x_58, x_40);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_36, 1);
lean_inc(x_61);
lean_dec(x_36);
x_62 = l_List_reverse___rarg(x_61);
x_63 = l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_7);
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
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_35);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_34, 0);
lean_inc(x_67);
lean_dec(x_34);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_maxRecDepthErrorMessage;
x_71 = lean_string_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_69);
x_73 = l_Lean_MessageData_ofFormat(x_72);
x_74 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__5(x_68, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_68);
return x_74;
}
else
{
lean_object* x_75; 
lean_dec(x_69);
x_75 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7(x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_7);
return x_75;
}
}
else
{
lean_object* x_76; 
lean_dec(x_7);
x_76 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg(x_29);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_26, 0);
x_78 = lean_ctor_get(x_26, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_26);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_environment_main_module(x_13);
x_81 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_81, 0, x_25);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_19);
lean_ctor_set(x_81, 3, x_14);
lean_ctor_set(x_81, 4, x_15);
lean_ctor_set(x_81, 5, x_16);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_apply_2(x_1, x_81, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_st_ref_take(x_8, x_78);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_89, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_89, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_89, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 5);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 6);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 lean_ctor_release(x_89, 2);
 lean_ctor_release(x_89, 3);
 lean_ctor_release(x_89, 4);
 lean_ctor_release(x_89, 5);
 lean_ctor_release(x_89, 6);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(0, 7, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_91);
lean_ctor_set(x_98, 1, x_87);
lean_ctor_set(x_98, 2, x_92);
lean_ctor_set(x_98, 3, x_93);
lean_ctor_set(x_98, 4, x_94);
lean_ctor_set(x_98, 5, x_95);
lean_ctor_set(x_98, 6, x_96);
x_99 = lean_st_ref_set(x_8, x_98, x_90);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_86, 1);
lean_inc(x_101);
lean_dec(x_86);
x_102 = l_List_reverse___rarg(x_101);
x_103 = l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(x_102, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_100);
lean_dec(x_7);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_85);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_84, 0);
lean_inc(x_107);
lean_dec(x_84);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_maxRecDepthErrorMessage;
x_111 = lean_string_dec_eq(x_109, x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_109);
x_113 = l_Lean_MessageData_ofFormat(x_112);
x_114 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__5(x_108, x_113, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_108);
return x_114;
}
else
{
lean_object* x_115; 
lean_dec(x_109);
x_115 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_7);
return x_115;
}
}
else
{
lean_object* x_116; 
lean_dec(x_7);
x_116 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg(x_78);
return x_116;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 5);
x_11 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_5, x_6, x_7, x_8, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 5);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_ctor_set(x_8, 5, x_13);
x_14 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
x_23 = lean_ctor_get(x_8, 8);
x_24 = lean_ctor_get(x_8, 9);
x_25 = lean_ctor_get(x_8, 10);
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*12);
x_27 = lean_ctor_get(x_8, 11);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_29 = l_Lean_replaceRef(x_1, x_20);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_30, 0, x_15);
lean_ctor_set(x_30, 1, x_16);
lean_ctor_set(x_30, 2, x_17);
lean_ctor_set(x_30, 3, x_18);
lean_ctor_set(x_30, 4, x_19);
lean_ctor_set(x_30, 5, x_29);
lean_ctor_set(x_30, 6, x_21);
lean_ctor_set(x_30, 7, x_22);
lean_ctor_set(x_30, 8, x_23);
lean_ctor_set(x_30, 9, x_24);
lean_ctor_set(x_30, 10, x_25);
lean_ctor_set(x_30, 11, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*12, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*12 + 1, x_28);
x_31 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_30, x_9, x_10);
lean_dec(x_30);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no macro or `[quot_precheck]` instance for syntax kind '", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' found", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nThis means we cannot eagerly check your notation/quotation for unbound identifiers; you can use `set_option quotPrecheck false` to disable this check.", 151, 151);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_1);
x_11 = l_Lean_Syntax_getKind(x_1);
x_12 = l_Lean_MessageData_ofName(x_11);
x_13 = l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__2;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__4;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_1);
x_17 = l_Lean_MessageData_ofSyntax(x_1);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__6;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__9(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Macro_expandMacro_x3f), 3, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_8);
x_12 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Term_Quotation_precheck___lambda__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
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
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
lean_inc(x_1);
x_11 = l_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_Elab_Term_Quotation_precheck___lambda__2(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
lean_inc(x_1);
x_11 = l_Lean_Syntax_isAnyAntiquot(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Elab_Term_Quotation_precheck___lambda__3(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Quotation_precheckAttribute;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
x_14 = l_Lean_Syntax_getKind(x_1);
x_15 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_16 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_15, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Term_Quotation_precheck___lambda__4(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 6);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 7);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 8);
lean_inc(x_28);
x_29 = lean_ctor_get(x_7, 9);
lean_inc(x_29);
x_30 = lean_ctor_get(x_7, 10);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_7, sizeof(void*)*12);
x_32 = lean_ctor_get(x_7, 11);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
x_34 = l_Lean_replaceRef(x_1, x_25);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_35, 0, x_20);
lean_ctor_set(x_35, 1, x_21);
lean_ctor_set(x_35, 2, x_22);
lean_ctor_set(x_35, 3, x_23);
lean_ctor_set(x_35, 4, x_24);
lean_ctor_set(x_35, 5, x_34);
lean_ctor_set(x_35, 6, x_26);
lean_ctor_set(x_35, 7, x_27);
lean_ctor_set(x_35, 8, x_28);
lean_ctor_set(x_35, 9, x_29);
lean_ctor_set(x_35, 10, x_30);
lean_ctor_set(x_35, 11, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*12, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*12 + 1, x_33);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_36 = lean_apply_9(x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_35, x_8, x_12);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_36, 0, x_39);
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_36);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
x_46 = l_Lean_Exception_isInterrupt(x_44);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = l_Lean_Exception_isRuntime(x_44);
if (x_47 == 0)
{
if (lean_obj_tag(x_44) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__1;
x_50 = lean_nat_dec_eq(x_49, x_48);
lean_dec(x_48);
if (x_50 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_36);
lean_dec(x_44);
x_51 = lean_box(0);
x_52 = l_Lean_Elab_Term_Quotation_precheck___lambda__4(x_1, x_51, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
return x_52;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_36;
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
x_55 = l_Lean_Exception_isInterrupt(x_53);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Exception_isRuntime(x_53);
if (x_56 == 0)
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_57; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__1;
x_60 = lean_nat_dec_eq(x_59, x_58);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_54);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_53);
x_62 = lean_box(0);
x_63 = l_Lean_Elab_Term_Quotation_precheck___lambda__4(x_1, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_54);
return x_63;
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_54);
return x_64;
}
}
else
{
lean_object* x_65; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_54);
return x_65;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Quotation_precheck___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Quotation_precheck___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Quotation_precheck___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Quotation_precheck___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_runPrecheck___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Quotation_quotPrecheck;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_runPrecheck___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Quotation_hygiene;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = l_Lean_Elab_Term_Quotation_runPrecheck___closed__1;
x_11 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Elab_Term_Quotation_runPrecheck___closed__2;
x_15 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_9, x_14);
lean_dec(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_NameSet_empty;
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_1, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = lean_expr_eqv(x_1, x_5);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = l_Lean_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1(x_1, x_4);
if (x_8 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 6);
x_10 = l_Lean_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1(x_1, x_9);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg), 1, 0);
return x_8;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_23; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_15 = x_2;
} else {
 lean_dec_ref(x_2);
 x_15 = lean_box(0);
}
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_9, 2);
x_25 = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__1;
x_29 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_24, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_inc(x_1);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_1);
x_16 = x_30;
x_17 = x_27;
goto block_22;
}
else
{
uint8_t x_31; 
x_31 = lean_unbox(x_26);
lean_dec(x_26);
if (x_31 == 0)
{
lean_object* x_32; 
lean_inc(x_1);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_1);
x_16 = x_32;
x_17 = x_27;
goto block_22;
}
else
{
lean_object* x_33; 
x_33 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__4;
x_16 = x_33;
x_17 = x_27;
goto block_22;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_23);
lean_inc(x_1);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_1);
x_16 = x_34;
x_17 = x_11;
goto block_22;
}
block_22:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
if (lean_is_scalar(x_15)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_15;
 lean_ctor_set_tag(x_19, 0);
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_2 = x_14;
x_3 = x_20;
x_11 = x_17;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown identifier '", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' at quotation precheck; you can use `set_option quotPrecheck false` to disable this check.", 91, 91);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_MessageData_ofName(x_1);
x_12 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__4;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__10(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2___closed__1;
x_12 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2(x_11, x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_box(0);
x_17 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_Lean_Elab_Term_resolveName(x_2, x_1, x_12, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2(x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
x_21 = l_Lean_Exception_isInterrupt(x_19);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isRuntime(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
lean_free_object(x_14);
lean_dec(x_19);
x_23 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_23;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = l_Lean_Exception_isInterrupt(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
x_28 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_25);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_NameSet_contains(x_4, x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__3(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Lean_Elab_realizeGlobalNameWithInfos(x_1, x_2, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__4(x_2, x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = l_List_isEmpty___rarg(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__5(x_1, x_10, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_Quotation_precheckIdent(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckIdent", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckIdent___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("namedArgument", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ellipsis", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_3);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__3;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__5;
lean_inc(x_15);
x_19 = l_Lean_Syntax_isOfKind(x_15, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Elab_Term_Quotation_precheck(x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_box(0);
x_3 = x_23;
x_4 = x_24;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
lean_dec(x_15);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_box(0);
x_3 = x_31;
x_4 = x_32;
goto _start;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_unsigned_to_nat(3u);
x_35 = l_Lean_Syntax_getArg(x_15, x_34);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_36 = l_Lean_Elab_Term_Quotation_precheck(x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = 1;
x_39 = lean_usize_add(x_3, x_38);
x_40 = lean_box(0);
x_3 = x_39;
x_4 = x_40;
x_12 = x_37;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_precheckApp___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckApp___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_array_size(x_17);
x_21 = 0;
x_22 = lean_box(0);
x_23 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1(x_17, x_20, x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_17);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
return x_18;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_18, 0);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_18);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckApp", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckApp), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_precheckApp___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("typeAscription", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckTypeAscription(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
lean_inc(x_16);
x_17 = l_Lean_Syntax_matchesNull(x_16, x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_Syntax_matchesNull(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_16, x_22);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Elab_Term_Quotation_precheck(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckTypeAscription", 22, 22);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckTypeAscription), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("explicit", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckExplicit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckExplicit___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
lean_dec(x_1);
x_15 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckExplicit", 16, 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckExplicit), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_precheckExplicit___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_observing___at_Lean_Elab_Term_Quotation_precheckChoice___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = l_Lean_Exception_isInterrupt(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
return x_10;
}
}
else
{
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = l_Lean_Exception_isInterrupt(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Exception_isRuntime(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_4, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_4, x_3, x_16);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheck), 9, 1);
lean_closure_set(x_18, 0, x_15);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = lean_apply_9(x_1, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_17, x_3, x_20);
x_3 = x_23;
x_4 = x_24;
x_12 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2___at_Lean_Elab_Term_Quotation_precheckChoice___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_2, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheck), 9, 1);
lean_closure_set(x_17, 0, x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_observing___at_Lean_Elab_Term_Quotation_precheckChoice___spec__1(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_16, x_2, x_19);
x_2 = x_22;
x_3 = x_23;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Lean_MessageData_ofSyntax(x_11);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__1;
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_15);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Exception_toMessageData(x_13);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
x_21 = lean_array_push(x_4, x_20);
x_2 = x_8;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_ctor_get(x_9, 0);
lean_inc(x_24);
lean_dec(x_9);
x_25 = l_Lean_MessageData_ofSyntax(x_23);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__1;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__3;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Exception_toMessageData(x_24);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
x_33 = lean_array_push(x_4, x_32);
x_2 = x_8;
x_4 = x_33;
goto _start;
}
}
else
{
lean_dec(x_9);
lean_dec(x_6);
x_2 = x_8;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Term_Quotation_precheckChoice___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ambiguous notation with at least one interpretation that failed quotation precheck, possible interpretations ", 109, 109);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Quotation_precheckChoice___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Quotation_precheckChoice___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = l_Lean_Syntax_getArgs(x_1);
x_11 = lean_array_size(x_10);
x_12 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2___at_Lean_Elab_Term_Quotation_precheckChoice___spec__3(x_11, x_12, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Array_zip___rarg(x_15, x_10);
lean_dec(x_10);
lean_dec(x_15);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_filterMapM___at_Lean_Elab_Term_Quotation_precheckChoice___spec__4(x_17, x_19, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_21 = l_Array_isEmpty___rarg(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_13);
x_22 = lean_array_to_list(x_20);
x_23 = l_Lean_Elab_Term_Quotation_precheckChoice___closed__4;
x_24 = l_Lean_MessageData_joinSep(x_22, x_23);
x_25 = l_Lean_indentD(x_24);
x_26 = l_Lean_Elab_Term_Quotation_precheckChoice___closed__2;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__1;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__9(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(0);
lean_ctor_set(x_13, 0, x_31);
return x_13;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = l_Array_zip___rarg(x_32, x_10);
lean_dec(x_10);
lean_dec(x_32);
x_35 = lean_array_get_size(x_34);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Array_filterMapM___at_Lean_Elab_Term_Quotation_precheckChoice___spec__4(x_34, x_36, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_38 = l_Array_isEmpty___rarg(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_array_to_list(x_37);
x_40 = l_Lean_Elab_Term_Quotation_precheckChoice___closed__4;
x_41 = l_Lean_MessageData_joinSep(x_39, x_40);
x_42 = l_Lean_indentD(x_41);
x_43 = l_Lean_Elab_Term_Quotation_precheckChoice___closed__2;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__1;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__9(x_1, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_37);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_33);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
return x_13;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2___at_Lean_Elab_Term_Quotation_precheckChoice___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_Quotation_precheckChoice___spec__2___at_Lean_Elab_Term_Quotation_precheckChoice___spec__3(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_Term_Quotation_precheckChoice___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_Lean_Elab_Term_Quotation_precheckChoice___spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckChoice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_Quotation_precheckChoice(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("choice", 6, 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckChoice", 14, 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckChoice___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
lean_inc(x_11);
x_12 = l_Lean_Syntax_getQuotContent(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_Quotation_runPrecheck(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lambda__1___boxed), 9, 1);
lean_closure_set(x_15, 0, x_11);
x_16 = l_Lean_Elab_Term_adaptExpander(x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckedQuot", 14, 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elabPrecheckedQuot", 18, 18);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_termElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__5;
x_3 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__6;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(139u);
x_2 = lean_unsigned_to_nat(36u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(142u);
x_2 = lean_unsigned_to_nat(60u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__1;
x_2 = lean_unsigned_to_nat(36u);
x_3 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__2;
x_4 = lean_unsigned_to_nat(60u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(139u);
x_2 = lean_unsigned_to_nat(40u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(139u);
x_2 = lean_unsigned_to_nat(58u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__4;
x_2 = lean_unsigned_to_nat(40u);
x_3 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__5;
x_4 = lean_unsigned_to_nat(58u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__4;
x_3 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binrel", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckBinrel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckBinrel___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Elab_Term_Quotation_precheck(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_Quotation_precheck(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckBinrel", 14, 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinrel), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_precheckBinrel___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binrel_no_prop", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Elab_Term_Quotation_precheck(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_Quotation_precheck(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckBinrelNoProp", 20, 20);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckBinop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binop", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckBinop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_precheckBinop___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckBinop___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Elab_Term_Quotation_precheck(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_Quotation_precheck(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckBinop", 13, 13);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinop), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_precheckBinop___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binop_lazy", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckBinopLazy(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Elab_Term_Quotation_precheck(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_Quotation_precheck(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckBinopLazy", 17, 17);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckBinopLazy), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leftact", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckLeftact___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckLeftact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckLeftact___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Elab_Term_Quotation_precheck(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_Quotation_precheck(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckLeftact", 15, 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckLeftact), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_precheckLeftact___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckRightact___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rightact", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckRightact___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_precheckRightact___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckRightact(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckRightact___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_Elab_Term_Quotation_precheck(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Term_Quotation_precheck(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckRightact", 16, 16);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckRightact), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_precheckRightact___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckUnop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unop", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckUnop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_precheckUnop___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckUnop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckUnop___closed__2;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Term_Quotation_precheck(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precheckUnop", 12, 12);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8;
x_4 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckUnop), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheck___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_precheckUnop___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Quotation_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Quotation_Precheck(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_KeyedDeclsAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__1 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__1);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__2 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__2);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__3);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__4 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__4);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__5 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__5);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__6);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__7);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__8);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__9);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__10 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91____closed__10);
if (builtin) {res = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_91_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_quotPrecheck = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck);
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__1 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__1);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__2 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__2);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__3 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__3);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__4 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__4);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__5 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126____closed__5);
if (builtin) {res = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_126_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars);
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__2 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__2);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__3 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__3);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__4 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__4);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__5 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__5);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__6 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__6);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__7 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__7);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__8 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__8);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__9 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__9);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__11 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__11);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__12 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__12);
if (builtin) {res = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_precheckAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute);
lean_dec_ref(res);
}l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2___closed__1 = _init_l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_Quotation_precheck___spec__2___closed__1);
l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1();
l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2 = _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Elab_Term_Quotation_precheck___spec__7___closed__2);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__8___rarg___closed__2);
l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__1);
l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__2);
l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__3 = _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__3);
l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__4 = _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__4);
l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__5 = _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__5);
l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__6 = _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__6);
l_Lean_Elab_Term_Quotation_precheck___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheck___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheck___closed__1);
l_Lean_Elab_Term_Quotation_runPrecheck___closed__1 = _init_l_Lean_Elab_Term_Quotation_runPrecheck___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_runPrecheck___closed__1);
l_Lean_Elab_Term_Quotation_runPrecheck___closed__2 = _init_l_Lean_Elab_Term_Quotation_runPrecheck___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_runPrecheck___closed__2);
l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__1);
l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__2);
l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__3 = _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__3);
l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__4 = _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__4();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___closed__4);
l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__1);
l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__2);
l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__3 = _init_l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__3);
l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__4 = _init_l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__4);
l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__4);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__5);
l_Lean_Elab_Term_Quotation_precheckApp___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckApp___closed__1);
l_Lean_Elab_Term_Quotation_precheckApp___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckApp___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1);
l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1);
l_Lean_Elab_Term_Quotation_precheckExplicit___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckExplicit___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckChoice___spec__5___closed__3);
l_Lean_Elab_Term_Quotation_precheckChoice___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckChoice___closed__1);
l_Lean_Elab_Term_Quotation_precheckChoice___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckChoice___closed__2);
l_Lean_Elab_Term_Quotation_precheckChoice___closed__3 = _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckChoice___closed__3);
l_Lean_Elab_Term_Quotation_precheckChoice___closed__4 = _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckChoice___closed__4);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__4);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__5);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__4);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__5);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__6);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__3);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__4);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__5);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__6);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1___closed__7);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1);
l_Lean_Elab_Term_Quotation_precheckBinrel___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckBinrel___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1);
l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_precheckBinop___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckBinop___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1);
l_Lean_Elab_Term_Quotation_precheckBinop___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckBinop___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckBinop___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1);
l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1);
l_Lean_Elab_Term_Quotation_precheckLeftact___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckLeftact___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_precheckRightact___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckRightact___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1);
l_Lean_Elab_Term_Quotation_precheckRightact___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckRightact___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckRightact___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Elab_Term_Quotation_precheckUnop___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckUnop___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1);
l_Lean_Elab_Term_Quotation_precheckUnop___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckUnop___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckUnop___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__3);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
