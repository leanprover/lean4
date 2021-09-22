// Lean compiler output
// Module: Lean.Elab.Quotation.Precheck
// Imports: Init Lean.KeyedDeclsAttribute Lean.Parser.Command Lean.Elab.Term Lean.Elab.Quotation.Util
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
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__9;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__6;
static lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__2;
uint8_t l_Lean_Syntax_isAnyAntiquot(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__1;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___boxed(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__17;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__3;
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__8;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckParen___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckParen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__6;
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__15;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp(lean_object*);
lean_object* l_Lean_addTrace_addTraceOptions(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__5;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__4;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__5___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__14;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__6;
LEAN_EXPORT uint8_t l_Std_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute(lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckParen___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4___boxed(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__4;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__9;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_SepArray_getElems___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__3;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__7;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__5(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckParen___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__14;
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__5;
static lean_object* l_Lean_Elab_Term_Quotation_precheckParen___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__11;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__15;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__13;
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__5;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__2;
static uint32_t l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__3;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_withNewLocals___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_Lean_ppExpr___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckParen___closed__4;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___spec__1(lean_object*, size_t, size_t);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__3;
static lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__16;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__4;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_quotPrecheck___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_precheckParen___closed__5;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Macro_expandMacro_x3f(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNodeOf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__8(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10;
static lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__2;
lean_object* l_Lean_Syntax_getQuotContent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__13;
lean_object* lean_environment_main_module(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_Quotation_precheck___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckParen___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg___closed__1;
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__6;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__12;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__2;
static lean_object* l_Lean_Elab_Term_Quotation_precheckParen___closed__6;
static lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7___boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__3;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__16;
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__3;
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_Quotation_precheck___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__4;
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__11;
static lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocals___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckApp___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__4;
uint32_t lean_uint32_of_nat(lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
extern lean_object* l_Lean_Elab_Term_Quotation_hygiene;
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_withNewLocals___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___closed__7;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__1;
static lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__2;
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_withNewLocal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_3, x_1, x_11);
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
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_box(0);
x_8 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_6, x_7);
x_9 = 1;
x_10 = x_2 + x_9;
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
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("quotPrecheck");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Enable eager name analysis on notations in order to find unbound identifiers early.\nNote that type-sensitive syntax (\"elaborators\") needs special support for this kind of check, so it might need to be turned off when using such syntax.");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__3;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__2;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__5;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_quotPrecheck___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("allowSectionVars");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__2;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Allow occurrences of section variables in checked quotations, it is useful when declaring local notation.");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__3;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__2;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Attribute_Builtin_getId(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinQuotPrecheck");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Elab");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__4;
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Term");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__6;
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Quotation");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__8;
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Precheck");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10;
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a double backtick syntax quotation pre-check.\n\n[quotPrecheck k] registers a declaration of type `Lean.Elab.Term.Quotation.Precheck` for the `SyntaxNodeKind` `k`.\nIt should implement eager name analysis on the passed syntax by throwing an exception on unbound identifiers,\nand calling `precheck` recursively on nested terms, potentially with an extended local context (`withNewLocal`).\nMacros without registered precheck hook are unfolded, and identifier-less syntax is ultimately assumed to be well-formed.");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__2;
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__2;
x_3 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__13;
x_4 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__12;
x_5 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__14;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("precheckAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10;
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__16;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__15;
x_3 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__17;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__2;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static uint32_t _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__1() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__2() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__1;
x_3 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__3;
x_4 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint32(x_4, sizeof(void*)*2, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__2;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__2;
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__3;
x_3 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__1;
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
lean_ctor_set(x_4, 4, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__3___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__5___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__3;
x_3 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__4;
x_4 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__5;
x_5 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__6;
x_6 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__7;
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
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__6___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__8___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__10;
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__11;
x_4 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__6;
x_5 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__12;
x_6 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__13;
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
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__8;
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__14;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__2;
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Term_Quotation_precheckAttribute___closed__15;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__6(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__8(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 == x_3;
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = x_2 + x_7;
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
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = 0;
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___spec__1(x_4, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
}
else
{
uint8_t x_14; 
lean_dec(x_1);
x_14 = 0;
return x_14;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_Quotation_precheck___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = l_Lean_checkTraceOption(x_10, x_1);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_traceMsg");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("[");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("] ");
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_8, 3);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_addTrace_addTraceOptions(x_13);
x_16 = lean_st_ref_take(x_9, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 3);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
x_25 = l_Lean_Name_append(x_1, x_24);
x_26 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_26, 0, x_1);
x_27 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__4;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__6;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_15);
x_32 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__7;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_11);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Std_PersistentArray_push___rarg(x_23, x_35);
lean_ctor_set(x_18, 0, x_36);
x_37 = lean_st_ref_set(x_9, x_17, x_19);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_44 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_45 = lean_ctor_get(x_18, 0);
lean_inc(x_45);
lean_dec(x_18);
x_46 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
x_47 = l_Lean_Name_append(x_1, x_46);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__4;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__6;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_15);
x_54 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__7;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
lean_inc(x_11);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_11);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Std_PersistentArray_push___rarg(x_45, x_57);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_44);
lean_ctor_set(x_17, 3, x_59);
x_60 = lean_st_ref_set(x_9, x_17, x_19);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
x_67 = lean_ctor_get(x_17, 2);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
x_68 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
x_69 = lean_ctor_get(x_18, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_70 = x_18;
} else {
 lean_dec_ref(x_18);
 x_70 = lean_box(0);
}
x_71 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2;
x_72 = l_Lean_Name_append(x_1, x_71);
x_73 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_73, 0, x_1);
x_74 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__4;
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__6;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_15);
x_79 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__7;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_81, 0, x_72);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_11);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_11);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Std_PersistentArray_push___rarg(x_69, x_82);
if (lean_is_scalar(x_70)) {
 x_84 = lean_alloc_ctor(0, 1, 1);
} else {
 x_84 = x_70;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_68);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_65);
lean_ctor_set(x_85, 1, x_66);
lean_ctor_set(x_85, 2, x_67);
lean_ctor_set(x_85, 3, x_84);
x_86 = lean_st_ref_set(x_9, x_85, x_19);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_box(0);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
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
x_16 = lean_st_ref_get(x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 3);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_14);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_1 = x_13;
x_9 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
lean_inc(x_14);
x_23 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_Quotation_precheck___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_14);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_1 = x_13;
x_9 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_15);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3(x_14, x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_1 = x_13;
x_9 = x_32;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
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
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_8, 3, x_13);
x_14 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_23 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_19);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_22);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__6(x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10);
lean_dec(x_9);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg), 1, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
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
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_17);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_6, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_24 = x_5;
} else {
 lean_dec_ref(x_5);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
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
x_7 = l_Lean_ResolveName_resolveNamespace_x3f(x_1, x_2, x_3, x_4);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_7, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
lean_inc(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__1), 4, 1);
lean_closure_set(x_16, 0, x_13);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__1___rarg___boxed), 3, 1);
lean_closure_set(x_17, 0, x_14);
lean_inc(x_13);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_18, 0, x_13);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_15);
lean_inc(x_13);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_20, 0, x_13);
lean_closure_set(x_20, 1, x_14);
lean_closure_set(x_20, 2, x_15);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
x_22 = x_21;
x_23 = lean_ctor_get(x_7, 3);
lean_inc(x_23);
x_24 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 2);
lean_inc(x_28);
x_29 = lean_st_ref_get(x_8, x_26);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_environment_main_module(x_13);
x_34 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_25);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set(x_34, 4, x_28);
lean_ctor_set(x_34, 5, x_23);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_apply_2(x_1, x_34, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_st_ref_take(x_8, x_31);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_42, 1);
lean_dec(x_45);
lean_ctor_set(x_42, 1, x_40);
x_46 = lean_st_ref_set(x_8, x_42, x_43);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = l_List_reverse___rarg(x_48);
x_50 = l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_38);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_38);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = lean_ctor_get(x_42, 0);
x_56 = lean_ctor_get(x_42, 2);
x_57 = lean_ctor_get(x_42, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_42);
x_58 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_40);
lean_ctor_set(x_58, 2, x_56);
lean_ctor_set(x_58, 3, x_57);
x_59 = lean_st_ref_set(x_8, x_58, x_43);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_39, 1);
lean_inc(x_61);
lean_dec(x_39);
x_62 = l_List_reverse___rarg(x_61);
x_63 = l_List_forM___at_Lean_Elab_Term_Quotation_precheck___spec__4(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_ctor_set(x_66, 0, x_38);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_37, 0);
lean_inc(x_67);
lean_dec(x_37);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__5(x_68, x_71, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
return x_72;
}
else
{
lean_object* x_73; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg(x_31);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 3);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set(x_8, 3, x_13);
x_14 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_23 = l_Lean_replaceRef(x_1, x_18);
lean_dec(x_18);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_17);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_19);
lean_ctor_set(x_24, 5, x_20);
lean_ctor_set(x_24, 6, x_21);
lean_ctor_set(x_24, 7, x_22);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__9(x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_9, x_10);
lean_dec(x_9);
lean_dec(x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("no macro or `[quotPrecheck]` instance for syntax kind '");
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
x_1 = lean_mk_string("' found");
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
x_1 = lean_mk_string("\nThis means we cannot eagerly check your notation/quotation for unbound identifiers; you can use `set_option quotPrecheck false` to disable this check.");
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
lean_dec(x_2);
lean_inc(x_1);
x_11 = l_Lean_Syntax_getKind(x_1);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__2;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__4;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Term_Quotation_precheck___lambda__1___closed__6;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_precheck___spec__8(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheck___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Macro_expandMacro_x3f), 3, 1);
lean_closure_set(x_11, 0, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
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
lean_dec(x_2);
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
lean_dec(x_2);
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
x_15 = l_Lean_Elab_Term_Quotation_precheckAttribute;
x_16 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_15, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Elab_Term_Quotation_precheck___lambda__4(x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
x_28 = l_Lean_replaceRef(x_1, x_23);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_25);
lean_ctor_set(x_29, 6, x_26);
lean_ctor_set(x_29, 7, x_27);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_30 = lean_apply_9(x_19, x_1, x_2, x_3, x_4, x_5, x_6, x_29, x_8, x_12);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_30, 1);
x_44 = lean_ctor_get(x_30, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
x_46 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_47 = lean_nat_dec_eq(x_46, x_45);
lean_dec(x_45);
if (x_47 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_free_object(x_30);
lean_dec(x_37);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_Term_Quotation_precheck___lambda__4(x_1, x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_dec(x_30);
x_51 = lean_ctor_get(x_37, 0);
lean_inc(x_51);
x_52 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_53 = lean_nat_dec_eq(x_52, x_51);
lean_dec(x_51);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_37);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_37);
x_55 = lean_box(0);
x_56 = l_Lean_Elab_Term_Quotation_precheck___lambda__4(x_1, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_50);
return x_56;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_Quotation_precheck___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_Quotation_precheck___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at_Lean_Elab_Term_Quotation_precheck___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_runPrecheck(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = l_Lean_Elab_Term_Quotation_quotPrecheck;
x_11 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_9, x_10);
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
x_14 = l_Lean_Elab_Term_Quotation_hygiene;
x_15 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_9, x_14);
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
LEAN_EXPORT uint8_t l_Std_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Std_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1(x_1, x_4);
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
x_9 = lean_ctor_get(x_2, 7);
x_10 = l_Std_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1(x_1, x_9);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_RBNode_any___at___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___spec__1(x_1, x_2);
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
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_7, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 5);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_Lean_ResolveName_resolveGlobalName(x_13, x_14, x_15, x_1);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_7, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 5);
lean_inc(x_21);
lean_dec(x_7);
x_22 = l_Lean_ResolveName_resolveGlobalName(x_19, x_20, x_21, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; 
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
x_28 = l_Lean_Option_get___at_Lean_ppExpr___spec__1(x_23, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_25);
lean_inc(x_1);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_1);
x_15 = x_29;
x_16 = x_26;
goto block_21;
}
else
{
uint8_t x_30; 
x_30 = lean_unbox(x_25);
lean_dec(x_25);
if (x_30 == 0)
{
lean_object* x_31; 
lean_inc(x_1);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_15 = x_31;
x_16 = x_26;
goto block_21;
}
else
{
lean_object* x_32; 
x_32 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__3;
x_15 = x_32;
x_16 = x_26;
goto block_21;
}
}
}
else
{
lean_object* x_33; 
lean_inc(x_1);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_15 = x_33;
x_16 = x_11;
goto block_21;
}
block_21:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_2 = x_14;
x_3 = x_19;
x_11 = x_16;
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
x_1 = lean_mk_string("unknown identifier '");
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
x_1 = lean_mk_string("' at quotation precheck; you can use `set_option quotPrecheck false` to disable this check.");
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
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__1___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Elab_Term_Quotation_precheck___spec__9(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_12 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3(x_11, x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
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
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__2(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckIdent___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
lean_dec(x_3);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_inc(x_9);
lean_inc(x_1);
x_12 = l_Lean_resolveGlobalName___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__4(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_16 = l_Lean_Elab_Term_Quotation_precheckIdent___lambda__5(x_10, x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_resolveGlobalName___at_Lean_Elab_Term_Quotation_precheckIdent___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ident");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("precheckIdent");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10;
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckIdent), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("namedArgument");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_4 < x_3;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_5);
x_16 = lean_array_uget(x_2, x_4);
x_17 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1;
lean_inc(x_1);
x_18 = lean_name_mk_string(x_1, x_17);
lean_inc(x_16);
x_19 = l_Lean_Syntax_isOfKind(x_16, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Elab_Term_Quotation_precheck(x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = x_4 + x_22;
x_24 = lean_box(0);
x_4 = x_23;
x_5 = x_24;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_unsigned_to_nat(3u);
x_31 = l_Lean_Syntax_getArg(x_16, x_30);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_32 = l_Lean_Elab_Term_Quotation_precheck(x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; size_t x_34; size_t x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = 1;
x_35 = x_4 + x_34;
x_36 = lean_box(0);
x_4 = x_35;
x_5 = x_36;
x_13 = x_33;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_32);
if (x_38 == 0)
{
return x_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
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
x_1 = lean_mk_string("Parser");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__4;
x_2 = l_Lean_Elab_Term_Quotation_precheckApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_precheckApp___closed__2;
x_2 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("app");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_precheckApp___closed__3;
x_2 = l_Lean_Elab_Term_Quotation_precheckApp___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckApp___closed__5;
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
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_array_get_size(x_17);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = 0;
x_23 = l_Lean_Elab_Term_Quotation_precheckApp___closed__3;
x_24 = lean_box(0);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1(x_23, x_17, x_21, x_22, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_17);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_16;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("precheckApp");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10;
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckApp), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute;
x_3 = l_Lean_Elab_Term_Quotation_precheckApp___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckParen___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_2 == x_3;
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_Quotation_precheck(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = x_2 + x_18;
x_2 = x_19;
x_4 = x_16;
x_12 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("paren");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_precheckApp___closed__3;
x_2 = l_Lean_Elab_Term_Quotation_precheckParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("typeAscription");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_precheckApp___closed__3;
x_2 = l_Lean_Elab_Term_Quotation_precheckParen___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("tupleTail");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_precheckApp___closed__3;
x_2 = l_Lean_Elab_Term_Quotation_precheckParen___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Quotation_precheckParen(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_Quotation_precheckParen___closed__2;
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
lean_dec(x_1);
x_15 = l_Lean_nullKind;
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_14);
x_17 = l_Lean_Syntax_isNodeOf(x_14, x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(2u);
lean_inc(x_14);
x_19 = l_Lean_Syntax_isNodeOf(x_14, x_15, x_18);
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
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_Syntax_getArg(x_14, x_16);
x_22 = l_Lean_Syntax_getArg(x_14, x_13);
lean_dec(x_14);
lean_inc(x_22);
x_23 = l_Lean_Syntax_isNodeOf(x_22, x_15, x_13);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Syntax_isNodeOf(x_22, x_15, x_16);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_Elab_Term_Quotation_precheck(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Syntax_getArg(x_22, x_16);
lean_dec(x_22);
x_28 = l_Lean_Elab_Term_Quotation_precheckParen___closed__4;
lean_inc(x_27);
x_29 = l_Lean_Syntax_isOfKind(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Elab_Term_Quotation_precheckParen___closed__6;
lean_inc(x_27);
x_31 = l_Lean_Syntax_isOfKind(x_27, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheckIdent___spec__1___rarg(x_9);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_Syntax_getArg(x_27, x_13);
lean_dec(x_27);
x_34 = l_Lean_Syntax_getArgs(x_33);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_35 = l_Lean_Elab_Term_Quotation_precheck(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_35, 1);
x_38 = lean_ctor_get(x_35, 0);
lean_dec(x_38);
x_39 = l_Lean_Syntax_SepArray_getElems___rarg(x_34);
lean_dec(x_34);
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_lt(x_16, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_box(0);
lean_ctor_set(x_35, 0, x_42);
return x_35;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_40, x_40);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_box(0);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_35);
x_45 = 0;
x_46 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_47 = lean_box(0);
x_48 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckParen___spec__1(x_39, x_45, x_46, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_39);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_dec(x_35);
x_50 = l_Lean_Syntax_SepArray_getElems___rarg(x_34);
lean_dec(x_34);
x_51 = lean_array_get_size(x_50);
x_52 = lean_nat_dec_lt(x_16, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_51, x_51);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
return x_57;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_60 = lean_box(0);
x_61 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckParen___spec__1(x_50, x_58, x_59, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
lean_dec(x_50);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_35);
if (x_62 == 0)
{
return x_35;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_35, 0);
x_64 = lean_ctor_get(x_35, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_35);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_Syntax_getArg(x_27, x_13);
lean_dec(x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_67 = l_Lean_Elab_Term_Quotation_precheck(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Elab_Term_Quotation_precheck(x_66, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_66);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_9);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckParen___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Term_Quotation_precheckParen___spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("precheckParen");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10;
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_precheckParen), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_Quotation_precheckAttribute;
x_3 = l_Lean_Elab_Term_Quotation_precheckParen___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__3;
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
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("precheckedQuot");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_precheckApp___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabPrecheckedQuot");
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__10;
x_2 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Quotation_elabPrecheckedQuot), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__4;
x_5 = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__5;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
lean_object* initialize_Lean_Parser_Command(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
lean_object* initialize_Lean_Elab_Quotation_Util(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Quotation_Precheck(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__1 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__1);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__2 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__2);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__3 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__3);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__4 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__4);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__5 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71____closed__5);
l_Lean_Elab_Term_Quotation_quotPrecheck___closed__1 = _init_l_Lean_Elab_Term_Quotation_quotPrecheck___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck___closed__1);
res = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_71_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_quotPrecheck = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck);
lean_dec_ref(res);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__1 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__1);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__2 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__2);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__3 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__3);
l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__4 = _init_l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90____closed__4);
res = l_Lean_Elab_Term_Quotation_initFn____x40_Lean_Elab_Quotation_Precheck___hyg_90_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars);
lean_dec_ref(res);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__1();
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
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__13 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__13);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__14 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__14);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__15 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__15);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__16 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__16);
l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__17 = _init_l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_mkPrecheckAttribute___closed__17);
l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__1);
l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__1___closed__2);
l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__1();
l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__2___closed__2);
l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__4___closed__1);
l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___lambda__7___closed__1);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__1);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__2);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__3 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__3);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__4 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__4);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__5 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__5);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__6 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__6);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__7 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__7);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__8 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__8);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__9 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__9);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__10 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__10);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__11 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__11);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__12 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__12);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__13 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__13);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__14 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__14);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__15 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__15);
l_Lean_Elab_Term_Quotation_precheckAttribute___closed__16 = _init_l_Lean_Elab_Term_Quotation_precheckAttribute___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute___closed__16);
res = l_Lean_Elab_Term_Quotation_mkPrecheckAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Term_Quotation_precheckAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute);
lean_dec_ref(res);
l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__1);
l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2 = _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__2);
l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__3 = _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__3);
l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__4 = _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__4);
l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__5 = _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__5);
l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__6 = _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__6);
l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__7 = _init_l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__7();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_Quotation_precheck___spec__3___closed__7);
l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at_Lean_Elab_Term_Quotation_precheck___spec__7___rarg___closed__1);
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
l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__1);
l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__2);
l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__3 = _init_l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_Quotation_precheckIdent___spec__3___closed__3);
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
l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__3);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__4);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent___closed__5);
res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_Term_Quotation_precheckApp___spec__1___closed__1);
l_Lean_Elab_Term_Quotation_precheckApp___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckApp___closed__1);
l_Lean_Elab_Term_Quotation_precheckApp___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckApp___closed__2);
l_Lean_Elab_Term_Quotation_precheckApp___closed__3 = _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckApp___closed__3);
l_Lean_Elab_Term_Quotation_precheckApp___closed__4 = _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckApp___closed__4);
l_Lean_Elab_Term_Quotation_precheckApp___closed__5 = _init_l_Lean_Elab_Term_Quotation_precheckApp___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckApp___closed__5);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp___closed__3);
res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_Quotation_precheckParen___closed__1 = _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckParen___closed__1);
l_Lean_Elab_Term_Quotation_precheckParen___closed__2 = _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckParen___closed__2);
l_Lean_Elab_Term_Quotation_precheckParen___closed__3 = _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckParen___closed__3);
l_Lean_Elab_Term_Quotation_precheckParen___closed__4 = _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckParen___closed__4);
l_Lean_Elab_Term_Quotation_precheckParen___closed__5 = _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckParen___closed__5);
l_Lean_Elab_Term_Quotation_precheckParen___closed__6 = _init_l_Lean_Elab_Term_Quotation_precheckParen___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckParen___closed__6);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen___closed__3);
res = l___regBuiltin_Lean_Elab_Term_Quotation_precheckParen(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__1);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__2);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__3);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__4);
l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot___closed__5);
res = l___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
