// Lean compiler output
// Module: Lean.PrettyPrinter
// Imports: Lean.PrettyPrinter.Delaborator Lean.PrettyPrinter.Parenthesizer Lean.PrettyPrinter.Formatter Lean.Parser.Module Lean.ParserCompiler Lean.Util.NumObjs Lean.Util.ShareCommon
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
static lean_object* l_Lean_MessageData_ofConst___closed__8;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM(lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_pp_exprSizes;
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__11;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParserCompiler_registerParserCompiler___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__5;
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_signature___closed__0;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_Lean_MessageData_ofConst___closed__6;
lean_object* lean_sharecommon_quick(lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__8;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__2;
lean_object* l_Lean_MessageData_toString(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppSignature___closed__1;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__12;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__24;
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__15;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__19;
static lean_object* l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_1164_;
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__5;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__1;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_214_;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__26;
lean_object* lean_io_get_num_heartbeats(lean_object*);
static lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3;
lean_object* l_panic___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1084_;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* lean_pp_expr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_signature___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_214_;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3;
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__7;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageData_signature(lean_object*);
lean_object* l_Lean_Expr_sizeWithoutSharing(lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__6;
static lean_object* l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_1164_;
static lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2;
static lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_MessageData_ofConst___closed__2;
static lean_object* l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_1164_;
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__9;
extern lean_object* l_Lean_ppFnsRef;
static lean_object* l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_1164_;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__1;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__17;
static lean_object* l_Lean_PrettyPrinter_initFn___lam__1___closed__0____x40_Lean_PrettyPrinter___hyg_1084_;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__5;
extern lean_object* l_Lean_pp_raw;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppTactic___closed__0;
static lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__0;
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_1164_;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__13;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__11;
static lean_object* l_Lean_PrettyPrinter_initFn___closed__10____x40_Lean_PrettyPrinter___hyg_1164_;
extern lean_object* l_Lean_PrettyPrinter_parenthesizerAttribute;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__10;
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__11;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__3;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__8;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_214_;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__14;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofConst___closed__0;
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__22;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__7;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConst(lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__4;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofConst___closed__7;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__6;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__27;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__21;
extern lean_object* l_Lean_diagnostics;
static uint64_t l_Lean_PPContext_runMetaM___redArg___closed__1;
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__0;
lean_object* lean_mk_syntax_ident(lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__20;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__9;
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__6;
static lean_object* l_Lean_PrettyPrinter_initFn___closed__9____x40_Lean_PrettyPrinter___hyg_1164_;
extern lean_object* l_Lean_inheritedTraceOptions;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__14;
static lean_object* l_Lean_PrettyPrinter_ppTerm___closed__1;
static lean_object* l_Lean_PrettyPrinter_initFn___closed__8____x40_Lean_PrettyPrinter___hyg_1164_;
static uint8_t l_Lean_PrettyPrinter_ppExprLegacy___closed__14;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_sanitizeSyntax(lean_object*, lean_object*);
static lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__7;
extern lean_object* l_Lean_PrettyPrinter_combinatorFormatterAttribute;
static lean_object* l_Lean_PrettyPrinter_ppTerm___closed__0;
static lean_object* l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_214_;
static lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1;
static lean_object* l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_214_;
static lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0;
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__4;
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__25;
extern lean_object* l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__4;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__15;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppTactic___closed__1;
static lean_object* l_Lean_MessageData_ofConst___closed__1;
static lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3;
static lean_object* l_Lean_MessageData_ofConst___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_getPPMVarsLevels(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_1164_;
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofLazyM___closed__0;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofLazyM___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_parenthesizeCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__13;
lean_object* l_Lean_Level_format(lean_object*, uint8_t);
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__8;
static lean_object* l_Lean_PrettyPrinter_ppSignature___closed__2;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__16;
static lean_object* l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_1164_;
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__12;
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__7;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runMetaM___redArg___closed__3;
static lean_object* l_Lean_MessageData_ofConst___closed__4;
static lean_object* l_Lean_MessageData_ofConst___closed__9;
static lean_object* l_Lean_PrettyPrinter_ppCommand___closed__0;
lean_object* l_Lean_PrettyPrinter_formatCategory(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__18;
lean_object* l_Lean_PrettyPrinter_parenthesize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__6;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Expr_numObjs(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__4;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_214_;
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_214_(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1164_(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_PrettyPrinter_formatterAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__10;
static lean_object* l_Lean_PrettyPrinter_registerParserCompilers___closed__0;
static lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0;
lean_object* l_Lean_PrettyPrinter_delabCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1164_;
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_214_;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4;
lean_object* l_Lean_LocalContext_sanitizeNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__11____x40_Lean_PrettyPrinter___hyg_1164_;
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers(lean_object*);
static lean_object* l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_214_;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__23;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084_(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Parser_Module_module_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__9;
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__9;
lean_object* l_Lean_Parser_Module_module_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofConst___closed__5;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__5;
lean_object* l_Lean_MessageData_lazy(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_ofFormatWithInfosM___lam__1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppExprLegacy___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0;
static lean_object* l_Lean_PPContext_runCoreM___redArg___closed__3;
static lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_ppCommand___closed__1;
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MessageData_signature___lam__0___closed__1;
static lean_object* l_Lean_PrettyPrinter_ppSignature___closed__0;
static lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1;
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_pp_uniq", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_PPContext_runCoreM___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_PPContext_runCoreM___redArg___closed__4;
x_4 = l_Lean_PPContext_runCoreM___redArg___closed__5;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__7() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__6;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__9;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__12() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_PPContext_runCoreM___redArg___closed__4;
x_4 = l_Lean_PPContext_runCoreM___redArg___closed__11;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PPContext_runCoreM___redArg___closed__12;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__17() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_PPContext_runCoreM___redArg___closed__4;
x_4 = l_Lean_PPContext_runCoreM___redArg___closed__16;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__17;
x_2 = l_Lean_PPContext_runCoreM___redArg___closed__15;
x_3 = l_Lean_PPContext_runCoreM___redArg___closed__14;
x_4 = lean_box(1);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_inheritedTraceOptions;
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<PrettyPrinter>", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__23;
x_2 = l_Lean_PPContext_runCoreM___redArg___closed__22;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runCoreM___redArg___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internal exception #", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_103; 
x_4 = lean_io_get_num_heartbeats(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 3);
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_ctor_get(x_1, 5);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_PPContext_runCoreM___redArg___closed__2;
x_15 = l_Lean_PPContext_runCoreM___redArg___closed__3;
x_16 = l_Lean_PPContext_runCoreM___redArg___closed__7;
x_17 = l_Lean_PPContext_runCoreM___redArg___closed__10;
x_18 = l_Lean_PPContext_runCoreM___redArg___closed__13;
x_19 = l_Lean_PPContext_runCoreM___redArg___closed__18;
x_20 = l_Lean_PPContext_runCoreM___redArg___closed__19;
lean_inc(x_7);
x_21 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_17);
lean_ctor_set(x_21, 6, x_18);
lean_ctor_set(x_21, 7, x_19);
lean_ctor_set(x_21, 8, x_20);
x_22 = lean_st_mk_ref(x_21, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_PPContext_runCoreM___redArg___closed__20;
x_26 = lean_st_ref_get(x_25, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_23, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_PPContext_runCoreM___redArg___closed__21;
x_34 = l_Lean_PPContext_runCoreM___redArg___closed__24;
x_35 = lean_box(0);
x_36 = l_Lean_Core_getMaxHeartbeats(x_8);
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = l_Lean_PPContext_runCoreM___redArg___closed__25;
x_40 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_8, x_39);
x_103 = l_Lean_Kernel_isDiagnosticsEnabled(x_32);
lean_dec(x_32);
if (x_103 == 0)
{
if (x_40 == 0)
{
lean_inc(x_23);
x_41 = x_23;
x_42 = x_31;
goto block_80;
}
else
{
goto block_102;
}
}
else
{
if (x_40 == 0)
{
goto block_102;
}
else
{
lean_inc(x_23);
x_41 = x_23;
x_42 = x_31;
goto block_80;
}
}
block_80:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_43 = l_Lean_PPContext_runCoreM___redArg___closed__26;
x_44 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_8, x_43);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_45 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_34);
lean_ctor_set(x_45, 2, x_8);
lean_ctor_set(x_45, 3, x_11);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 5, x_35);
lean_ctor_set(x_45, 6, x_9);
lean_ctor_set(x_45, 7, x_10);
lean_ctor_set(x_45, 8, x_5);
lean_ctor_set(x_45, 9, x_36);
lean_ctor_set(x_45, 10, x_12);
lean_ctor_set(x_45, 11, x_37);
lean_ctor_set(x_45, 12, x_27);
lean_ctor_set_uint8(x_45, sizeof(void*)*13, x_40);
x_46 = lean_unbox(x_38);
lean_ctor_set_uint8(x_45, sizeof(void*)*13 + 1, x_46);
x_47 = lean_apply_3(x_2, x_45, x_41, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_st_ref_get(x_23, x_49);
lean_dec(x_23);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_48);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_23);
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec(x_47);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_MessageData_toString(x_57, x_56);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set_tag(x_58, 1);
lean_ctor_set(x_58, 0, x_61);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_58, 0);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_58);
x_64 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_47);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_47, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
lean_dec(x_55);
x_69 = l_Lean_PPContext_runCoreM___redArg___closed__27;
x_70 = l_Nat_reprFast(x_68);
x_71 = lean_string_append(x_69, x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_47, 0, x_72);
return x_47;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_47, 1);
lean_inc(x_73);
lean_dec(x_47);
x_74 = lean_ctor_get(x_55, 0);
lean_inc(x_74);
lean_dec(x_55);
x_75 = l_Lean_PPContext_runCoreM___redArg___closed__27;
x_76 = l_Nat_reprFast(x_74);
x_77 = lean_string_append(x_75, x_76);
lean_dec(x_76);
x_78 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
}
}
}
block_102:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_81 = lean_st_ref_take(x_23, x_31);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 5);
lean_dec(x_86);
x_87 = l_Lean_Kernel_enableDiag(x_85, x_40);
lean_ctor_set(x_82, 5, x_17);
lean_ctor_set(x_82, 0, x_87);
x_88 = lean_st_ref_set(x_23, x_82, x_83);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
lean_inc(x_23);
x_41 = x_23;
x_42 = x_89;
goto block_80;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_90 = lean_ctor_get(x_82, 0);
x_91 = lean_ctor_get(x_82, 1);
x_92 = lean_ctor_get(x_82, 2);
x_93 = lean_ctor_get(x_82, 3);
x_94 = lean_ctor_get(x_82, 4);
x_95 = lean_ctor_get(x_82, 6);
x_96 = lean_ctor_get(x_82, 7);
x_97 = lean_ctor_get(x_82, 8);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_82);
x_98 = l_Lean_Kernel_enableDiag(x_90, x_40);
x_99 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_91);
lean_ctor_set(x_99, 2, x_92);
lean_ctor_set(x_99, 3, x_93);
lean_ctor_set(x_99, 4, x_94);
lean_ctor_set(x_99, 5, x_17);
lean_ctor_set(x_99, 6, x_95);
lean_ctor_set(x_99, 7, x_96);
lean_ctor_set(x_99, 8, x_97);
x_100 = lean_st_ref_set(x_23, x_99, x_83);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
lean_inc(x_23);
x_41 = x_23;
x_42 = x_101;
goto block_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PPContext_runCoreM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runCoreM___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runCoreM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PPContext_runCoreM(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_st_mk_ref(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = lean_apply_5(x_2, x_3, x_8, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_8, x_12);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_dec(x_8);
return x_10;
}
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_1 = lean_box(2);
x_2 = lean_box(0);
x_3 = lean_box(1);
x_4 = lean_box(1);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 0, 18);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 0, x_7);
x_8 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 1, x_8);
x_9 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 2, x_9);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 3, x_10);
x_11 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 4, x_11);
x_12 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 5, x_12);
x_13 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 6, x_13);
x_14 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 7, x_14);
x_15 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 8, x_15);
x_16 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, 9, x_16);
x_17 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 10, x_17);
x_18 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 11, x_18);
x_19 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 12, x_19);
x_20 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 13, x_20);
x_21 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 14, x_21);
x_22 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 15, x_22);
x_23 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 16, x_23);
x_24 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 17, x_24);
return x_6;
}
}
static uint64_t _init_l_Lean_PPContext_runMetaM___redArg___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_PPContext_runMetaM___redArg___closed__0;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runMetaM___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runMetaM___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runMetaM___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runMetaM___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PPContext_runMetaM___redArg___closed__7;
x_2 = l_Lean_PPContext_runMetaM___redArg___closed__6;
x_3 = l_Lean_PPContext_runMetaM___redArg___closed__5;
x_4 = l_Lean_PPContext_runMetaM___redArg___closed__4;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runMetaM___redArg___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__11() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_PPContext_runMetaM___redArg___closed__9;
x_4 = l_Lean_PPContext_runMetaM___redArg___closed__10;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runMetaM___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runMetaM___redArg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PPContext_runMetaM___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runMetaM___redArg___closed__13;
x_2 = l_Lean_PPContext_runMetaM___redArg___closed__12;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_box(0);
x_7 = l_Lean_PPContext_runMetaM___redArg___closed__0;
x_8 = l_Lean_PPContext_runMetaM___redArg___closed__1;
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_PPContext_runMetaM___redArg___closed__2;
x_12 = lean_box(0);
x_13 = lean_box(0);
lean_inc(x_5);
x_14 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_5);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_10);
lean_ctor_set(x_14, 6, x_13);
lean_ctor_set_uint64(x_14, sizeof(void*)*7, x_8);
x_15 = lean_unbox(x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*7 + 8, x_15);
x_16 = lean_unbox(x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*7 + 9, x_16);
x_17 = lean_unbox(x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*7 + 10, x_17);
x_18 = l_Lean_PPContext_runMetaM___redArg___closed__8;
x_19 = l_Lean_PPContext_runMetaM___redArg___closed__11;
x_20 = l_Lean_PPContext_runMetaM___redArg___closed__14;
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_9);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_PPContext_runMetaM___redArg___lam__0), 6, 3);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_14);
x_23 = l_Lean_PPContext_runCoreM___redArg(x_1, x_22, x_3);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PPContext_runMetaM___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runMetaM___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PPContext_runMetaM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PPContext_runMetaM(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
x_9 = l_Lean_sanitizeSyntax(x_2, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_PrettyPrinter_parenthesizeCategory(x_1, x_10, x_3, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_PrettyPrinter_formatCategory(x_1, x_12, x_3, x_4, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppTerm___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppTerm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_ppTerm___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_ppTerm___closed__1;
x_6 = l_Lean_PrettyPrinter_ppCategory(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 2);
lean_dec(x_9);
lean_ctor_set(x_3, 2, x_1);
x_10 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
else
{
lean_object* x_11; uint64_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_13 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_3, 3);
x_16 = lean_ctor_get(x_3, 4);
x_17 = lean_ctor_get(x_3, 5);
x_18 = lean_ctor_get(x_3, 6);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_11);
lean_dec(x_3);
x_21 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_1);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_17);
lean_ctor_set(x_21, 6, x_18);
lean_ctor_set_uint64(x_21, sizeof(void*)*7, x_12);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 8, x_13);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 9, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 10, x_20);
x_22 = lean_apply_5(x_2, x_21, x_4, x_5, x_6, x_7);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PrettyPrinter_ppTerm(x_9, x_5, x_6, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppUsing(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Lean_LocalContext_sanitizeNames(x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppUsing___lam__0), 7, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_1);
x_15 = l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(x_13, x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_214_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pp", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_214_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exprSizes", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_214_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_214_;
x_2 = l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_214_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_214_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(pretty printer) prefix each embedded expression with its sizes in the format (size disregarding sharing/size with sharing/size with max sharing)", 145, 145);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_214_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_214_;
x_2 = l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_214_;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_214_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_214_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PrettyPrinter", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_214_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_214_;
x_2 = l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_214_;
x_3 = l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_214_;
x_4 = l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_214_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_214_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_214_;
x_3 = l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_214_;
x_4 = l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_214_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_pp_exprSizes;
return x_1;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[size ", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("] ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__22;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0;
x_7 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_9 = l_Lean_Expr_numObjs(x_1, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_sharecommon_quick(x_1);
x_14 = l_Lean_Expr_numObjs(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2;
x_18 = l_Lean_Expr_sizeWithoutSharing(x_1);
lean_dec(x_1);
x_19 = l_Nat_reprFast(x_18);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_9, 5);
lean_ctor_set(x_9, 1, x_20);
lean_ctor_set(x_9, 0, x_17);
x_21 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4;
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Nat_reprFast(x_11);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_21);
x_27 = l_Nat_reprFast(x_16);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__6;
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
x_33 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__7;
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_14, 0, x_34);
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2;
x_38 = l_Lean_Expr_sizeWithoutSharing(x_1);
lean_dec(x_1);
x_39 = l_Nat_reprFast(x_38);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set_tag(x_9, 5);
lean_ctor_set(x_9, 1, x_40);
lean_ctor_set(x_9, 0, x_37);
x_41 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4;
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_9);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Nat_reprFast(x_11);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
x_47 = l_Nat_reprFast(x_35);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__6;
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_2);
x_53 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__7;
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_36);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_56 = lean_ctor_get(x_9, 0);
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_9);
x_58 = lean_sharecommon_quick(x_1);
x_59 = l_Lean_Expr_numObjs(x_58, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2;
x_64 = l_Lean_Expr_sizeWithoutSharing(x_1);
lean_dec(x_1);
x_65 = l_Nat_reprFast(x_64);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
x_68 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4;
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Nat_reprFast(x_56);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
x_74 = l_Nat_reprFast(x_60);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__6;
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_2);
x_80 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__7;
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
if (lean_is_scalar(x_62)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_62;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_61);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(x_1, x_2, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_PrettyPrinter_delab(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExpr___lam__0), 6, 0);
lean_inc(x_4);
lean_inc(x_1);
x_8 = l_Lean_PrettyPrinter_ppUsing(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(x_1, x_9, x_4, x_10);
lean_dec(x_4);
return x_11;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_9 = l_Lean_PrettyPrinter_delabCore___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_28; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_14 = x_10;
} else {
 lean_dec_ref(x_10);
 x_14 = lean_box(0);
}
lean_inc(x_6);
x_28 = l_Lean_PrettyPrinter_ppTerm(x_12, x_6, x_7, x_11);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg(x_1, x_29, x_6, x_30);
lean_dec(x_6);
x_15 = x_31;
goto block_27;
}
else
{
lean_dec(x_6);
lean_dec(x_1);
x_15 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_is_scalar(x_14)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_14;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
if (lean_is_scalar(x_14)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_14;
}
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_9);
if (x_32 == 0)
{
return x_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_9, 0);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_9);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppExprWithInfos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Lean_LocalContext_sanitizeNames(x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos___lam__0), 8, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
x_16 = l_Lean_Meta_withLCtx_x27___at___Lean_PrettyPrinter_ppUsing_spec__0___redArg(x_14, x_15, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tagAppFns", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0;
x_2 = l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_214_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(1, 0, 1);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConst), 7, 0);
x_2 = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2;
x_3 = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1;
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos), 11, 4);
lean_closure_set(x_4, 0, lean_box(0));
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_2);
lean_closure_set(x_4, 3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppConstNameWithInfos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
lean_inc(x_1);
x_13 = l_Lean_Environment_find_x3f(x_10, x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
x_15 = lean_mk_syntax_ident(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_Lean_sanitizeSyntax(x_15, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_dec(x_21);
x_22 = l_Lean_PrettyPrinter_ppTerm___closed__1;
x_23 = l_Lean_PrettyPrinter_formatCategory(x_22, x_20, x_4, x_5, x_9);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_box(0);
lean_ctor_set(x_18, 1, x_26);
lean_ctor_set(x_18, 0, x_25);
lean_ctor_set(x_23, 0, x_18);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_box(0);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_18);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
return x_23;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_23);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
lean_dec(x_18);
x_36 = l_Lean_PrettyPrinter_ppTerm___closed__1;
x_37 = l_Lean_PrettyPrinter_formatCategory(x_36, x_35, x_4, x_5, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_46 = x_37;
} else {
 lean_dec_ref(x_37);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_13, 0);
lean_inc(x_48);
lean_dec(x_13);
x_49 = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3;
x_50 = l_Lean_ConstantInfo_levelParams(x_48);
lean_dec(x_48);
x_51 = lean_box(0);
x_52 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_50, x_51);
x_53 = l_Lean_Expr_const___override(x_1, x_52);
x_54 = lean_box(0);
x_55 = l_Lean_PrettyPrinter_ppExprWithInfos(x_53, x_54, x_49, x_2, x_3, x_4, x_5, x_9);
return x_55;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_uniq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_ppExprLegacy___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_PrettyPrinter_ppExprLegacy___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_ppExprLegacy___closed__6;
x_2 = l_Lean_PrettyPrinter_ppExprLegacy___closed__5;
x_3 = l_Lean_PrettyPrinter_ppExprLegacy___closed__4;
x_4 = l_Lean_PrettyPrinter_ppExprLegacy___closed__3;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_PPContext_runCoreM___redArg___closed__4;
x_4 = l_Lean_PrettyPrinter_ppExprLegacy___closed__8;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_ppExprLegacy___closed__11;
x_2 = l_Lean_PrettyPrinter_ppExprLegacy___closed__10;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Core_getMaxHeartbeats(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__25;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__26;
x_2 = lean_box(0);
x_3 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lean_pp_expr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_203; 
x_7 = lean_io_get_num_heartbeats(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_box(0);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_PrettyPrinter_ppExprLegacy___closed__2;
x_15 = l_Lean_PPContext_runCoreM___redArg___closed__3;
x_16 = l_Lean_PPContext_runCoreM___redArg___closed__7;
x_17 = l_Lean_PPContext_runCoreM___redArg___closed__10;
x_18 = lean_box(0);
x_19 = l_Lean_PPContext_runCoreM___redArg___closed__13;
x_20 = l_Lean_PPContext_runCoreM___redArg___closed__18;
x_21 = l_Lean_PPContext_runCoreM___redArg___closed__19;
x_22 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_13);
lean_ctor_set(x_22, 2, x_14);
lean_ctor_set(x_22, 3, x_15);
lean_ctor_set(x_22, 4, x_16);
lean_ctor_set(x_22, 5, x_17);
lean_ctor_set(x_22, 6, x_19);
lean_ctor_set(x_22, 7, x_20);
lean_ctor_set(x_22, 8, x_21);
x_23 = lean_st_mk_ref(x_22, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PPContext_runCoreM___redArg___closed__20;
x_27 = lean_st_ref_get(x_26, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_24, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_box(0);
x_35 = l_Lean_PPContext_runMetaM___redArg___closed__0;
x_36 = l_Lean_PPContext_runMetaM___redArg___closed__1;
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_18);
lean_ctor_set(x_39, 2, x_3);
lean_ctor_set(x_39, 3, x_21);
lean_ctor_set(x_39, 4, x_37);
lean_ctor_set(x_39, 5, x_10);
lean_ctor_set(x_39, 6, x_38);
lean_ctor_set_uint64(x_39, sizeof(void*)*7, x_36);
x_40 = lean_unbox(x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 8, x_40);
x_41 = lean_unbox(x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 9, x_41);
x_42 = lean_unbox(x_34);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 10, x_42);
x_150 = l_Lean_PrettyPrinter_ppExprLegacy___closed__7;
x_151 = l_Lean_PrettyPrinter_ppExprLegacy___closed__9;
x_152 = l_Lean_PrettyPrinter_ppExprLegacy___closed__12;
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_2);
lean_ctor_set(x_153, 1, x_150);
lean_ctor_set(x_153, 2, x_18);
lean_ctor_set(x_153, 3, x_151);
lean_ctor_set(x_153, 4, x_152);
x_154 = l_Lean_PPContext_runCoreM___redArg___closed__21;
x_155 = l_Lean_PPContext_runCoreM___redArg___closed__24;
x_156 = lean_box(0);
x_157 = lean_box(0);
x_158 = lean_box(0);
x_159 = l_Lean_PrettyPrinter_ppExprLegacy___closed__13;
x_160 = lean_box(0);
x_161 = l_Lean_PPContext_runCoreM___redArg___closed__25;
x_162 = l_Lean_PrettyPrinter_ppExprLegacy___closed__14;
x_203 = l_Lean_Kernel_isDiagnosticsEnabled(x_33);
lean_dec(x_33);
if (x_203 == 0)
{
if (x_162 == 0)
{
lean_inc(x_24);
x_163 = x_24;
x_164 = x_32;
goto block_180;
}
else
{
goto block_202;
}
}
else
{
if (x_162 == 0)
{
goto block_202;
}
else
{
lean_inc(x_24);
x_163 = x_24;
x_164 = x_32;
goto block_180;
}
}
block_97:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_4, x_44);
lean_dec(x_44);
x_61 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_47);
lean_ctor_set(x_61, 2, x_4);
lean_ctor_set(x_61, 3, x_48);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_49);
lean_ctor_set(x_61, 6, x_50);
lean_ctor_set(x_61, 7, x_51);
lean_ctor_set(x_61, 8, x_52);
lean_ctor_set(x_61, 9, x_53);
lean_ctor_set(x_61, 10, x_54);
lean_ctor_set(x_61, 11, x_55);
lean_ctor_set(x_61, 12, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*13, x_45);
lean_ctor_set_uint8(x_61, sizeof(void*)*13 + 1, x_56);
lean_inc(x_43);
x_62 = l_Lean_PrettyPrinter_ppExpr(x_5, x_39, x_43, x_61, x_58, x_59);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_st_ref_get(x_43, x_64);
lean_dec(x_43);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_get(x_24, x_66);
lean_dec(x_24);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_63);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
lean_object* x_72; 
lean_dec(x_43);
lean_dec(x_24);
x_72 = lean_ctor_get(x_62, 0);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
lean_dec(x_62);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_MessageData_toString(x_74, x_73);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set_tag(x_75, 1);
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
x_81 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_81, 0, x_79);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_62);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_62, 0);
lean_dec(x_84);
x_85 = lean_ctor_get(x_72, 0);
lean_inc(x_85);
lean_dec(x_72);
x_86 = l_Lean_PPContext_runCoreM___redArg___closed__27;
x_87 = l_Nat_reprFast(x_85);
x_88 = lean_string_append(x_86, x_87);
lean_dec(x_87);
x_89 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_62, 0, x_89);
return x_62;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_62, 1);
lean_inc(x_90);
lean_dec(x_62);
x_91 = lean_ctor_get(x_72, 0);
lean_inc(x_91);
lean_dec(x_72);
x_92 = l_Lean_PPContext_runCoreM___redArg___closed__27;
x_93 = l_Nat_reprFast(x_91);
x_94 = lean_string_append(x_92, x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
return x_96;
}
}
}
}
block_149:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_st_ref_take(x_101, x_102);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_108 = lean_ctor_get(x_105, 0);
x_109 = lean_ctor_get(x_105, 5);
lean_dec(x_109);
x_110 = l_Lean_Kernel_enableDiag(x_108, x_100);
lean_ctor_set(x_105, 5, x_17);
lean_ctor_set(x_105, 0, x_110);
x_111 = lean_st_ref_set(x_101, x_105, x_106);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_103, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_103, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_103, 3);
lean_inc(x_115);
x_116 = lean_ctor_get(x_103, 5);
lean_inc(x_116);
x_117 = lean_ctor_get(x_103, 6);
lean_inc(x_117);
x_118 = lean_ctor_get(x_103, 7);
lean_inc(x_118);
x_119 = lean_ctor_get(x_103, 8);
lean_inc(x_119);
x_120 = lean_ctor_get(x_103, 9);
lean_inc(x_120);
x_121 = lean_ctor_get(x_103, 10);
lean_inc(x_121);
x_122 = lean_ctor_get(x_103, 11);
lean_inc(x_122);
x_123 = lean_ctor_get_uint8(x_103, sizeof(void*)*13 + 1);
x_124 = lean_ctor_get(x_103, 12);
lean_inc(x_124);
lean_dec(x_103);
x_43 = x_98;
x_44 = x_99;
x_45 = x_100;
x_46 = x_113;
x_47 = x_114;
x_48 = x_115;
x_49 = x_116;
x_50 = x_117;
x_51 = x_118;
x_52 = x_119;
x_53 = x_120;
x_54 = x_121;
x_55 = x_122;
x_56 = x_123;
x_57 = x_124;
x_58 = x_101;
x_59 = x_112;
goto block_97;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; 
x_125 = lean_ctor_get(x_105, 0);
x_126 = lean_ctor_get(x_105, 1);
x_127 = lean_ctor_get(x_105, 2);
x_128 = lean_ctor_get(x_105, 3);
x_129 = lean_ctor_get(x_105, 4);
x_130 = lean_ctor_get(x_105, 6);
x_131 = lean_ctor_get(x_105, 7);
x_132 = lean_ctor_get(x_105, 8);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_105);
x_133 = l_Lean_Kernel_enableDiag(x_125, x_100);
x_134 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_127);
lean_ctor_set(x_134, 3, x_128);
lean_ctor_set(x_134, 4, x_129);
lean_ctor_set(x_134, 5, x_17);
lean_ctor_set(x_134, 6, x_130);
lean_ctor_set(x_134, 7, x_131);
lean_ctor_set(x_134, 8, x_132);
x_135 = lean_st_ref_set(x_101, x_134, x_106);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_ctor_get(x_103, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_103, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_103, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_103, 5);
lean_inc(x_140);
x_141 = lean_ctor_get(x_103, 6);
lean_inc(x_141);
x_142 = lean_ctor_get(x_103, 7);
lean_inc(x_142);
x_143 = lean_ctor_get(x_103, 8);
lean_inc(x_143);
x_144 = lean_ctor_get(x_103, 9);
lean_inc(x_144);
x_145 = lean_ctor_get(x_103, 10);
lean_inc(x_145);
x_146 = lean_ctor_get(x_103, 11);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_103, sizeof(void*)*13 + 1);
x_148 = lean_ctor_get(x_103, 12);
lean_inc(x_148);
lean_dec(x_103);
x_43 = x_98;
x_44 = x_99;
x_45 = x_100;
x_46 = x_137;
x_47 = x_138;
x_48 = x_139;
x_49 = x_140;
x_50 = x_141;
x_51 = x_142;
x_52 = x_143;
x_53 = x_144;
x_54 = x_145;
x_55 = x_146;
x_56 = x_147;
x_57 = x_148;
x_58 = x_101;
x_59 = x_136;
goto block_97;
}
}
block_180:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; 
x_165 = lean_st_mk_ref(x_153, x_164);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = lean_st_ref_get(x_163, x_167);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_PPContext_runCoreM___redArg___closed__26;
x_173 = l_Lean_PrettyPrinter_ppExprLegacy___closed__15;
lean_inc(x_28);
lean_inc(x_8);
x_174 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_174, 0, x_154);
lean_ctor_set(x_174, 1, x_155);
lean_ctor_set(x_174, 2, x_156);
lean_ctor_set(x_174, 3, x_10);
lean_ctor_set(x_174, 4, x_173);
lean_ctor_set(x_174, 5, x_157);
lean_ctor_set(x_174, 6, x_11);
lean_ctor_set(x_174, 7, x_158);
lean_ctor_set(x_174, 8, x_8);
lean_ctor_set(x_174, 9, x_159);
lean_ctor_set(x_174, 10, x_12);
lean_ctor_set(x_174, 11, x_160);
lean_ctor_set(x_174, 12, x_28);
lean_ctor_set_uint8(x_174, sizeof(void*)*13, x_162);
x_175 = lean_unbox(x_34);
lean_ctor_set_uint8(x_174, sizeof(void*)*13 + 1, x_175);
x_176 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_4, x_161);
x_177 = l_Lean_Kernel_isDiagnosticsEnabled(x_171);
lean_dec(x_171);
if (x_177 == 0)
{
if (x_176 == 0)
{
uint8_t x_178; 
lean_dec(x_174);
x_178 = lean_unbox(x_34);
x_43 = x_166;
x_44 = x_172;
x_45 = x_176;
x_46 = x_154;
x_47 = x_155;
x_48 = x_10;
x_49 = x_157;
x_50 = x_11;
x_51 = x_158;
x_52 = x_8;
x_53 = x_159;
x_54 = x_12;
x_55 = x_160;
x_56 = x_178;
x_57 = x_28;
x_58 = x_163;
x_59 = x_170;
goto block_97;
}
else
{
lean_dec(x_28);
lean_dec(x_8);
x_98 = x_166;
x_99 = x_172;
x_100 = x_176;
x_101 = x_163;
x_102 = x_170;
x_103 = x_174;
goto block_149;
}
}
else
{
if (x_176 == 0)
{
lean_dec(x_28);
lean_dec(x_8);
x_98 = x_166;
x_99 = x_172;
x_100 = x_176;
x_101 = x_163;
x_102 = x_170;
x_103 = x_174;
goto block_149;
}
else
{
uint8_t x_179; 
lean_dec(x_174);
x_179 = lean_unbox(x_34);
x_43 = x_166;
x_44 = x_172;
x_45 = x_176;
x_46 = x_154;
x_47 = x_155;
x_48 = x_10;
x_49 = x_157;
x_50 = x_11;
x_51 = x_158;
x_52 = x_8;
x_53 = x_159;
x_54 = x_12;
x_55 = x_160;
x_56 = x_179;
x_57 = x_28;
x_58 = x_163;
x_59 = x_170;
goto block_97;
}
}
}
block_202:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_st_ref_take(x_24, x_32);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = !lean_is_exclusive(x_182);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_185 = lean_ctor_get(x_182, 0);
x_186 = lean_ctor_get(x_182, 5);
lean_dec(x_186);
x_187 = l_Lean_Kernel_enableDiag(x_185, x_162);
lean_ctor_set(x_182, 5, x_17);
lean_ctor_set(x_182, 0, x_187);
x_188 = lean_st_ref_set(x_24, x_182, x_183);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
lean_inc(x_24);
x_163 = x_24;
x_164 = x_189;
goto block_180;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_190 = lean_ctor_get(x_182, 0);
x_191 = lean_ctor_get(x_182, 1);
x_192 = lean_ctor_get(x_182, 2);
x_193 = lean_ctor_get(x_182, 3);
x_194 = lean_ctor_get(x_182, 4);
x_195 = lean_ctor_get(x_182, 6);
x_196 = lean_ctor_get(x_182, 7);
x_197 = lean_ctor_get(x_182, 8);
lean_inc(x_197);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_182);
x_198 = l_Lean_Kernel_enableDiag(x_190, x_162);
x_199 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_191);
lean_ctor_set(x_199, 2, x_192);
lean_ctor_set(x_199, 3, x_193);
lean_ctor_set(x_199, 4, x_194);
lean_ctor_set(x_199, 5, x_17);
lean_ctor_set(x_199, 6, x_195);
lean_ctor_set(x_199, 7, x_196);
lean_ctor_set(x_199, 8, x_197);
x_200 = lean_st_ref_set(x_24, x_199, x_183);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
lean_inc(x_24);
x_163 = x_24;
x_164 = x_201;
goto block_180;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppTactic___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppTactic___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_ppTactic___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_ppTactic___closed__1;
x_6 = l_Lean_PrettyPrinter_ppCategory(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppCommand___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("command", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppCommand___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_ppCommand___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppCommand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_PrettyPrinter_ppCommand___closed__1;
x_6 = l_Lean_PrettyPrinter_ppCategory(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppModule(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_parenthesizer), 5, 0);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_PrettyPrinter_parenthesize(x_5, x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Parser_Module_module_formatter), 5, 0);
x_10 = l_Lean_PrettyPrinter_format(x_9, x_7, x_2, x_3, x_8);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppSignature___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_pp_raw;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppSignature___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConstWithSignature___boxed), 8, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_ppSignature___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" : ", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_ppSignature(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = l_Lean_ConstantInfo_levelParams(x_9);
x_13 = lean_box(0);
x_14 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_12, x_13);
x_15 = l_Lean_Expr_const___override(x_1, x_14);
x_16 = l_Lean_PrettyPrinter_ppSignature___closed__0;
x_17 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_11, x_16);
lean_dec(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
lean_dec(x_9);
x_18 = lean_box(0);
x_19 = l_Lean_PrettyPrinter_ppSignature___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_20 = l_Lean_PrettyPrinter_delabCore___redArg(x_15, x_18, x_19, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
x_26 = l_Lean_PrettyPrinter_ppTerm(x_24, x_4, x_5, x_22);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_21, 0, x_28);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_21, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_free_object(x_21);
lean_dec(x_25);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = l_Lean_PrettyPrinter_ppTerm(x_36, x_4, x_5, x_22);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_37);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_20);
if (x_48 == 0)
{
return x_20;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_20, 0);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_20);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_expr_dbg_to_string(x_15);
lean_dec(x_15);
x_53 = l_Lean_PrettyPrinter_ppSignature___closed__2;
x_54 = lean_string_append(x_52, x_53);
x_55 = l_Lean_ConstantInfo_type(x_9);
lean_dec(x_9);
x_56 = lean_expr_dbg_to_string(x_55);
lean_dec(x_55);
x_57 = lean_string_append(x_54, x_56);
lean_dec(x_56);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_7, 0, x_60);
return x_7;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_61 = lean_ctor_get(x_7, 0);
x_62 = lean_ctor_get(x_7, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_7);
x_63 = lean_ctor_get(x_4, 2);
lean_inc(x_63);
x_64 = l_Lean_ConstantInfo_levelParams(x_61);
x_65 = lean_box(0);
x_66 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_64, x_65);
x_67 = l_Lean_Expr_const___override(x_1, x_66);
x_68 = l_Lean_PrettyPrinter_ppSignature___closed__0;
x_69 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_63, x_68);
lean_dec(x_63);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_61);
x_70 = lean_box(0);
x_71 = l_Lean_PrettyPrinter_ppSignature___closed__1;
lean_inc(x_5);
lean_inc(x_4);
x_72 = l_Lean_PrettyPrinter_delabCore___redArg(x_67, x_70, x_71, x_2, x_3, x_4, x_5, x_62);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
x_78 = l_Lean_PrettyPrinter_ppTerm(x_75, x_4, x_5, x_74);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_77;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_76);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_77);
lean_dec(x_76);
x_84 = lean_ctor_get(x_78, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_78, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_86 = x_78;
} else {
 lean_dec_ref(x_78);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_5);
lean_dec(x_4);
x_88 = lean_ctor_get(x_72, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_90 = x_72;
} else {
 lean_dec_ref(x_72);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_expr_dbg_to_string(x_67);
lean_dec(x_67);
x_93 = l_Lean_PrettyPrinter_ppSignature___closed__2;
x_94 = lean_string_append(x_92, x_93);
x_95 = l_Lean_ConstantInfo_type(x_61);
lean_dec(x_61);
x_96 = lean_expr_dbg_to_string(x_95);
lean_dec(x_95);
x_97 = lean_string_append(x_94, x_96);
lean_dec(x_96);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_62);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_7);
if (x_102 == 0)
{
return x_7;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_7, 0);
x_104 = lean_ctor_get(x_7, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_7);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_1 = x_2;
goto _start;
}
case 4:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_5);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_8);
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
case 5:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_12);
lean_ctor_set(x_1, 1, x_13);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
case 6:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_19);
lean_ctor_set(x_1, 0, x_20);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_21);
x_23 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
case 7:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_25);
x_28 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_26);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_29);
x_32 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_30);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
case 8:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 1);
x_36 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_38);
x_40 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
case 9:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get(x_1, 2);
x_44 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_42);
x_45 = lean_array_size(x_43);
x_46 = 0;
x_47 = l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(x_45, x_46, x_43);
lean_ctor_set(x_1, 2, x_47);
lean_ctor_set(x_1, 1, x_44);
return x_1;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_1, 0);
x_49 = lean_ctor_get(x_1, 1);
x_50 = lean_ctor_get(x_1, 2);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_1);
x_51 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_49);
x_52 = lean_array_size(x_50);
x_53 = 0;
x_54 = l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(x_52, x_53, x_50);
x_55 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_51);
lean_ctor_set(x_55, 2, x_54);
return x_55;
}
}
default: 
{
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_4);
lean_ctor_set(x_2, 1, x_5);
x_6 = lean_apply_2(x_1, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = lean_apply_2(x_1, lean_box(0), x_2);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_apply_3(x_4, lean_box(0), x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_28; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_28 = l_Lean_Exception_isInterrupt(x_8);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_8);
x_10 = x_29;
goto block_27;
}
else
{
x_10 = x_28;
goto block_27;
}
block_27:
{
if (x_10 == 0)
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_8, 1);
x_16 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_15);
lean_ctor_set(x_8, 1, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_7);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_23 = x_8;
} else {
 lean_dec_ref(x_8);
 x_23 = lean_box(0);
}
x_24 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_22);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
return x_7;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
return x_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_26; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_26 = l_Lean_Exception_isInterrupt(x_6);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_6);
x_8 = x_27;
goto block_25;
}
else
{
x_8 = x_26;
goto block_25;
}
block_25:
{
if (x_8 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
x_14 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_13);
lean_ctor_set(x_6, 1, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_5, 0, x_18);
return x_5;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_21 = x_6;
} else {
 lean_dec_ref(x_6);
 x_21 = lean_box(0);
}
x_22 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_noContext(x_20);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_7);
return x_24;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_5;
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
return x_5;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = l_Lean_getPPMVarsLevels(x_4);
x_6 = l_Lean_Level_format(x_2, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___lam__1___closed__0____x40_Lean_PrettyPrinter___hyg_1084_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_box(0);
x_5 = l_Lean_PrettyPrinter_initFn___lam__1___closed__0____x40_Lean_PrettyPrinter___hyg_1084_;
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos), 8, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_5);
x_7 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0), 7, 2);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_6);
x_8 = l_Lean_PPContext_runMetaM___redArg(x_1, x_7, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppConstNameWithInfos), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0), 7, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_PPContext_runMetaM___redArg(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_ppGoal), 6, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__0), 7, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_PPContext_runMetaM___redArg(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppTerm), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_withoutContext___at___Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084__spec__1), 5, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_4);
x_6 = l_Lean_PPContext_runCoreM___redArg(x_1, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1084_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_ppFnsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084____boxed), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084____boxed), 3, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084____boxed), 3, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084____boxed), 3, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084____boxed), 3, 0);
x_7 = l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1084_;
x_8 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_2);
lean_ctor_set(x_8, 4, x_5);
x_9 = lean_st_ref_set(x_7, x_8, x_1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn___lam__0____x40_Lean_PrettyPrinter___hyg_1084_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn___lam__1____x40_Lean_PrettyPrinter___hyg_1084_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn___lam__2____x40_Lean_PrettyPrinter___hyg_1084_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn___lam__3____x40_Lean_PrettyPrinter___hyg_1084_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PrettyPrinter_initFn___lam__4____x40_Lean_PrettyPrinter___hyg_1084_(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_214_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_214_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_214_;
x_2 = l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_1164_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_1164_;
x_2 = l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_1164_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_1164_;
x_2 = l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_1164_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_214_;
x_2 = l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_1164_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__8____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_214_;
x_2 = l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_1164_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__9____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__10____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_initFn___closed__9____x40_Lean_PrettyPrinter___hyg_1164_;
x_2 = l_Lean_PrettyPrinter_initFn___closed__8____x40_Lean_PrettyPrinter___hyg_1164_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn___closed__11____x40_Lean_PrettyPrinter___hyg_1164_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1164u);
x_2 = l_Lean_PrettyPrinter_initFn___closed__10____x40_Lean_PrettyPrinter___hyg_1164_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1164_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1164_;
x_3 = lean_box(0);
x_4 = l_Lean_PrettyPrinter_initFn___closed__11____x40_Lean_PrettyPrinter___hyg_1164_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("parenthesizer", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_registerParserCompilers___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_parenthesizerAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_combinatorParenthesizerAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_registerParserCompilers___closed__3;
x_2 = l_Lean_PrettyPrinter_registerParserCompilers___closed__2;
x_3 = l_Lean_PrettyPrinter_registerParserCompilers___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("formatter", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_registerParserCompilers___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_formatterAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_combinatorFormatterAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_registerParserCompilers___closed__8;
x_2 = l_Lean_PrettyPrinter_registerParserCompilers___closed__7;
x_3 = l_Lean_PrettyPrinter_registerParserCompilers___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_registerParserCompilers(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PrettyPrinter_registerParserCompilers___closed__4;
x_3 = l_Lean_ParserCompiler_registerParserCompiler___redArg(x_2, x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_PrettyPrinter_registerParserCompilers___closed__9;
x_6 = l_Lean_ParserCompiler_registerParserCompiler___redArg(x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[Error pretty printing: ", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runMetaM___redArg(x_2, x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1;
x_15 = lean_io_error_to_string(x_13);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1;
x_24 = lean_io_error_to_string(x_21);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_MessageData_ofFormat(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofFormatWithInfosM___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(invalid MessageData.lazy, missing context)", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed), 2, 0);
x_5 = l_Lean_MessageData_lazy(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_ofFormatWithInfosM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_ofFormatWithInfosM___lam__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ofFormatWithInfosM___lam__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_7 = l_Lean_instantiateMVarsCore(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Expr_hasSyntheticSorry(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_9;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PPContext_runMetaM___redArg(x_2, x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1;
x_12 = lean_io_error_to_string(x_10);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_MessageData_ofFormat(x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1;
x_21 = lean_io_error_to_string(x_18);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_ofLazyM___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = 0;
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_ofLazyM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__2___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_MessageData_ofLazyM___lam__0___boxed), 3, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_MessageData_ofLazyM___lam__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lean_MessageData_ofLazyM___closed__0;
x_6 = l_Lean_MessageData_lazy(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_MessageData_ofLazyM_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_ofLazyM___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofLazyM___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_ofLazyM___lam__1(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[Error pretty printing: expression not a constant]", 50, 50);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_ofConst___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_ofConst___closed__2;
x_2 = l_Lean_MessageData_ofConst___closed__1;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PPContext_runCoreM___redArg___closed__22;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MessageData_ofConst___closed__4;
x_2 = l_Lean_MessageData_ofConst___closed__3;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.PrettyPrinter", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.MessageData.ofConst", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("not a constant", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_ofConst___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_MessageData_ofConst___closed__8;
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_unsigned_to_nat(179u);
x_4 = l_Lean_MessageData_ofConst___closed__7;
x_5 = l_Lean_MessageData_ofConst___closed__6;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_ofConst(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isConst(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_MessageData_ofConst___closed__4;
x_4 = l_Lean_MessageData_ofConst___closed__5;
x_5 = l_Lean_MessageData_ofExpr(x_1);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
x_8 = l_Lean_MessageData_ofConst___closed__9;
x_9 = l_panic___redArg(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1;
x_11 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_11, 0, x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabConst), 7, 0);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos), 11, 4);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppExprWithInfos), 8, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_13);
x_16 = l_Lean_MessageData_ofFormatWithInfosM(x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_MessageData_signature___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[Error pretty printing signature: ", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_MessageData_signature___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MessageData_signature___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_ppSignature), 6, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_PPContext_runMetaM___redArg(x_2, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = l_Lean_MessageData_signature___lam__0___closed__1;
x_16 = lean_io_error_to_string(x_14);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_MessageData_ofFormat(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofConst___closed__2;
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_ofConst___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_MessageData_ofName(x_1);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_28);
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = l_Lean_MessageData_signature___lam__0___closed__1;
x_32 = lean_io_error_to_string(x_29);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_MessageData_ofFormat(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_MessageData_ofConst___closed__2;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_MessageData_ofConst___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_MessageData_ofName(x_1);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_30);
return x_45;
}
}
}
}
static lean_object* _init_l_Lean_MessageData_signature___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofFormatWithInfosM___lam__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_alloc_closure((void*)(l_Lean_MessageData_signature___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_MessageData_signature___closed__0;
x_4 = l_Lean_MessageData_ofLazyM___closed__0;
x_5 = l_Lean_MessageData_lazy(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_signature___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MessageData_signature___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Lean_PrettyPrinter_Delaborator(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ParserCompiler(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_NumObjs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_ShareCommon(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter_Delaborator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Formatter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ParserCompiler(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_NumObjs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ShareCommon(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PPContext_runCoreM___redArg___closed__0 = _init_l_Lean_PPContext_runCoreM___redArg___closed__0();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__0);
l_Lean_PPContext_runCoreM___redArg___closed__1 = _init_l_Lean_PPContext_runCoreM___redArg___closed__1();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__1);
l_Lean_PPContext_runCoreM___redArg___closed__2 = _init_l_Lean_PPContext_runCoreM___redArg___closed__2();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__2);
l_Lean_PPContext_runCoreM___redArg___closed__3 = _init_l_Lean_PPContext_runCoreM___redArg___closed__3();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__3);
l_Lean_PPContext_runCoreM___redArg___closed__4 = _init_l_Lean_PPContext_runCoreM___redArg___closed__4();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__4);
l_Lean_PPContext_runCoreM___redArg___closed__5 = _init_l_Lean_PPContext_runCoreM___redArg___closed__5();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__5);
l_Lean_PPContext_runCoreM___redArg___closed__6 = _init_l_Lean_PPContext_runCoreM___redArg___closed__6();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__6);
l_Lean_PPContext_runCoreM___redArg___closed__7 = _init_l_Lean_PPContext_runCoreM___redArg___closed__7();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__7);
l_Lean_PPContext_runCoreM___redArg___closed__8 = _init_l_Lean_PPContext_runCoreM___redArg___closed__8();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__8);
l_Lean_PPContext_runCoreM___redArg___closed__9 = _init_l_Lean_PPContext_runCoreM___redArg___closed__9();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__9);
l_Lean_PPContext_runCoreM___redArg___closed__10 = _init_l_Lean_PPContext_runCoreM___redArg___closed__10();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__10);
l_Lean_PPContext_runCoreM___redArg___closed__11 = _init_l_Lean_PPContext_runCoreM___redArg___closed__11();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__11);
l_Lean_PPContext_runCoreM___redArg___closed__12 = _init_l_Lean_PPContext_runCoreM___redArg___closed__12();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__12);
l_Lean_PPContext_runCoreM___redArg___closed__13 = _init_l_Lean_PPContext_runCoreM___redArg___closed__13();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__13);
l_Lean_PPContext_runCoreM___redArg___closed__14 = _init_l_Lean_PPContext_runCoreM___redArg___closed__14();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__14);
l_Lean_PPContext_runCoreM___redArg___closed__15 = _init_l_Lean_PPContext_runCoreM___redArg___closed__15();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__15);
l_Lean_PPContext_runCoreM___redArg___closed__16 = _init_l_Lean_PPContext_runCoreM___redArg___closed__16();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__16);
l_Lean_PPContext_runCoreM___redArg___closed__17 = _init_l_Lean_PPContext_runCoreM___redArg___closed__17();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__17);
l_Lean_PPContext_runCoreM___redArg___closed__18 = _init_l_Lean_PPContext_runCoreM___redArg___closed__18();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__18);
l_Lean_PPContext_runCoreM___redArg___closed__19 = _init_l_Lean_PPContext_runCoreM___redArg___closed__19();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__19);
l_Lean_PPContext_runCoreM___redArg___closed__20 = _init_l_Lean_PPContext_runCoreM___redArg___closed__20();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__20);
l_Lean_PPContext_runCoreM___redArg___closed__21 = _init_l_Lean_PPContext_runCoreM___redArg___closed__21();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__21);
l_Lean_PPContext_runCoreM___redArg___closed__22 = _init_l_Lean_PPContext_runCoreM___redArg___closed__22();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__22);
l_Lean_PPContext_runCoreM___redArg___closed__23 = _init_l_Lean_PPContext_runCoreM___redArg___closed__23();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__23);
l_Lean_PPContext_runCoreM___redArg___closed__24 = _init_l_Lean_PPContext_runCoreM___redArg___closed__24();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__24);
l_Lean_PPContext_runCoreM___redArg___closed__25 = _init_l_Lean_PPContext_runCoreM___redArg___closed__25();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__25);
l_Lean_PPContext_runCoreM___redArg___closed__26 = _init_l_Lean_PPContext_runCoreM___redArg___closed__26();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__26);
l_Lean_PPContext_runCoreM___redArg___closed__27 = _init_l_Lean_PPContext_runCoreM___redArg___closed__27();
lean_mark_persistent(l_Lean_PPContext_runCoreM___redArg___closed__27);
l_Lean_PPContext_runMetaM___redArg___closed__0 = _init_l_Lean_PPContext_runMetaM___redArg___closed__0();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__0);
l_Lean_PPContext_runMetaM___redArg___closed__1 = _init_l_Lean_PPContext_runMetaM___redArg___closed__1();
l_Lean_PPContext_runMetaM___redArg___closed__2 = _init_l_Lean_PPContext_runMetaM___redArg___closed__2();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__2);
l_Lean_PPContext_runMetaM___redArg___closed__3 = _init_l_Lean_PPContext_runMetaM___redArg___closed__3();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__3);
l_Lean_PPContext_runMetaM___redArg___closed__4 = _init_l_Lean_PPContext_runMetaM___redArg___closed__4();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__4);
l_Lean_PPContext_runMetaM___redArg___closed__5 = _init_l_Lean_PPContext_runMetaM___redArg___closed__5();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__5);
l_Lean_PPContext_runMetaM___redArg___closed__6 = _init_l_Lean_PPContext_runMetaM___redArg___closed__6();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__6);
l_Lean_PPContext_runMetaM___redArg___closed__7 = _init_l_Lean_PPContext_runMetaM___redArg___closed__7();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__7);
l_Lean_PPContext_runMetaM___redArg___closed__8 = _init_l_Lean_PPContext_runMetaM___redArg___closed__8();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__8);
l_Lean_PPContext_runMetaM___redArg___closed__9 = _init_l_Lean_PPContext_runMetaM___redArg___closed__9();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__9);
l_Lean_PPContext_runMetaM___redArg___closed__10 = _init_l_Lean_PPContext_runMetaM___redArg___closed__10();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__10);
l_Lean_PPContext_runMetaM___redArg___closed__11 = _init_l_Lean_PPContext_runMetaM___redArg___closed__11();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__11);
l_Lean_PPContext_runMetaM___redArg___closed__12 = _init_l_Lean_PPContext_runMetaM___redArg___closed__12();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__12);
l_Lean_PPContext_runMetaM___redArg___closed__13 = _init_l_Lean_PPContext_runMetaM___redArg___closed__13();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__13);
l_Lean_PPContext_runMetaM___redArg___closed__14 = _init_l_Lean_PPContext_runMetaM___redArg___closed__14();
lean_mark_persistent(l_Lean_PPContext_runMetaM___redArg___closed__14);
l_Lean_PrettyPrinter_ppTerm___closed__0 = _init_l_Lean_PrettyPrinter_ppTerm___closed__0();
lean_mark_persistent(l_Lean_PrettyPrinter_ppTerm___closed__0);
l_Lean_PrettyPrinter_ppTerm___closed__1 = _init_l_Lean_PrettyPrinter_ppTerm___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppTerm___closed__1);
l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_214_ = _init_l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_214_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_214_);
l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_214_ = _init_l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_214_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_214_);
l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_214_ = _init_l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_214_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_214_);
l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_214_ = _init_l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_214_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_214_);
l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_214_ = _init_l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_214_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_214_);
l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_214_ = _init_l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_214_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_214_);
l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_214_ = _init_l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_214_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_214_);
l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_214_ = _init_l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_214_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_214_);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_214_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_pp_exprSizes = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_pp_exprSizes);
lean_dec_ref(res);
}l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0 = _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0();
lean_mark_persistent(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__0);
l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1 = _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1();
lean_mark_persistent(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__1);
l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2 = _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2();
lean_mark_persistent(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__2);
l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3 = _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3();
lean_mark_persistent(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__3);
l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4 = _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4();
lean_mark_persistent(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__4);
l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5 = _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5();
lean_mark_persistent(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__5);
l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__6 = _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__6();
lean_mark_persistent(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__6);
l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__7 = _init_l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__7();
lean_mark_persistent(l___private_Lean_PrettyPrinter_0__Lean_PrettyPrinter_maybePrependExprSizes___redArg___closed__7);
l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0 = _init_l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0();
lean_mark_persistent(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__0);
l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1 = _init_l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__1);
l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2 = _init_l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__2);
l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3 = _init_l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_ppConstNameWithInfos___closed__3);
l_Lean_PrettyPrinter_ppExprLegacy___closed__0 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__0();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__0);
l_Lean_PrettyPrinter_ppExprLegacy___closed__1 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__1);
l_Lean_PrettyPrinter_ppExprLegacy___closed__2 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__2);
l_Lean_PrettyPrinter_ppExprLegacy___closed__3 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__3);
l_Lean_PrettyPrinter_ppExprLegacy___closed__4 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__4);
l_Lean_PrettyPrinter_ppExprLegacy___closed__5 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__5);
l_Lean_PrettyPrinter_ppExprLegacy___closed__6 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__6);
l_Lean_PrettyPrinter_ppExprLegacy___closed__7 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__7);
l_Lean_PrettyPrinter_ppExprLegacy___closed__8 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__8);
l_Lean_PrettyPrinter_ppExprLegacy___closed__9 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__9);
l_Lean_PrettyPrinter_ppExprLegacy___closed__10 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__10);
l_Lean_PrettyPrinter_ppExprLegacy___closed__11 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__11);
l_Lean_PrettyPrinter_ppExprLegacy___closed__12 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__12);
l_Lean_PrettyPrinter_ppExprLegacy___closed__13 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__13);
l_Lean_PrettyPrinter_ppExprLegacy___closed__14 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__14();
l_Lean_PrettyPrinter_ppExprLegacy___closed__15 = _init_l_Lean_PrettyPrinter_ppExprLegacy___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_ppExprLegacy___closed__15);
l_Lean_PrettyPrinter_ppTactic___closed__0 = _init_l_Lean_PrettyPrinter_ppTactic___closed__0();
lean_mark_persistent(l_Lean_PrettyPrinter_ppTactic___closed__0);
l_Lean_PrettyPrinter_ppTactic___closed__1 = _init_l_Lean_PrettyPrinter_ppTactic___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppTactic___closed__1);
l_Lean_PrettyPrinter_ppCommand___closed__0 = _init_l_Lean_PrettyPrinter_ppCommand___closed__0();
lean_mark_persistent(l_Lean_PrettyPrinter_ppCommand___closed__0);
l_Lean_PrettyPrinter_ppCommand___closed__1 = _init_l_Lean_PrettyPrinter_ppCommand___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppCommand___closed__1);
l_Lean_PrettyPrinter_ppSignature___closed__0 = _init_l_Lean_PrettyPrinter_ppSignature___closed__0();
lean_mark_persistent(l_Lean_PrettyPrinter_ppSignature___closed__0);
l_Lean_PrettyPrinter_ppSignature___closed__1 = _init_l_Lean_PrettyPrinter_ppSignature___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_ppSignature___closed__1);
l_Lean_PrettyPrinter_ppSignature___closed__2 = _init_l_Lean_PrettyPrinter_ppSignature___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_ppSignature___closed__2);
l_Lean_PrettyPrinter_initFn___lam__1___closed__0____x40_Lean_PrettyPrinter___hyg_1084_ = _init_l_Lean_PrettyPrinter_initFn___lam__1___closed__0____x40_Lean_PrettyPrinter___hyg_1084_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___lam__1___closed__0____x40_Lean_PrettyPrinter___hyg_1084_);
l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1084_ = _init_l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1084_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1084_);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1084_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__0____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__1____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__2____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__3____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__4____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__5____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__6____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__7____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__8____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__8____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__8____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__9____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__9____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__9____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__10____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__10____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__10____x40_Lean_PrettyPrinter___hyg_1164_);
l_Lean_PrettyPrinter_initFn___closed__11____x40_Lean_PrettyPrinter___hyg_1164_ = _init_l_Lean_PrettyPrinter_initFn___closed__11____x40_Lean_PrettyPrinter___hyg_1164_();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn___closed__11____x40_Lean_PrettyPrinter___hyg_1164_);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter___hyg_1164_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_PrettyPrinter_registerParserCompilers___closed__0 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__0();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__0);
l_Lean_PrettyPrinter_registerParserCompilers___closed__1 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__1);
l_Lean_PrettyPrinter_registerParserCompilers___closed__2 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__2);
l_Lean_PrettyPrinter_registerParserCompilers___closed__3 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__3);
l_Lean_PrettyPrinter_registerParserCompilers___closed__4 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__4);
l_Lean_PrettyPrinter_registerParserCompilers___closed__5 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__5);
l_Lean_PrettyPrinter_registerParserCompilers___closed__6 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__6);
l_Lean_PrettyPrinter_registerParserCompilers___closed__7 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__7);
l_Lean_PrettyPrinter_registerParserCompilers___closed__8 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__8);
l_Lean_PrettyPrinter_registerParserCompilers___closed__9 = _init_l_Lean_PrettyPrinter_registerParserCompilers___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_registerParserCompilers___closed__9);
if (builtin) {res = l_Lean_PrettyPrinter_registerParserCompilers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0 = _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0();
lean_mark_persistent(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__0);
l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1 = _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1();
lean_mark_persistent(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__1);
l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2 = _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2();
lean_mark_persistent(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__2);
l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3 = _init_l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3();
lean_mark_persistent(l_Lean_MessageData_ofFormatWithInfosM___lam__0___closed__3);
l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0 = _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0();
lean_mark_persistent(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__0);
l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1 = _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1();
lean_mark_persistent(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__1);
l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2 = _init_l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2();
lean_mark_persistent(l_Lean_MessageData_ofFormatWithInfosM___lam__2___closed__2);
l_Lean_MessageData_ofLazyM___closed__0 = _init_l_Lean_MessageData_ofLazyM___closed__0();
lean_mark_persistent(l_Lean_MessageData_ofLazyM___closed__0);
l_Lean_MessageData_ofConst___closed__0 = _init_l_Lean_MessageData_ofConst___closed__0();
lean_mark_persistent(l_Lean_MessageData_ofConst___closed__0);
l_Lean_MessageData_ofConst___closed__1 = _init_l_Lean_MessageData_ofConst___closed__1();
lean_mark_persistent(l_Lean_MessageData_ofConst___closed__1);
l_Lean_MessageData_ofConst___closed__2 = _init_l_Lean_MessageData_ofConst___closed__2();
lean_mark_persistent(l_Lean_MessageData_ofConst___closed__2);
l_Lean_MessageData_ofConst___closed__3 = _init_l_Lean_MessageData_ofConst___closed__3();
lean_mark_persistent(l_Lean_MessageData_ofConst___closed__3);
l_Lean_MessageData_ofConst___closed__4 = _init_l_Lean_MessageData_ofConst___closed__4();
lean_mark_persistent(l_Lean_MessageData_ofConst___closed__4);
l_Lean_MessageData_ofConst___closed__5 = _init_l_Lean_MessageData_ofConst___closed__5();
lean_mark_persistent(l_Lean_MessageData_ofConst___closed__5);
l_Lean_MessageData_ofConst___closed__6 = _init_l_Lean_MessageData_ofConst___closed__6();
lean_mark_persistent(l_Lean_MessageData_ofConst___closed__6);
l_Lean_MessageData_ofConst___closed__7 = _init_l_Lean_MessageData_ofConst___closed__7();
lean_mark_persistent(l_Lean_MessageData_ofConst___closed__7);
l_Lean_MessageData_ofConst___closed__8 = _init_l_Lean_MessageData_ofConst___closed__8();
lean_mark_persistent(l_Lean_MessageData_ofConst___closed__8);
l_Lean_MessageData_ofConst___closed__9 = _init_l_Lean_MessageData_ofConst___closed__9();
lean_mark_persistent(l_Lean_MessageData_ofConst___closed__9);
l_Lean_MessageData_signature___lam__0___closed__0 = _init_l_Lean_MessageData_signature___lam__0___closed__0();
lean_mark_persistent(l_Lean_MessageData_signature___lam__0___closed__0);
l_Lean_MessageData_signature___lam__0___closed__1 = _init_l_Lean_MessageData_signature___lam__0___closed__1();
lean_mark_persistent(l_Lean_MessageData_signature___lam__0___closed__1);
l_Lean_MessageData_signature___closed__0 = _init_l_Lean_MessageData_signature___closed__0();
lean_mark_persistent(l_Lean_MessageData_signature___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
