// Lean compiler output
// Module: Lean.DefEqAttrib
// Imports: Lean.PrettyPrinter
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
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_validateDefEqAttr___closed__20;
static lean_object* l_Lean_validateDefEqAttr___closed__16;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__7;
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_validateDefEqAttr___lam__1___closed__3;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__14;
static lean_object* l_Lean_validateDefEqAttr___closed__15;
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__12;
static lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__1;
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__21;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__18;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__2;
static lean_object* l_Lean_validateDefEqAttr___closed__2;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__11;
static lean_object* l_Lean_validateDefEqAttr___lam__1___closed__4;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__13;
uint8_t l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(uint8_t, uint8_t);
static lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
static lean_object* l_Lean_validateDefEqAttr___lam__1___closed__0;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__5;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_DefEqAttrib___hyg_456_;
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__3;
static lean_object* l_Lean_inferDefEqAttr___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static uint64_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__1;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__9;
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2;
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__4;
static lean_object* l_Lean_validateDefEqAttr___closed__14;
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2;
static lean_object* l_Lean_inferDefEqAttr___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3(lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__19;
static lean_object* l_Lean_validateDefEqAttr___closed__1;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__6;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__0;
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__5;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_DefEqAttrib___hyg_456_;
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4;
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__7;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__0;
static lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2;
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__2;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__10;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static uint64_t l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__1;
static lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__2;
uint8_t l_Lean_Environment_asyncMayContain(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_DefEqAttrib___hyg_456_;
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_inferDefEqAttr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__11;
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__24;
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__6;
static lean_object* l_Lean_validateDefEqAttr___closed__30;
extern lean_object* l_Lean_warningAsError;
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___closed__0;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_DefEqAttrib___hyg_456_;
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__25;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__8;
static lean_object* l_Lean_validateDefEqAttr___lam__1___closed__1;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l_Lean_initFn___closed__6____x40_Lean_DefEqAttrib___hyg_456_;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__4;
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__6;
static lean_object* l_Lean_validateDefEqAttr___closed__10;
static lean_object* l_Lean_validateDefEqAttr___closed__22;
lean_object* l_Lean_Meta_addPPExplicitToExposeDiff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__4;
static lean_object* l_Lean_validateDefEqAttr___closed__8;
LEAN_EXPORT lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1(lean_object*);
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__8;
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__0;
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_inferDefEqAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__6;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_DefEqAttrib___hyg_456_;
static uint64_t l_Lean_validateDefEqAttr___closed__28;
LEAN_EXPORT lean_object* l_Lean_defeqAttr;
static lean_object* l_Lean_initFn___closed__5____x40_Lean_DefEqAttrib___hyg_456_;
static lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__0;
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__4;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__9;
static lean_object* l_Lean_validateDefEqAttr___closed__13;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_validateDefEqAttr___lam__1___closed__2;
static lean_object* l_Lean_inferDefEqAttr___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_DefEqAttrib___hyg_456_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__0;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static uint64_t l_Lean_validateDefEqAttr___closed__27;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint8_t l_Lean_isPrivateName(lean_object*);
static uint64_t l_Lean_validateDefEqAttr___closed__29;
static lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__3;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__0;
static lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4;
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0;
static lean_object* l_Lean_validateDefEqAttr___lam__0___closed__2;
static lean_object* l_Lean_validateDefEqAttr___closed__5;
static lean_object* l_Lean_validateDefEqAttr___closed__3;
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_inferDefEqAttr___lam__1___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__12;
lean_object* l_Lean_MessageData_ofLazyM(lean_object*, lean_object*);
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5;
static lean_object* l_Lean_validateDefEqAttr___closed__6;
static lean_object* l_Lean_validateDefEqAttr___closed__17;
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3;
static lean_object* l_Lean_validateDefEqAttr___closed__7;
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_validateDefEqAttr___closed__23;
static lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0;
static lean_object* l_Lean_validateDefEqAttr___closed__26;
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
static lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4;
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_smartUnfolding;
return x_1;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static uint64_t _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; uint64_t x_3; 
x_1 = lean_box(1);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
return x_3;
}
}
static uint64_t _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; uint64_t x_3; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
x_3 = l_Lean_Meta_TransparencyMode_toUInt64(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__6;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_221; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 8);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 9);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 10);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 11);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_23 = lean_ctor_get(x_5, 12);
lean_inc(x_23);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 lean_ctor_release(x_5, 4);
 lean_ctor_release(x_5, 5);
 lean_ctor_release(x_5, 6);
 lean_ctor_release(x_5, 7);
 lean_ctor_release(x_5, 8);
 lean_ctor_release(x_5, 9);
 lean_ctor_release(x_5, 10);
 lean_ctor_release(x_5, 11);
 lean_ctor_release(x_5, 12);
 x_24 = x_5;
} else {
 lean_dec_ref(x_5);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
lean_dec(x_9);
x_26 = lean_box(1);
x_27 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0;
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_13, x_27, x_29);
x_31 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1;
x_32 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_30, x_31);
x_221 = l_Lean_Kernel_isDiagnosticsEnabled(x_25);
lean_dec(x_25);
if (x_221 == 0)
{
if (x_32 == 0)
{
x_33 = x_11;
x_34 = x_12;
x_35 = x_14;
x_36 = x_15;
x_37 = x_16;
x_38 = x_17;
x_39 = x_18;
x_40 = x_19;
x_41 = x_20;
x_42 = x_21;
x_43 = x_22;
x_44 = x_23;
x_45 = x_6;
x_46 = x_10;
goto block_196;
}
else
{
goto block_220;
}
}
else
{
if (x_32 == 0)
{
goto block_220;
}
else
{
x_33 = x_11;
x_34 = x_12;
x_35 = x_14;
x_36 = x_15;
x_37 = x_16;
x_38 = x_17;
x_39 = x_18;
x_40 = x_19;
x_41 = x_20;
x_42 = x_21;
x_43 = x_22;
x_44 = x_23;
x_45 = x_6;
x_46 = x_10;
goto block_196;
}
}
block_196:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_3);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_3, 0);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
uint64_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; lean_object* x_86; 
x_50 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_51 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_52 = lean_ctor_get(x_3, 1);
x_53 = lean_ctor_get(x_3, 2);
x_54 = lean_ctor_get(x_3, 3);
x_55 = lean_ctor_get(x_3, 4);
x_56 = lean_ctor_get(x_3, 5);
x_57 = lean_ctor_get(x_3, 6);
x_58 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_59 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_60 = lean_ctor_get_uint8(x_48, 0);
x_61 = lean_ctor_get_uint8(x_48, 1);
x_62 = lean_ctor_get_uint8(x_48, 2);
x_63 = lean_ctor_get_uint8(x_48, 3);
x_64 = lean_ctor_get_uint8(x_48, 4);
x_65 = lean_ctor_get_uint8(x_48, 5);
x_66 = lean_ctor_get_uint8(x_48, 6);
x_67 = lean_ctor_get_uint8(x_48, 7);
x_68 = lean_ctor_get_uint8(x_48, 8);
x_69 = lean_ctor_get_uint8(x_48, 10);
x_70 = lean_ctor_get_uint8(x_48, 11);
x_71 = lean_ctor_get_uint8(x_48, 12);
x_72 = lean_ctor_get_uint8(x_48, 13);
x_73 = lean_ctor_get_uint8(x_48, 14);
x_74 = lean_ctor_get_uint8(x_48, 15);
x_75 = lean_ctor_get_uint8(x_48, 16);
x_76 = lean_ctor_get_uint8(x_48, 17);
x_77 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2;
x_78 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_30, x_77);
if (lean_is_scalar(x_24)) {
 x_79 = lean_alloc_ctor(0, 13, 2);
} else {
 x_79 = x_24;
}
lean_ctor_set(x_79, 0, x_33);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_30);
lean_ctor_set(x_79, 3, x_35);
lean_ctor_set(x_79, 4, x_78);
lean_ctor_set(x_79, 5, x_36);
lean_ctor_set(x_79, 6, x_37);
lean_ctor_set(x_79, 7, x_38);
lean_ctor_set(x_79, 8, x_39);
lean_ctor_set(x_79, 9, x_40);
lean_ctor_set(x_79, 10, x_41);
lean_ctor_set(x_79, 11, x_42);
lean_ctor_set(x_79, 12, x_44);
lean_ctor_set_uint8(x_79, sizeof(void*)*13, x_32);
lean_ctor_set_uint8(x_79, sizeof(void*)*13 + 1, x_43);
x_80 = lean_unbox(x_26);
lean_ctor_set_uint8(x_48, 9, x_80);
x_81 = 2;
x_82 = lean_uint64_shift_right(x_50, x_81);
x_83 = lean_uint64_shift_left(x_82, x_81);
x_84 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3;
x_85 = lean_uint64_lor(x_83, x_84);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_85);
lean_inc(x_45);
lean_inc(x_79);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_86 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_79, x_45, x_46);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint64_t x_93; uint64_t x_94; lean_object* x_95; lean_object* x_96; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_91, 0, x_60);
lean_ctor_set_uint8(x_91, 1, x_61);
lean_ctor_set_uint8(x_91, 2, x_62);
lean_ctor_set_uint8(x_91, 3, x_63);
lean_ctor_set_uint8(x_91, 4, x_64);
lean_ctor_set_uint8(x_91, 5, x_65);
lean_ctor_set_uint8(x_91, 6, x_66);
lean_ctor_set_uint8(x_91, 7, x_67);
lean_ctor_set_uint8(x_91, 8, x_68);
x_92 = lean_unbox(x_90);
lean_ctor_set_uint8(x_91, 9, x_92);
lean_ctor_set_uint8(x_91, 10, x_69);
lean_ctor_set_uint8(x_91, 11, x_70);
lean_ctor_set_uint8(x_91, 12, x_71);
lean_ctor_set_uint8(x_91, 13, x_72);
lean_ctor_set_uint8(x_91, 14, x_73);
lean_ctor_set_uint8(x_91, 15, x_74);
lean_ctor_set_uint8(x_91, 16, x_75);
lean_ctor_set_uint8(x_91, 17, x_76);
x_93 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4;
x_94 = lean_uint64_lor(x_83, x_93);
x_95 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_52);
lean_ctor_set(x_95, 2, x_53);
lean_ctor_set(x_95, 3, x_54);
lean_ctor_set(x_95, 4, x_55);
lean_ctor_set(x_95, 5, x_56);
lean_ctor_set(x_95, 6, x_57);
lean_ctor_set_uint64(x_95, sizeof(void*)*7, x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 8, x_51);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 9, x_58);
lean_ctor_set_uint8(x_95, sizeof(void*)*7 + 10, x_59);
x_96 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_95, x_4, x_79, x_45, x_89);
return x_96;
}
else
{
lean_dec(x_79);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_45);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_86;
}
}
else
{
lean_dec(x_79);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_45);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_86;
}
}
else
{
uint64_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; lean_object* x_134; 
x_97 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_98 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_99 = lean_ctor_get(x_3, 1);
x_100 = lean_ctor_get(x_3, 2);
x_101 = lean_ctor_get(x_3, 3);
x_102 = lean_ctor_get(x_3, 4);
x_103 = lean_ctor_get(x_3, 5);
x_104 = lean_ctor_get(x_3, 6);
x_105 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_106 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_107 = lean_ctor_get_uint8(x_48, 0);
x_108 = lean_ctor_get_uint8(x_48, 1);
x_109 = lean_ctor_get_uint8(x_48, 2);
x_110 = lean_ctor_get_uint8(x_48, 3);
x_111 = lean_ctor_get_uint8(x_48, 4);
x_112 = lean_ctor_get_uint8(x_48, 5);
x_113 = lean_ctor_get_uint8(x_48, 6);
x_114 = lean_ctor_get_uint8(x_48, 7);
x_115 = lean_ctor_get_uint8(x_48, 8);
x_116 = lean_ctor_get_uint8(x_48, 10);
x_117 = lean_ctor_get_uint8(x_48, 11);
x_118 = lean_ctor_get_uint8(x_48, 12);
x_119 = lean_ctor_get_uint8(x_48, 13);
x_120 = lean_ctor_get_uint8(x_48, 14);
x_121 = lean_ctor_get_uint8(x_48, 15);
x_122 = lean_ctor_get_uint8(x_48, 16);
x_123 = lean_ctor_get_uint8(x_48, 17);
lean_dec(x_48);
x_124 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2;
x_125 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_30, x_124);
if (lean_is_scalar(x_24)) {
 x_126 = lean_alloc_ctor(0, 13, 2);
} else {
 x_126 = x_24;
}
lean_ctor_set(x_126, 0, x_33);
lean_ctor_set(x_126, 1, x_34);
lean_ctor_set(x_126, 2, x_30);
lean_ctor_set(x_126, 3, x_35);
lean_ctor_set(x_126, 4, x_125);
lean_ctor_set(x_126, 5, x_36);
lean_ctor_set(x_126, 6, x_37);
lean_ctor_set(x_126, 7, x_38);
lean_ctor_set(x_126, 8, x_39);
lean_ctor_set(x_126, 9, x_40);
lean_ctor_set(x_126, 10, x_41);
lean_ctor_set(x_126, 11, x_42);
lean_ctor_set(x_126, 12, x_44);
lean_ctor_set_uint8(x_126, sizeof(void*)*13, x_32);
lean_ctor_set_uint8(x_126, sizeof(void*)*13 + 1, x_43);
x_127 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_127, 0, x_107);
lean_ctor_set_uint8(x_127, 1, x_108);
lean_ctor_set_uint8(x_127, 2, x_109);
lean_ctor_set_uint8(x_127, 3, x_110);
lean_ctor_set_uint8(x_127, 4, x_111);
lean_ctor_set_uint8(x_127, 5, x_112);
lean_ctor_set_uint8(x_127, 6, x_113);
lean_ctor_set_uint8(x_127, 7, x_114);
lean_ctor_set_uint8(x_127, 8, x_115);
x_128 = lean_unbox(x_26);
lean_ctor_set_uint8(x_127, 9, x_128);
lean_ctor_set_uint8(x_127, 10, x_116);
lean_ctor_set_uint8(x_127, 11, x_117);
lean_ctor_set_uint8(x_127, 12, x_118);
lean_ctor_set_uint8(x_127, 13, x_119);
lean_ctor_set_uint8(x_127, 14, x_120);
lean_ctor_set_uint8(x_127, 15, x_121);
lean_ctor_set_uint8(x_127, 16, x_122);
lean_ctor_set_uint8(x_127, 17, x_123);
x_129 = 2;
x_130 = lean_uint64_shift_right(x_97, x_129);
x_131 = lean_uint64_shift_left(x_130, x_129);
x_132 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3;
x_133 = lean_uint64_lor(x_131, x_132);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_ctor_set(x_3, 0, x_127);
lean_ctor_set_uint64(x_3, sizeof(void*)*7, x_133);
lean_inc(x_45);
lean_inc(x_126);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_134 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_3, x_4, x_126, x_45, x_46);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint64_t x_141; uint64_t x_142; lean_object* x_143; lean_object* x_144; 
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_139, 0, x_107);
lean_ctor_set_uint8(x_139, 1, x_108);
lean_ctor_set_uint8(x_139, 2, x_109);
lean_ctor_set_uint8(x_139, 3, x_110);
lean_ctor_set_uint8(x_139, 4, x_111);
lean_ctor_set_uint8(x_139, 5, x_112);
lean_ctor_set_uint8(x_139, 6, x_113);
lean_ctor_set_uint8(x_139, 7, x_114);
lean_ctor_set_uint8(x_139, 8, x_115);
x_140 = lean_unbox(x_138);
lean_ctor_set_uint8(x_139, 9, x_140);
lean_ctor_set_uint8(x_139, 10, x_116);
lean_ctor_set_uint8(x_139, 11, x_117);
lean_ctor_set_uint8(x_139, 12, x_118);
lean_ctor_set_uint8(x_139, 13, x_119);
lean_ctor_set_uint8(x_139, 14, x_120);
lean_ctor_set_uint8(x_139, 15, x_121);
lean_ctor_set_uint8(x_139, 16, x_122);
lean_ctor_set_uint8(x_139, 17, x_123);
x_141 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4;
x_142 = lean_uint64_lor(x_131, x_141);
x_143 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_143, 0, x_139);
lean_ctor_set(x_143, 1, x_99);
lean_ctor_set(x_143, 2, x_100);
lean_ctor_set(x_143, 3, x_101);
lean_ctor_set(x_143, 4, x_102);
lean_ctor_set(x_143, 5, x_103);
lean_ctor_set(x_143, 6, x_104);
lean_ctor_set_uint64(x_143, sizeof(void*)*7, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*7 + 8, x_98);
lean_ctor_set_uint8(x_143, sizeof(void*)*7 + 9, x_105);
lean_ctor_set_uint8(x_143, sizeof(void*)*7 + 10, x_106);
x_144 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_143, x_4, x_126, x_45, x_137);
return x_144;
}
else
{
lean_dec(x_126);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_45);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_134;
}
}
else
{
lean_dec(x_126);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_45);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_134;
}
}
}
else
{
lean_object* x_145; uint64_t x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; lean_object* x_184; lean_object* x_185; 
x_145 = lean_ctor_get(x_3, 0);
x_146 = lean_ctor_get_uint64(x_3, sizeof(void*)*7);
x_147 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_148 = lean_ctor_get(x_3, 1);
x_149 = lean_ctor_get(x_3, 2);
x_150 = lean_ctor_get(x_3, 3);
x_151 = lean_ctor_get(x_3, 4);
x_152 = lean_ctor_get(x_3, 5);
x_153 = lean_ctor_get(x_3, 6);
x_154 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_155 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_145);
lean_dec(x_3);
x_156 = lean_ctor_get_uint8(x_145, 0);
x_157 = lean_ctor_get_uint8(x_145, 1);
x_158 = lean_ctor_get_uint8(x_145, 2);
x_159 = lean_ctor_get_uint8(x_145, 3);
x_160 = lean_ctor_get_uint8(x_145, 4);
x_161 = lean_ctor_get_uint8(x_145, 5);
x_162 = lean_ctor_get_uint8(x_145, 6);
x_163 = lean_ctor_get_uint8(x_145, 7);
x_164 = lean_ctor_get_uint8(x_145, 8);
x_165 = lean_ctor_get_uint8(x_145, 10);
x_166 = lean_ctor_get_uint8(x_145, 11);
x_167 = lean_ctor_get_uint8(x_145, 12);
x_168 = lean_ctor_get_uint8(x_145, 13);
x_169 = lean_ctor_get_uint8(x_145, 14);
x_170 = lean_ctor_get_uint8(x_145, 15);
x_171 = lean_ctor_get_uint8(x_145, 16);
x_172 = lean_ctor_get_uint8(x_145, 17);
if (lean_is_exclusive(x_145)) {
 x_173 = x_145;
} else {
 lean_dec_ref(x_145);
 x_173 = lean_box(0);
}
x_174 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2;
x_175 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_30, x_174);
if (lean_is_scalar(x_24)) {
 x_176 = lean_alloc_ctor(0, 13, 2);
} else {
 x_176 = x_24;
}
lean_ctor_set(x_176, 0, x_33);
lean_ctor_set(x_176, 1, x_34);
lean_ctor_set(x_176, 2, x_30);
lean_ctor_set(x_176, 3, x_35);
lean_ctor_set(x_176, 4, x_175);
lean_ctor_set(x_176, 5, x_36);
lean_ctor_set(x_176, 6, x_37);
lean_ctor_set(x_176, 7, x_38);
lean_ctor_set(x_176, 8, x_39);
lean_ctor_set(x_176, 9, x_40);
lean_ctor_set(x_176, 10, x_41);
lean_ctor_set(x_176, 11, x_42);
lean_ctor_set(x_176, 12, x_44);
lean_ctor_set_uint8(x_176, sizeof(void*)*13, x_32);
lean_ctor_set_uint8(x_176, sizeof(void*)*13 + 1, x_43);
if (lean_is_scalar(x_173)) {
 x_177 = lean_alloc_ctor(0, 0, 18);
} else {
 x_177 = x_173;
}
lean_ctor_set_uint8(x_177, 0, x_156);
lean_ctor_set_uint8(x_177, 1, x_157);
lean_ctor_set_uint8(x_177, 2, x_158);
lean_ctor_set_uint8(x_177, 3, x_159);
lean_ctor_set_uint8(x_177, 4, x_160);
lean_ctor_set_uint8(x_177, 5, x_161);
lean_ctor_set_uint8(x_177, 6, x_162);
lean_ctor_set_uint8(x_177, 7, x_163);
lean_ctor_set_uint8(x_177, 8, x_164);
x_178 = lean_unbox(x_26);
lean_ctor_set_uint8(x_177, 9, x_178);
lean_ctor_set_uint8(x_177, 10, x_165);
lean_ctor_set_uint8(x_177, 11, x_166);
lean_ctor_set_uint8(x_177, 12, x_167);
lean_ctor_set_uint8(x_177, 13, x_168);
lean_ctor_set_uint8(x_177, 14, x_169);
lean_ctor_set_uint8(x_177, 15, x_170);
lean_ctor_set_uint8(x_177, 16, x_171);
lean_ctor_set_uint8(x_177, 17, x_172);
x_179 = 2;
x_180 = lean_uint64_shift_right(x_146, x_179);
x_181 = lean_uint64_shift_left(x_180, x_179);
x_182 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3;
x_183 = lean_uint64_lor(x_181, x_182);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
x_184 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_184, 0, x_177);
lean_ctor_set(x_184, 1, x_148);
lean_ctor_set(x_184, 2, x_149);
lean_ctor_set(x_184, 3, x_150);
lean_ctor_set(x_184, 4, x_151);
lean_ctor_set(x_184, 5, x_152);
lean_ctor_set(x_184, 6, x_153);
lean_ctor_set_uint64(x_184, sizeof(void*)*7, x_183);
lean_ctor_set_uint8(x_184, sizeof(void*)*7 + 8, x_147);
lean_ctor_set_uint8(x_184, sizeof(void*)*7 + 9, x_154);
lean_ctor_set_uint8(x_184, sizeof(void*)*7 + 10, x_155);
lean_inc(x_45);
lean_inc(x_176);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_185 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_184, x_4, x_176, x_45, x_46);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_unbox(x_186);
lean_dec(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; uint64_t x_192; uint64_t x_193; lean_object* x_194; lean_object* x_195; 
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_190, 0, x_156);
lean_ctor_set_uint8(x_190, 1, x_157);
lean_ctor_set_uint8(x_190, 2, x_158);
lean_ctor_set_uint8(x_190, 3, x_159);
lean_ctor_set_uint8(x_190, 4, x_160);
lean_ctor_set_uint8(x_190, 5, x_161);
lean_ctor_set_uint8(x_190, 6, x_162);
lean_ctor_set_uint8(x_190, 7, x_163);
lean_ctor_set_uint8(x_190, 8, x_164);
x_191 = lean_unbox(x_189);
lean_ctor_set_uint8(x_190, 9, x_191);
lean_ctor_set_uint8(x_190, 10, x_165);
lean_ctor_set_uint8(x_190, 11, x_166);
lean_ctor_set_uint8(x_190, 12, x_167);
lean_ctor_set_uint8(x_190, 13, x_168);
lean_ctor_set_uint8(x_190, 14, x_169);
lean_ctor_set_uint8(x_190, 15, x_170);
lean_ctor_set_uint8(x_190, 16, x_171);
lean_ctor_set_uint8(x_190, 17, x_172);
x_192 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4;
x_193 = lean_uint64_lor(x_181, x_192);
x_194 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_194, 0, x_190);
lean_ctor_set(x_194, 1, x_148);
lean_ctor_set(x_194, 2, x_149);
lean_ctor_set(x_194, 3, x_150);
lean_ctor_set(x_194, 4, x_151);
lean_ctor_set(x_194, 5, x_152);
lean_ctor_set(x_194, 6, x_153);
lean_ctor_set_uint64(x_194, sizeof(void*)*7, x_193);
lean_ctor_set_uint8(x_194, sizeof(void*)*7 + 8, x_147);
lean_ctor_set_uint8(x_194, sizeof(void*)*7 + 9, x_154);
lean_ctor_set_uint8(x_194, sizeof(void*)*7 + 10, x_155);
x_195 = l_Lean_Meta_isExprDefEq(x_1, x_2, x_194, x_4, x_176, x_45, x_188);
return x_195;
}
else
{
lean_dec(x_176);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_45);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_185;
}
}
else
{
lean_dec(x_176);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_45);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_185;
}
}
}
block_220:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_197 = lean_st_ref_take(x_6, x_10);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = !lean_is_exclusive(x_198);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_198, 0);
x_202 = lean_ctor_get(x_198, 5);
lean_dec(x_202);
x_203 = l_Lean_Kernel_enableDiag(x_201, x_32);
x_204 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7;
lean_ctor_set(x_198, 5, x_204);
lean_ctor_set(x_198, 0, x_203);
x_205 = lean_st_ref_set(x_6, x_198, x_199);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_33 = x_11;
x_34 = x_12;
x_35 = x_14;
x_36 = x_15;
x_37 = x_16;
x_38 = x_17;
x_39 = x_18;
x_40 = x_19;
x_41 = x_20;
x_42 = x_21;
x_43 = x_22;
x_44 = x_23;
x_45 = x_6;
x_46 = x_206;
goto block_196;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_207 = lean_ctor_get(x_198, 0);
x_208 = lean_ctor_get(x_198, 1);
x_209 = lean_ctor_get(x_198, 2);
x_210 = lean_ctor_get(x_198, 3);
x_211 = lean_ctor_get(x_198, 4);
x_212 = lean_ctor_get(x_198, 6);
x_213 = lean_ctor_get(x_198, 7);
x_214 = lean_ctor_get(x_198, 8);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_198);
x_215 = l_Lean_Kernel_enableDiag(x_207, x_32);
x_216 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7;
x_217 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_208);
lean_ctor_set(x_217, 2, x_209);
lean_ctor_set(x_217, 3, x_210);
lean_ctor_set(x_217, 4, x_211);
lean_ctor_set(x_217, 5, x_216);
lean_ctor_set(x_217, 6, x_212);
lean_ctor_set(x_217, 7, x_213);
lean_ctor_set(x_217, 8, x_214);
x_218 = lean_st_ref_set(x_6, x_217, x_199);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_33 = x_11;
x_34 = x_12;
x_35 = x_14;
x_36 = x_15;
x_37 = x_16;
x_38 = x_17;
x_39 = x_18;
x_40 = x_19;
x_41 = x_20;
x_42 = x_21;
x_43 = x_22;
x_44 = x_23;
x_45 = x_6;
x_46 = x_219;
goto block_196;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 5);
lean_dec(x_13);
x_14 = l_Lean_Environment_setExporting(x_12, x_2);
lean_ctor_set(x_9, 5, x_3);
lean_ctor_set(x_9, 0, x_14);
x_15 = lean_st_ref_set(x_1, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_dec(x_21);
lean_ctor_set(x_18, 1, x_5);
x_22 = lean_st_ref_set(x_4, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_st_ref_set(x_4, x_33, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
x_42 = lean_ctor_get(x_9, 3);
x_43 = lean_ctor_get(x_9, 4);
x_44 = lean_ctor_get(x_9, 6);
x_45 = lean_ctor_get(x_9, 7);
x_46 = lean_ctor_get(x_9, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_47 = l_Lean_Environment_setExporting(x_39, x_2);
x_48 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_41);
lean_ctor_set(x_48, 3, x_42);
lean_ctor_set(x_48, 4, x_43);
lean_ctor_set(x_48, 5, x_3);
lean_ctor_set(x_48, 6, x_44);
lean_ctor_set(x_48, 7, x_45);
lean_ctor_set(x_48, 8, x_46);
x_49 = lean_st_ref_set(x_1, x_48, x_10);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_take(x_4, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_57);
x_60 = lean_st_ref_set(x_4, x_59, x_53);
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
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__3;
x_2 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__2;
x_3 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__1;
x_4 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_5, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 5);
lean_dec(x_17);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_Environment_setExporting(x_16, x_19);
x_21 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7;
lean_ctor_set(x_13, 5, x_21);
lean_ctor_set(x_13, 0, x_20);
x_22 = lean_st_ref_set(x_5, x_13, x_14);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_take(x_3, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_25, 1);
lean_dec(x_28);
x_29 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4;
lean_ctor_set(x_25, 1, x_29);
x_30 = lean_st_ref_set(x_3, x_25, x_26);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_5);
lean_inc(x_3);
x_32 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_33);
x_36 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0(x_5, x_11, x_21, x_3, x_29, x_35, x_34);
lean_dec(x_35);
lean_dec(x_3);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_33);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_box(0);
x_44 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0(x_5, x_11, x_21, x_3, x_29, x_43, x_42);
lean_dec(x_3);
lean_dec(x_5);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 0, x_41);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_25, 0);
x_50 = lean_ctor_get(x_25, 2);
x_51 = lean_ctor_get(x_25, 3);
x_52 = lean_ctor_get(x_25, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_25);
x_53 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4;
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_51);
lean_ctor_set(x_54, 4, x_52);
x_55 = lean_st_ref_set(x_3, x_54, x_26);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
lean_inc(x_5);
lean_inc(x_3);
x_57 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_58);
x_61 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0(x_5, x_11, x_21, x_3, x_53, x_60, x_59);
lean_dec(x_60);
lean_dec(x_3);
lean_dec(x_5);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_dec(x_57);
x_67 = lean_box(0);
x_68 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0(x_5, x_11, x_21, x_3, x_53, x_67, x_66);
lean_dec(x_3);
lean_dec(x_5);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_65);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_72 = lean_ctor_get(x_13, 0);
x_73 = lean_ctor_get(x_13, 1);
x_74 = lean_ctor_get(x_13, 2);
x_75 = lean_ctor_get(x_13, 3);
x_76 = lean_ctor_get(x_13, 4);
x_77 = lean_ctor_get(x_13, 6);
x_78 = lean_ctor_get(x_13, 7);
x_79 = lean_ctor_get(x_13, 8);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_13);
x_80 = lean_box(0);
x_81 = lean_unbox(x_80);
x_82 = l_Lean_Environment_setExporting(x_72, x_81);
x_83 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7;
x_84 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_73);
lean_ctor_set(x_84, 2, x_74);
lean_ctor_set(x_84, 3, x_75);
lean_ctor_set(x_84, 4, x_76);
lean_ctor_set(x_84, 5, x_83);
lean_ctor_set(x_84, 6, x_77);
lean_ctor_set(x_84, 7, x_78);
lean_ctor_set(x_84, 8, x_79);
x_85 = lean_st_ref_set(x_5, x_84, x_14);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_st_ref_take(x_3, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_88, 4);
lean_inc(x_93);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 x_94 = x_88;
} else {
 lean_dec_ref(x_88);
 x_94 = lean_box(0);
}
x_95 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4;
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 5, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_91);
lean_ctor_set(x_96, 3, x_92);
lean_ctor_set(x_96, 4, x_93);
x_97 = lean_st_ref_set(x_3, x_96, x_89);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
lean_inc(x_5);
lean_inc(x_3);
x_99 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_100);
x_103 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0(x_5, x_11, x_83, x_3, x_95, x_102, x_101);
lean_dec(x_102);
lean_dec(x_3);
lean_dec(x_5);
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
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_99, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_99, 1);
lean_inc(x_108);
lean_dec(x_99);
x_109 = lean_box(0);
x_110 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0(x_5, x_11, x_83, x_3, x_95, x_109, x_108);
lean_dec(x_3);
lean_dec(x_5);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
 lean_ctor_set_tag(x_113, 1);
}
lean_ctor_set(x_113, 0, x_107);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not a definitional equality: the left-hand side", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nis not definitionally equal to the right-hand side", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___lam__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("This theorem is exported from the current module. This requires that all definitions that need to be unfolded to prove this theorem must be exposed.", 148, 148);
return x_1;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___lam__0___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___lam__0___closed__7;
x_2 = l_Lean_MessageData_note(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_addPPExplicitToExposeDiff(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_st_ref_get(x_6, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_14, 1);
x_19 = lean_ctor_get(x_14, 0);
lean_dec(x_19);
x_20 = lean_ctor_get_uint8(x_16, sizeof(void*)*8);
lean_dec(x_16);
x_21 = l_Lean_validateDefEqAttr___lam__0___closed__1;
lean_inc(x_12);
x_22 = l_Lean_indentExpr(x_12);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_22);
lean_ctor_set(x_9, 0, x_21);
x_23 = l_Lean_validateDefEqAttr___lam__0___closed__3;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_13);
x_25 = l_Lean_indentExpr(x_13);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_validateDefEqAttr___lam__0___closed__5;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
if (x_20 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_14, 0, x_28);
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_14);
x_29 = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful), 7, 2);
lean_closure_set(x_29, 0, x_12);
lean_closure_set(x_29, 1, x_13);
x_30 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(x_29, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = l_Lean_validateDefEqAttr___lam__0___closed__8;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_30, 0, x_40);
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_dec(x_30);
x_42 = l_Lean_validateDefEqAttr___lam__0___closed__8;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_28);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_49 = lean_ctor_get(x_14, 1);
lean_inc(x_49);
lean_dec(x_14);
x_50 = lean_ctor_get_uint8(x_16, sizeof(void*)*8);
lean_dec(x_16);
x_51 = l_Lean_validateDefEqAttr___lam__0___closed__1;
lean_inc(x_12);
x_52 = l_Lean_indentExpr(x_12);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_52);
lean_ctor_set(x_9, 0, x_51);
x_53 = l_Lean_validateDefEqAttr___lam__0___closed__3;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_9);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_13);
x_55 = l_Lean_indentExpr(x_13);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_validateDefEqAttr___lam__0___closed__5;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
if (x_50 == 0)
{
lean_object* x_59; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_49);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful), 7, 2);
lean_closure_set(x_60, 0, x_12);
lean_closure_set(x_60, 1, x_13);
x_61 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(x_60, x_3, x_4, x_5, x_6, x_49);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_68 = x_61;
} else {
 lean_dec_ref(x_61);
 x_68 = lean_box(0);
}
x_69 = l_Lean_validateDefEqAttr___lam__0___closed__8;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_58);
x_72 = lean_ctor_get(x_61, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_61, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_74 = x_61;
} else {
 lean_dec_ref(x_61);
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
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_76 = lean_ctor_get(x_9, 0);
x_77 = lean_ctor_get(x_9, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_9);
x_78 = lean_st_ref_get(x_6, x_10);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get_uint8(x_80, sizeof(void*)*8);
lean_dec(x_80);
x_84 = l_Lean_validateDefEqAttr___lam__0___closed__1;
lean_inc(x_76);
x_85 = l_Lean_indentExpr(x_76);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_validateDefEqAttr___lam__0___closed__3;
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
lean_inc(x_77);
x_89 = l_Lean_indentExpr(x_77);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_validateDefEqAttr___lam__0___closed__5;
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
if (x_83 == 0)
{
lean_object* x_93; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_82)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_82;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_81);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_82);
x_94 = lean_alloc_closure((void*)(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful), 7, 2);
lean_closure_set(x_94, 0, x_76);
lean_closure_set(x_94, 1, x_77);
x_95 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(x_94, x_3, x_4, x_5, x_6, x_81);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_99 = x_95;
} else {
 lean_dec_ref(x_95);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_92);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_102 = x_95;
} else {
 lean_dec_ref(x_95);
 x_102 = lean_box(0);
}
x_103 = l_Lean_validateDefEqAttr___lam__0___closed__8;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_92);
lean_ctor_set(x_104, 1, x_103);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_102;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_92);
x_106 = lean_ctor_get(x_95, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_95, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_108 = x_95;
} else {
 lean_dec_ref(x_95);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_110 = !lean_is_exclusive(x_8);
if (x_110 == 0)
{
return x_8;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_8, 0);
x_112 = lean_ctor_get(x_8, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_8);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___lam__1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not a definitional equality: the conclusion should be an equality, but is", 73, 73);
return x_1;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_whnf(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_validateDefEqAttr___lam__1___closed__1;
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_validateDefEqAttr___lam__1___closed__3;
x_15 = lean_unsigned_to_nat(30u);
x_16 = l_Lean_inlineExpr(x_9, x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_validateDefEqAttr___lam__0___closed__5;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_19, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = l_Lean_Expr_appFn_x21(x_9);
x_22 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_23 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_23);
lean_inc(x_22);
x_24 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful(x_22, x_23, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_28 = lean_alloc_closure((void*)(l_Lean_validateDefEqAttr___lam__0), 7, 2);
lean_closure_set(x_28, 0, x_22);
lean_closure_set(x_28, 1, x_23);
x_29 = l_Lean_validateDefEqAttr___lam__1___closed__4;
x_30 = lean_array_push(x_29, x_22);
x_31 = lean_array_push(x_30, x_23);
x_32 = l_Lean_MessageData_ofLazyM(x_28, x_31);
x_33 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_32, x_3, x_4, x_5, x_6, x_27);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_24, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_24, 0, x_36);
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_24);
if (x_40 == 0)
{
return x_24;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_24, 0);
x_42 = lean_ctor_get(x_24, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_24);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
return x_8;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_8);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_validateDefEqAttr___closed__6;
x_2 = l_Lean_validateDefEqAttr___closed__5;
x_3 = l_Lean_validateDefEqAttr___closed__4;
x_4 = l_Lean_validateDefEqAttr___closed__3;
x_5 = l_Lean_validateDefEqAttr___closed__2;
x_6 = l_Lean_validateDefEqAttr___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_validateDefEqAttr___closed__11;
x_2 = l_Lean_validateDefEqAttr___closed__10;
x_3 = l_Lean_validateDefEqAttr___closed__9;
x_4 = l_Lean_validateDefEqAttr___closed__8;
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
static lean_object* _init_l_Lean_validateDefEqAttr___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__15() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_validateDefEqAttr___closed__13;
x_4 = l_Lean_validateDefEqAttr___closed__14;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_validateDefEqAttr___closed__16;
x_2 = l_Lean_validateDefEqAttr___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_validateDefEqAttr___closed__17;
x_2 = l_Lean_validateDefEqAttr___closed__15;
x_3 = lean_box(0);
x_4 = l_Lean_validateDefEqAttr___closed__12;
x_5 = l_Lean_validateDefEqAttr___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__19() {
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
static uint64_t _init_l_Lean_validateDefEqAttr___closed__20() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__19;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_validateDefEqAttr___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__23() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_validateDefEqAttr___closed__13;
x_4 = l_Lean_validateDefEqAttr___closed__22;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_validateDefEqAttr___closed__23;
x_3 = l_Lean_validateDefEqAttr___closed__21;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_1 = lean_box(2);
x_2 = lean_box(0);
x_3 = lean_box(0);
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
static uint64_t _init_l_Lean_validateDefEqAttr___closed__27() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 2;
x_2 = l_Lean_validateDefEqAttr___closed__20;
x_3 = lean_uint64_shift_right(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_Lean_validateDefEqAttr___closed__28() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 2;
x_2 = l_Lean_validateDefEqAttr___closed__27;
x_3 = lean_uint64_shift_left(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_Lean_validateDefEqAttr___closed__29() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4;
x_2 = l_Lean_validateDefEqAttr___closed__28;
x_3 = lean_uint64_lor(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_validateDefEqAttr___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_Lean_validateDefEqAttr___closed__25;
x_5 = l_Lean_validateDefEqAttr___closed__24;
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = l_Lean_validateDefEqAttr___closed__29;
x_9 = l_Lean_validateDefEqAttr___closed__26;
x_10 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_4);
lean_ctor_set(x_10, 4, x_3);
lean_ctor_set(x_10, 5, x_2);
lean_ctor_set(x_10, 6, x_1);
lean_ctor_set_uint64(x_10, sizeof(void*)*7, x_8);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 8, x_11);
x_12 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 9, x_12);
x_13 = lean_unbox(x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*7 + 10, x_13);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getConstVal___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_validateDefEqAttr___closed__18;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_validateDefEqAttr___lam__1___boxed), 7, 0);
x_14 = lean_box(0);
x_15 = l_Lean_validateDefEqAttr___closed__30;
x_16 = lean_unbox(x_14);
lean_inc(x_10);
x_17 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1___redArg(x_12, x_13, x_16, x_15, x_10, x_2, x_3, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_10, x_19);
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_dec(x_10);
return x_17;
}
}
else
{
uint8_t x_25; 
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_validateDefEqAttr___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_validateDefEqAttr___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_DefEqAttrib___hyg_456_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defeq", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_DefEqAttrib___hyg_456_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_DefEqAttrib___hyg_456_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_DefEqAttrib___hyg_456_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mark theorem as a definitional equality, to be used by `dsimp`", 62, 62);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_DefEqAttrib___hyg_456_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_validateDefEqAttr), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_DefEqAttrib___hyg_456_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_DefEqAttrib___hyg_456_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defeqAttr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__6____x40_Lean_DefEqAttrib___hyg_456_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__5____x40_Lean_DefEqAttrib___hyg_456_;
x_2 = l_Lean_initFn___closed__4____x40_Lean_DefEqAttrib___hyg_456_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_DefEqAttrib___hyg_456_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_DefEqAttrib___hyg_456_;
x_3 = l_Lean_initFn___closed__2____x40_Lean_DefEqAttrib___hyg_456_;
x_4 = l_Lean_initFn___closed__3____x40_Lean_DefEqAttrib___hyg_456_;
x_5 = l_Lean_initFn___closed__6____x40_Lean_DefEqAttrib___hyg_456_;
x_6 = lean_box(0);
x_7 = lean_box(3);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_5, x_8, x_9, x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Marks the theorem as a definitional equality.\n\nThe theorem must be an equality that holds by `rfl`. This allows `dsimp` to use this theorem\nwhen rewriting.\n\nA theorem with with a definition that is (syntactically) `:= rfl` is implicitly marked `@[defeq]`.\nTo avoid this behavior, write `:= (rfl)` instead.\n\nThe attribute should be given before a `@[simp]` attribute to have effect.\n\nWhen using the module system, an exported theorem can only be `@[defeq]` if all definitions that\nneed to be unfolded to prove the theorem are exported and exposed.\n", 547, 547);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn___closed__6____x40_Lean_DefEqAttrib___hyg_456_;
x_3 = l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(47u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = lean_unsigned_to_nat(65u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(25u);
x_2 = l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = lean_unsigned_to_nat(62u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_unsigned_to_nat(62u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(19u);
x_4 = l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5;
x_2 = l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn___closed__6____x40_Lean_DefEqAttrib___hyg_456_;
x_3 = l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refl", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0;
x_2 = l_Lean_validateDefEqAttr___lam__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rfl", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("symm", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4;
x_2 = l_Lean_validateDefEqAttr___lam__1___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_defeqAttr;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_validateDefEqAttr___lam__1___closed__1;
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1;
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Lean_Expr_isAppOfArity(x_2, x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3;
x_19 = l_Lean_Expr_isAppOfArity(x_2, x_18, x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5;
x_21 = lean_unsigned_to_nat(4u);
x_22 = l_Lean_Expr_isAppOfArity(x_2, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_24 = l_Lean_Expr_isConst(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_st_ref_get(x_3, x_4);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__6;
x_32 = l_Lean_Expr_constName_x21(x_23);
lean_dec(x_23);
x_33 = l_Lean_TagAttribute_hasTag(x_31, x_30, x_32);
x_34 = lean_box(x_33);
lean_ctor_set(x_27, 0, x_34);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__6;
x_39 = l_Lean_Expr_constName_x21(x_23);
lean_dec(x_23);
x_40 = l_Lean_TagAttribute_hasTag(x_38, x_37, x_39);
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
}
else
{
lean_object* x_43; 
x_43 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_2 = x_43;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_45 = lean_box(x_12);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
x_47 = lean_box(x_12);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_4);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 5);
lean_dec(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_15, x_13, x_2);
x_17 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7;
lean_ctor_set(x_10, 5, x_17);
lean_ctor_set(x_10, 0, x_16);
x_18 = lean_st_ref_set(x_7, x_10, x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_5, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_dec(x_24);
x_25 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4;
lean_ctor_set(x_21, 1, x_25);
x_26 = lean_st_ref_set(x_5, x_21, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 2);
x_35 = lean_ctor_get(x_21, 3);
x_36 = lean_ctor_get(x_21, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_37 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4;
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
x_39 = lean_st_ref_set(x_5, x_38, x_22);
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
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
x_46 = lean_ctor_get(x_10, 2);
x_47 = lean_ctor_get(x_10, 3);
x_48 = lean_ctor_get(x_10, 4);
x_49 = lean_ctor_get(x_10, 6);
x_50 = lean_ctor_get(x_10, 7);
x_51 = lean_ctor_get(x_10, 8);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_dec(x_1);
x_53 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_52, x_44, x_2);
x_54 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7;
x_55 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_45);
lean_ctor_set(x_55, 2, x_46);
lean_ctor_set(x_55, 3, x_47);
lean_ctor_set(x_55, 4, x_48);
lean_ctor_set(x_55, 5, x_54);
lean_ctor_set(x_55, 6, x_49);
lean_ctor_set(x_55, 7, x_50);
lean_ctor_set(x_55, 8, x_51);
x_56 = lean_st_ref_set(x_7, x_55, x_11);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_st_ref_take(x_5, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 4);
lean_inc(x_64);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 lean_ctor_release(x_59, 3);
 lean_ctor_release(x_59, 4);
 x_65 = x_59;
} else {
 lean_dec_ref(x_59);
 x_65 = lean_box(0);
}
x_66 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4;
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 5, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_62);
lean_ctor_set(x_67, 3, x_63);
lean_ctor_set(x_67, 4, x_64);
x_68 = lean_st_ref_set(x_5, x_67, x_60);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid attribute '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', declaration ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" is not from the present async context ", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__7;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("some (", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__10;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__13;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
lean_inc(x_2);
x_11 = l_Lean_Environment_asyncMayContain(x_1, x_2);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__1;
x_18 = l_Lean_MessageData_ofName(x_16);
lean_ctor_set_tag(x_3, 7);
lean_ctor_set(x_3, 1, x_18);
lean_ctor_set(x_3, 0, x_17);
x_19 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__3;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_MessageData_ofConstName(x_2, x_11);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__5;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_31 = l_Lean_Environment_asyncPrefix_x3f(x_1);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__8;
x_25 = x_32;
goto block_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__11;
x_35 = l_Lean_MessageData_ofName(x_33);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__14;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_25 = x_38;
goto block_30;
}
block_30:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_validateDefEqAttr___lam__0___closed__5;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_28, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_29;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_57; 
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
lean_dec(x_3);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__1;
x_43 = l_Lean_MessageData_ofName(x_41);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__3;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_MessageData_ofConstName(x_2, x_11);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__5;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_57 = l_Lean_Environment_asyncPrefix_x3f(x_1);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__8;
x_51 = x_58;
goto block_56;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__11;
x_61 = l_Lean_MessageData_ofName(x_59);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__14;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_51 = x_64;
goto block_56;
}
block_56:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_validateDefEqAttr___lam__0___closed__5;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_54, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_55;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_box(0);
x_66 = lean_apply_6(x_4, x_65, x_6, x_7, x_8, x_9, x_10);
return x_66;
}
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" is in an imported module", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Environment_getModuleIdxFor_x3f(x_12, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_8);
x_15 = lean_box(0);
x_16 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1(x_12, x_2, x_1, x_13, x_15, x_3, x_4, x_5, x_6, x_11);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__1;
x_24 = l_Lean_MessageData_ofName(x_21);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_23);
x_25 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__3;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_25);
lean_ctor_set(x_8, 0, x_1);
x_26 = lean_unbox(x_22);
x_27 = l_Lean_MessageData_ofConstName(x_2, x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__1;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_30, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__1;
x_37 = l_Lean_MessageData_ofName(x_34);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__3;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_39);
lean_ctor_set(x_8, 0, x_38);
x_40 = lean_unbox(x_35);
x_41 = l_Lean_MessageData_ofConstName(x_2, x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__1;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_44, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_8);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_2);
lean_inc(x_1);
x_49 = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(x_49, 0, x_1);
lean_closure_set(x_49, 1, x_2);
x_50 = l_Lean_Environment_getModuleIdxFor_x3f(x_48, x_2);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1(x_48, x_2, x_1, x_49, x_51, x_3, x_4, x_5, x_6, x_47);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_54 = x_1;
} else {
 lean_dec_ref(x_1);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__1;
x_59 = l_Lean_MessageData_ofName(x_56);
if (lean_is_scalar(x_54)) {
 x_60 = lean_alloc_ctor(7, 2, 0);
} else {
 x_60 = x_54;
 lean_ctor_set_tag(x_60, 7);
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__3;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_unbox(x_57);
x_64 = l_Lean_MessageData_ofConstName(x_2, x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__1;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_67, x_3, x_4, x_5, x_6, x_47);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_68;
}
}
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsolvedGoals", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("synthPlaceholder", 16, 16);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__0;
x_7 = lean_string_dec_eq(x_5, x_6);
if (x_7 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
case 1:
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_4, 1);
x_11 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__1;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__2;
x_14 = lean_string_dec_eq(x_10, x_13);
if (x_14 == 0)
{
return x_1;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__3;
x_16 = lean_string_dec_eq(x_9, x_15);
if (x_16 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__4;
x_18 = lean_string_dec_eq(x_9, x_17);
if (x_18 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
else
{
return x_1;
}
}
default: 
{
return x_1;
}
}
}
else
{
return x_1;
}
}
}
static lean_object* _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_142; uint8_t x_159; uint8_t x_160; 
x_132 = lean_box(2);
x_159 = lean_unbox(x_132);
x_160 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_3, x_159);
if (x_160 == 0)
{
x_142 = x_160;
goto block_158;
}
else
{
uint8_t x_161; 
lean_inc(x_2);
x_161 = l_Lean_MessageData_hasSyntheticSorry(x_2);
x_142 = x_161;
goto block_158;
}
block_80:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_st_ref_take(x_18, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_ctor_get(x_17, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 7);
lean_inc(x_25);
lean_dec(x_17);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_22, 6);
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_16);
lean_ctor_set(x_29, 3, x_14);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_29, sizeof(void*)*5 + 2, x_4);
x_30 = l_Lean_MessageLog_add(x_29, x_27);
lean_ctor_set(x_22, 6, x_30);
x_31 = lean_st_ref_set(x_18, x_22, x_23);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
x_40 = lean_ctor_get(x_22, 2);
x_41 = lean_ctor_get(x_22, 3);
x_42 = lean_ctor_get(x_22, 4);
x_43 = lean_ctor_get(x_22, 5);
x_44 = lean_ctor_get(x_22, 6);
x_45 = lean_ctor_get(x_22, 7);
x_46 = lean_ctor_get(x_22, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
lean_ctor_set(x_20, 1, x_25);
lean_ctor_set(x_20, 0, x_24);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_10);
x_48 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_48, 0, x_12);
lean_ctor_set(x_48, 1, x_11);
lean_ctor_set(x_48, 2, x_16);
lean_ctor_set(x_48, 3, x_14);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_48, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_48, sizeof(void*)*5 + 2, x_4);
x_49 = l_Lean_MessageLog_add(x_48, x_44);
x_50 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_39);
lean_ctor_set(x_50, 2, x_40);
lean_ctor_set(x_50, 3, x_41);
lean_ctor_set(x_50, 4, x_42);
lean_ctor_set(x_50, 5, x_43);
lean_ctor_set(x_50, 6, x_49);
lean_ctor_set(x_50, 7, x_45);
lean_ctor_set(x_50, 8, x_46);
x_51 = lean_st_ref_set(x_18, x_50, x_23);
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
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_56 = lean_ctor_get(x_20, 0);
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_20);
x_58 = lean_ctor_get(x_17, 6);
lean_inc(x_58);
x_59 = lean_ctor_get(x_17, 7);
lean_inc(x_59);
lean_dec(x_17);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_56, 3);
lean_inc(x_63);
x_64 = lean_ctor_get(x_56, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_56, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_56, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_56, 7);
lean_inc(x_67);
x_68 = lean_ctor_get(x_56, 8);
lean_inc(x_68);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 lean_ctor_release(x_56, 2);
 lean_ctor_release(x_56, 3);
 lean_ctor_release(x_56, 4);
 lean_ctor_release(x_56, 5);
 lean_ctor_release(x_56, 6);
 lean_ctor_release(x_56, 7);
 lean_ctor_release(x_56, 8);
 x_69 = x_56;
} else {
 lean_dec_ref(x_56);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_58);
lean_ctor_set(x_70, 1, x_59);
x_71 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_10);
x_72 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_72, 0, x_12);
lean_ctor_set(x_72, 1, x_11);
lean_ctor_set(x_72, 2, x_16);
lean_ctor_set(x_72, 3, x_14);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_72, sizeof(void*)*5 + 1, x_13);
lean_ctor_set_uint8(x_72, sizeof(void*)*5 + 2, x_4);
x_73 = l_Lean_MessageLog_add(x_72, x_66);
if (lean_is_scalar(x_69)) {
 x_74 = lean_alloc_ctor(0, 9, 0);
} else {
 x_74 = x_69;
}
lean_ctor_set(x_74, 0, x_60);
lean_ctor_set(x_74, 1, x_61);
lean_ctor_set(x_74, 2, x_62);
lean_ctor_set(x_74, 3, x_63);
lean_ctor_set(x_74, 4, x_64);
lean_ctor_set(x_74, 5, x_65);
lean_ctor_set(x_74, 6, x_73);
lean_ctor_set(x_74, 7, x_67);
lean_ctor_set(x_74, 8, x_68);
x_75 = lean_st_ref_set(x_18, x_74, x_57);
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
block_108:
{
lean_object* x_89; uint8_t x_90; 
x_89 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_5, x_6, x_7, x_8, x_9);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_83);
x_93 = l_Lean_FileMap_toPosition(x_83, x_85);
lean_dec(x_85);
x_94 = l_Lean_FileMap_toPosition(x_83, x_88);
lean_dec(x_88);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = l_Lean_validateDefEqAttr___lam__0___closed__4;
if (x_86 == 0)
{
lean_free_object(x_89);
lean_dec(x_81);
x_10 = x_91;
x_11 = x_93;
x_12 = x_82;
x_13 = x_84;
x_14 = x_96;
x_15 = x_87;
x_16 = x_95;
x_17 = x_7;
x_18 = x_8;
x_19 = x_92;
goto block_80;
}
else
{
uint8_t x_97; 
lean_inc(x_91);
x_97 = l_Lean_MessageData_hasTag(x_81, x_91);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_82);
lean_dec(x_7);
x_98 = lean_box(0);
lean_ctor_set(x_89, 0, x_98);
return x_89;
}
else
{
lean_free_object(x_89);
x_10 = x_91;
x_11 = x_93;
x_12 = x_82;
x_13 = x_84;
x_14 = x_96;
x_15 = x_87;
x_16 = x_95;
x_17 = x_7;
x_18 = x_8;
x_19 = x_92;
goto block_80;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_89, 0);
x_100 = lean_ctor_get(x_89, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_89);
lean_inc(x_83);
x_101 = l_Lean_FileMap_toPosition(x_83, x_85);
lean_dec(x_85);
x_102 = l_Lean_FileMap_toPosition(x_83, x_88);
lean_dec(x_88);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = l_Lean_validateDefEqAttr___lam__0___closed__4;
if (x_86 == 0)
{
lean_dec(x_81);
x_10 = x_99;
x_11 = x_101;
x_12 = x_82;
x_13 = x_84;
x_14 = x_104;
x_15 = x_87;
x_16 = x_103;
x_17 = x_7;
x_18 = x_8;
x_19 = x_100;
goto block_80;
}
else
{
uint8_t x_105; 
lean_inc(x_99);
x_105 = l_Lean_MessageData_hasTag(x_81, x_99);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_99);
lean_dec(x_82);
lean_dec(x_7);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_100);
return x_107;
}
else
{
x_10 = x_99;
x_11 = x_101;
x_12 = x_82;
x_13 = x_84;
x_14 = x_104;
x_15 = x_87;
x_16 = x_103;
x_17 = x_7;
x_18 = x_8;
x_19 = x_100;
goto block_80;
}
}
}
}
block_119:
{
lean_object* x_117; 
x_117 = l_Lean_Syntax_getTailPos_x3f(x_115, x_113);
lean_dec(x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_inc(x_116);
x_81 = x_109;
x_82 = x_110;
x_83 = x_111;
x_84 = x_112;
x_85 = x_116;
x_86 = x_114;
x_87 = x_113;
x_88 = x_116;
goto block_108;
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec(x_117);
x_81 = x_109;
x_82 = x_110;
x_83 = x_111;
x_84 = x_112;
x_85 = x_116;
x_86 = x_114;
x_87 = x_113;
x_88 = x_118;
goto block_108;
}
}
block_131:
{
lean_object* x_127; lean_object* x_128; 
x_127 = l_Lean_replaceRef(x_1, x_121);
lean_dec(x_121);
x_128 = l_Lean_Syntax_getPos_x3f(x_127, x_125);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_unsigned_to_nat(0u);
x_109 = x_120;
x_110 = x_122;
x_111 = x_123;
x_112 = x_126;
x_113 = x_125;
x_114 = x_124;
x_115 = x_127;
x_116 = x_129;
goto block_119;
}
else
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_109 = x_120;
x_110 = x_122;
x_111 = x_123;
x_112 = x_126;
x_113 = x_125;
x_114 = x_124;
x_115 = x_127;
x_116 = x_130;
goto block_119;
}
}
block_141:
{
if (x_139 == 0)
{
x_120 = x_136;
x_121 = x_133;
x_122 = x_134;
x_123 = x_135;
x_124 = x_137;
x_125 = x_138;
x_126 = x_3;
goto block_131;
}
else
{
uint8_t x_140; 
x_140 = lean_unbox(x_132);
x_120 = x_136;
x_121 = x_133;
x_122 = x_134;
x_123 = x_135;
x_124 = x_137;
x_125 = x_138;
x_126 = x_140;
goto block_131;
}
}
block_158:
{
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_153; 
x_143 = lean_ctor_get(x_7, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_7, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_7, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_7, 5);
lean_inc(x_146);
x_147 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_148 = lean_box(x_142);
x_149 = lean_box(x_147);
x_150 = lean_alloc_closure((void*)(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(x_150, 0, x_148);
lean_closure_set(x_150, 1, x_149);
x_151 = lean_box(1);
x_152 = lean_unbox(x_151);
x_153 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_3, x_152);
if (x_153 == 0)
{
lean_dec(x_145);
x_133 = x_146;
x_134 = x_143;
x_135 = x_144;
x_136 = x_150;
x_137 = x_147;
x_138 = x_142;
x_139 = x_153;
goto block_141;
}
else
{
lean_object* x_154; uint8_t x_155; 
x_154 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___closed__0;
x_155 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_145, x_154);
lean_dec(x_145);
x_133 = x_146;
x_134 = x_143;
x_135 = x_144;
x_136 = x_150;
x_137 = x_147;
x_138 = x_142;
x_139 = x_155;
goto block_141;
}
}
else
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_7);
lean_dec(x_2);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_9);
return x_157;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
x_10 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_inferDefEqAttr_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_box(2);
x_8 = lean_box(0);
x_9 = lean_unbox(x_7);
x_10 = lean_unbox(x_8);
x_11 = l_Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 5);
lean_dec(x_13);
x_14 = l_Lean_Environment_setExporting(x_12, x_2);
lean_ctor_set(x_9, 5, x_3);
lean_ctor_set(x_9, 0, x_14);
x_15 = lean_st_ref_set(x_1, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_dec(x_21);
lean_ctor_set(x_18, 1, x_5);
x_22 = lean_st_ref_set(x_4, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
x_32 = lean_ctor_get(x_18, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_5);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
lean_ctor_set(x_33, 4, x_32);
x_34 = lean_st_ref_set(x_4, x_33, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_39 = lean_ctor_get(x_9, 0);
x_40 = lean_ctor_get(x_9, 1);
x_41 = lean_ctor_get(x_9, 2);
x_42 = lean_ctor_get(x_9, 3);
x_43 = lean_ctor_get(x_9, 4);
x_44 = lean_ctor_get(x_9, 6);
x_45 = lean_ctor_get(x_9, 7);
x_46 = lean_ctor_get(x_9, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_9);
x_47 = l_Lean_Environment_setExporting(x_39, x_2);
x_48 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
lean_ctor_set(x_48, 2, x_41);
lean_ctor_set(x_48, 3, x_42);
lean_ctor_set(x_48, 4, x_43);
lean_ctor_set(x_48, 5, x_3);
lean_ctor_set(x_48, 6, x_44);
lean_ctor_set(x_48, 7, x_45);
lean_ctor_set(x_48, 8, x_46);
x_49 = lean_st_ref_set(x_1, x_48, x_10);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_take(x_4, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 5, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_5);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_56);
lean_ctor_set(x_59, 4, x_57);
x_60 = lean_st_ref_set(x_4, x_59, x_53);
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
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Theorem ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_inferDefEqAttr___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" has a `rfl`-proof and was thus inferred to be `@[defeq]`, but validating that attribute failed:", 96, 96);
return x_1;
}
}
static lean_object* _init_l_Lean_inferDefEqAttr___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_inferDefEqAttr___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_150; 
lean_inc(x_1);
x_150 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_box(0);
x_154 = lean_unbox(x_153);
lean_inc(x_151);
x_155 = l_Lean_ConstantInfo_value_x3f(x_151, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_dec(x_151);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = x_152;
goto block_10;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Lean_ConstantInfo_type(x_151);
lean_dec(x_151);
x_158 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg(x_157, x_156, x_5, x_152);
lean_dec(x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unbox(x_159);
if (x_160 == 0)
{
lean_object* x_161; 
lean_dec(x_159);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_7 = x_161;
goto block_10;
}
else
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
lean_dec(x_158);
x_163 = l_Lean_isPrivateName(x_1);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = lean_unbox(x_159);
lean_dec(x_159);
lean_inc(x_3);
lean_inc(x_5);
x_50 = x_5;
x_51 = x_2;
x_52 = x_4;
x_53 = x_3;
x_54 = x_162;
x_55 = x_164;
goto block_149;
}
else
{
uint8_t x_165; 
lean_dec(x_159);
x_165 = lean_unbox(x_153);
lean_inc(x_3);
lean_inc(x_5);
x_50 = x_5;
x_51 = x_2;
x_52 = x_4;
x_53 = x_3;
x_54 = x_162;
x_55 = x_165;
goto block_149;
}
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = !lean_is_exclusive(x_150);
if (x_166 == 0)
{
return x_150;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_150, 0);
x_168 = lean_ctor_get(x_150, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_150);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__6;
x_17 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0(x_16, x_1, x_12, x_14, x_13, x_11, x_15);
return x_17;
}
block_39:
{
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_27 = l_Lean_inferDefEqAttr___lam__1___closed__1;
lean_inc(x_1);
x_28 = l_Lean_MessageData_ofName(x_1);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_inferDefEqAttr___lam__1___closed__3;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Exception_toMessageData(x_25);
x_33 = l_Lean_indentD(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_validateDefEqAttr___lam__0___closed__5;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_22);
x_37 = l_Lean_logError___at___Lean_inferDefEqAttr_spec__1(x_36, x_20, x_24, x_22, x_19, x_21);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_11 = x_19;
x_12 = x_20;
x_13 = x_22;
x_14 = x_24;
x_15 = x_38;
goto block_18;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_1);
return x_23;
}
}
block_49:
{
lean_object* x_46; uint8_t x_47; 
lean_inc(x_45);
lean_inc(x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Exception_isInterrupt(x_44);
if (x_47 == 0)
{
uint8_t x_48; 
x_48 = l_Lean_Exception_isRuntime(x_44);
x_19 = x_40;
x_20 = x_41;
x_21 = x_45;
x_22 = x_42;
x_23 = x_46;
x_24 = x_43;
x_25 = x_44;
x_26 = x_48;
goto block_39;
}
else
{
x_19 = x_40;
x_20 = x_41;
x_21 = x_45;
x_22 = x_42;
x_23 = x_46;
x_24 = x_43;
x_25 = x_44;
x_26 = x_47;
goto block_39;
}
}
block_149:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_st_ref_get(x_50, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_take(x_50, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_ctor_get(x_60, 5);
lean_dec(x_64);
x_65 = l_Lean_Environment_setExporting(x_63, x_55);
x_66 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7;
lean_ctor_set(x_60, 5, x_66);
lean_ctor_set(x_60, 0, x_65);
x_67 = lean_st_ref_set(x_50, x_60, x_61);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_st_ref_take(x_53, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_70, 1);
lean_dec(x_73);
x_74 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4;
lean_ctor_set(x_70, 1, x_74);
x_75 = lean_st_ref_set(x_53, x_70, x_71);
x_76 = lean_ctor_get(x_57, 0);
lean_inc(x_76);
lean_dec(x_57);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get_uint8(x_76, sizeof(void*)*8);
lean_dec(x_76);
lean_inc(x_50);
lean_inc(x_52);
lean_inc(x_1);
x_79 = l_Lean_validateDefEqAttr(x_1, x_52, x_50, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_80);
x_83 = l_Lean_inferDefEqAttr___lam__0(x_5, x_78, x_66, x_3, x_74, x_82, x_81);
lean_dec(x_82);
lean_dec(x_3);
lean_dec(x_5);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_11 = x_50;
x_12 = x_51;
x_13 = x_52;
x_14 = x_53;
x_15 = x_84;
goto block_18;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_box(0);
x_88 = l_Lean_inferDefEqAttr___lam__0(x_5, x_78, x_66, x_3, x_74, x_87, x_86);
lean_dec(x_3);
lean_dec(x_5);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_40 = x_50;
x_41 = x_51;
x_42 = x_52;
x_43 = x_53;
x_44 = x_85;
x_45 = x_89;
goto block_49;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_90 = lean_ctor_get(x_70, 0);
x_91 = lean_ctor_get(x_70, 2);
x_92 = lean_ctor_get(x_70, 3);
x_93 = lean_ctor_get(x_70, 4);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_70);
x_94 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4;
x_95 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_91);
lean_ctor_set(x_95, 3, x_92);
lean_ctor_set(x_95, 4, x_93);
x_96 = lean_st_ref_set(x_53, x_95, x_71);
x_97 = lean_ctor_get(x_57, 0);
lean_inc(x_97);
lean_dec(x_57);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get_uint8(x_97, sizeof(void*)*8);
lean_dec(x_97);
lean_inc(x_50);
lean_inc(x_52);
lean_inc(x_1);
x_100 = l_Lean_validateDefEqAttr(x_1, x_52, x_50, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_101);
x_104 = l_Lean_inferDefEqAttr___lam__0(x_5, x_99, x_66, x_3, x_94, x_103, x_102);
lean_dec(x_103);
lean_dec(x_3);
lean_dec(x_5);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_11 = x_50;
x_12 = x_51;
x_13 = x_52;
x_14 = x_53;
x_15 = x_105;
goto block_18;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_100, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_100, 1);
lean_inc(x_107);
lean_dec(x_100);
x_108 = lean_box(0);
x_109 = l_Lean_inferDefEqAttr___lam__0(x_5, x_99, x_66, x_3, x_94, x_108, x_107);
lean_dec(x_3);
lean_dec(x_5);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_40 = x_50;
x_41 = x_51;
x_42 = x_52;
x_43 = x_53;
x_44 = x_106;
x_45 = x_110;
goto block_49;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; 
x_111 = lean_ctor_get(x_60, 0);
x_112 = lean_ctor_get(x_60, 1);
x_113 = lean_ctor_get(x_60, 2);
x_114 = lean_ctor_get(x_60, 3);
x_115 = lean_ctor_get(x_60, 4);
x_116 = lean_ctor_get(x_60, 6);
x_117 = lean_ctor_get(x_60, 7);
x_118 = lean_ctor_get(x_60, 8);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_60);
x_119 = l_Lean_Environment_setExporting(x_111, x_55);
x_120 = l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7;
x_121 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_112);
lean_ctor_set(x_121, 2, x_113);
lean_ctor_set(x_121, 3, x_114);
lean_ctor_set(x_121, 4, x_115);
lean_ctor_set(x_121, 5, x_120);
lean_ctor_set(x_121, 6, x_116);
lean_ctor_set(x_121, 7, x_117);
lean_ctor_set(x_121, 8, x_118);
x_122 = lean_st_ref_set(x_50, x_121, x_61);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_st_ref_take(x_53, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_125, 3);
lean_inc(x_129);
x_130 = lean_ctor_get(x_125, 4);
lean_inc(x_130);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4;
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 5, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_127);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_128);
lean_ctor_set(x_133, 3, x_129);
lean_ctor_set(x_133, 4, x_130);
x_134 = lean_st_ref_set(x_53, x_133, x_126);
x_135 = lean_ctor_get(x_57, 0);
lean_inc(x_135);
lean_dec(x_57);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get_uint8(x_135, sizeof(void*)*8);
lean_dec(x_135);
lean_inc(x_50);
lean_inc(x_52);
lean_inc(x_1);
x_138 = l_Lean_validateDefEqAttr(x_1, x_52, x_50, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_139);
x_142 = l_Lean_inferDefEqAttr___lam__0(x_5, x_137, x_120, x_3, x_132, x_141, x_140);
lean_dec(x_141);
lean_dec(x_3);
lean_dec(x_5);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_11 = x_50;
x_12 = x_51;
x_13 = x_52;
x_14 = x_53;
x_15 = x_143;
goto block_18;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 1);
lean_inc(x_145);
lean_dec(x_138);
x_146 = lean_box(0);
x_147 = l_Lean_inferDefEqAttr___lam__0(x_5, x_137, x_120, x_3, x_132, x_146, x_145);
lean_dec(x_3);
lean_dec(x_5);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_40 = x_50;
x_41 = x_51;
x_42 = x_52;
x_43 = x_53;
x_44 = x_144;
x_45 = x_148;
goto block_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_inferDefEqAttr___lam__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0(x_4, x_5, x_3);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___Lean_inferDefEqAttr_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logError___at___Lean_inferDefEqAttr_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_inferDefEqAttr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_inferDefEqAttr___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DefEqAttrib(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0 = _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__0);
l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1 = _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__1);
l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2 = _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__2);
l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3 = _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__3();
l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4 = _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__4();
l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__5 = _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__5();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__5);
l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__6 = _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__6();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__6);
l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7 = _init_l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isDefEqCareful___closed__7);
l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__0 = _init_l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__0);
l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__1 = _init_l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__1);
l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__2 = _init_l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__2);
l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__3 = _init_l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__3);
l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4 = _init_l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_withoutExporting___at___Lean_validateDefEqAttr_spec__0___redArg___closed__4);
l_Lean_validateDefEqAttr___lam__0___closed__0 = _init_l_Lean_validateDefEqAttr___lam__0___closed__0();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__0___closed__0);
l_Lean_validateDefEqAttr___lam__0___closed__1 = _init_l_Lean_validateDefEqAttr___lam__0___closed__1();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__0___closed__1);
l_Lean_validateDefEqAttr___lam__0___closed__2 = _init_l_Lean_validateDefEqAttr___lam__0___closed__2();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__0___closed__2);
l_Lean_validateDefEqAttr___lam__0___closed__3 = _init_l_Lean_validateDefEqAttr___lam__0___closed__3();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__0___closed__3);
l_Lean_validateDefEqAttr___lam__0___closed__4 = _init_l_Lean_validateDefEqAttr___lam__0___closed__4();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__0___closed__4);
l_Lean_validateDefEqAttr___lam__0___closed__5 = _init_l_Lean_validateDefEqAttr___lam__0___closed__5();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__0___closed__5);
l_Lean_validateDefEqAttr___lam__0___closed__6 = _init_l_Lean_validateDefEqAttr___lam__0___closed__6();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__0___closed__6);
l_Lean_validateDefEqAttr___lam__0___closed__7 = _init_l_Lean_validateDefEqAttr___lam__0___closed__7();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__0___closed__7);
l_Lean_validateDefEqAttr___lam__0___closed__8 = _init_l_Lean_validateDefEqAttr___lam__0___closed__8();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__0___closed__8);
l_Lean_validateDefEqAttr___lam__1___closed__0 = _init_l_Lean_validateDefEqAttr___lam__1___closed__0();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__1___closed__0);
l_Lean_validateDefEqAttr___lam__1___closed__1 = _init_l_Lean_validateDefEqAttr___lam__1___closed__1();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__1___closed__1);
l_Lean_validateDefEqAttr___lam__1___closed__2 = _init_l_Lean_validateDefEqAttr___lam__1___closed__2();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__1___closed__2);
l_Lean_validateDefEqAttr___lam__1___closed__3 = _init_l_Lean_validateDefEqAttr___lam__1___closed__3();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__1___closed__3);
l_Lean_validateDefEqAttr___lam__1___closed__4 = _init_l_Lean_validateDefEqAttr___lam__1___closed__4();
lean_mark_persistent(l_Lean_validateDefEqAttr___lam__1___closed__4);
l_Lean_validateDefEqAttr___closed__0 = _init_l_Lean_validateDefEqAttr___closed__0();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__0);
l_Lean_validateDefEqAttr___closed__1 = _init_l_Lean_validateDefEqAttr___closed__1();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__1);
l_Lean_validateDefEqAttr___closed__2 = _init_l_Lean_validateDefEqAttr___closed__2();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__2);
l_Lean_validateDefEqAttr___closed__3 = _init_l_Lean_validateDefEqAttr___closed__3();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__3);
l_Lean_validateDefEqAttr___closed__4 = _init_l_Lean_validateDefEqAttr___closed__4();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__4);
l_Lean_validateDefEqAttr___closed__5 = _init_l_Lean_validateDefEqAttr___closed__5();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__5);
l_Lean_validateDefEqAttr___closed__6 = _init_l_Lean_validateDefEqAttr___closed__6();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__6);
l_Lean_validateDefEqAttr___closed__7 = _init_l_Lean_validateDefEqAttr___closed__7();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__7);
l_Lean_validateDefEqAttr___closed__8 = _init_l_Lean_validateDefEqAttr___closed__8();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__8);
l_Lean_validateDefEqAttr___closed__9 = _init_l_Lean_validateDefEqAttr___closed__9();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__9);
l_Lean_validateDefEqAttr___closed__10 = _init_l_Lean_validateDefEqAttr___closed__10();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__10);
l_Lean_validateDefEqAttr___closed__11 = _init_l_Lean_validateDefEqAttr___closed__11();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__11);
l_Lean_validateDefEqAttr___closed__12 = _init_l_Lean_validateDefEqAttr___closed__12();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__12);
l_Lean_validateDefEqAttr___closed__13 = _init_l_Lean_validateDefEqAttr___closed__13();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__13);
l_Lean_validateDefEqAttr___closed__14 = _init_l_Lean_validateDefEqAttr___closed__14();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__14);
l_Lean_validateDefEqAttr___closed__15 = _init_l_Lean_validateDefEqAttr___closed__15();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__15);
l_Lean_validateDefEqAttr___closed__16 = _init_l_Lean_validateDefEqAttr___closed__16();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__16);
l_Lean_validateDefEqAttr___closed__17 = _init_l_Lean_validateDefEqAttr___closed__17();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__17);
l_Lean_validateDefEqAttr___closed__18 = _init_l_Lean_validateDefEqAttr___closed__18();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__18);
l_Lean_validateDefEqAttr___closed__19 = _init_l_Lean_validateDefEqAttr___closed__19();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__19);
l_Lean_validateDefEqAttr___closed__20 = _init_l_Lean_validateDefEqAttr___closed__20();
l_Lean_validateDefEqAttr___closed__21 = _init_l_Lean_validateDefEqAttr___closed__21();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__21);
l_Lean_validateDefEqAttr___closed__22 = _init_l_Lean_validateDefEqAttr___closed__22();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__22);
l_Lean_validateDefEqAttr___closed__23 = _init_l_Lean_validateDefEqAttr___closed__23();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__23);
l_Lean_validateDefEqAttr___closed__24 = _init_l_Lean_validateDefEqAttr___closed__24();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__24);
l_Lean_validateDefEqAttr___closed__25 = _init_l_Lean_validateDefEqAttr___closed__25();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__25);
l_Lean_validateDefEqAttr___closed__26 = _init_l_Lean_validateDefEqAttr___closed__26();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__26);
l_Lean_validateDefEqAttr___closed__27 = _init_l_Lean_validateDefEqAttr___closed__27();
l_Lean_validateDefEqAttr___closed__28 = _init_l_Lean_validateDefEqAttr___closed__28();
l_Lean_validateDefEqAttr___closed__29 = _init_l_Lean_validateDefEqAttr___closed__29();
l_Lean_validateDefEqAttr___closed__30 = _init_l_Lean_validateDefEqAttr___closed__30();
lean_mark_persistent(l_Lean_validateDefEqAttr___closed__30);
l_Lean_initFn___closed__0____x40_Lean_DefEqAttrib___hyg_456_ = _init_l_Lean_initFn___closed__0____x40_Lean_DefEqAttrib___hyg_456_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_DefEqAttrib___hyg_456_);
l_Lean_initFn___closed__1____x40_Lean_DefEqAttrib___hyg_456_ = _init_l_Lean_initFn___closed__1____x40_Lean_DefEqAttrib___hyg_456_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_DefEqAttrib___hyg_456_);
l_Lean_initFn___closed__2____x40_Lean_DefEqAttrib___hyg_456_ = _init_l_Lean_initFn___closed__2____x40_Lean_DefEqAttrib___hyg_456_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_DefEqAttrib___hyg_456_);
l_Lean_initFn___closed__3____x40_Lean_DefEqAttrib___hyg_456_ = _init_l_Lean_initFn___closed__3____x40_Lean_DefEqAttrib___hyg_456_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_DefEqAttrib___hyg_456_);
l_Lean_initFn___closed__4____x40_Lean_DefEqAttrib___hyg_456_ = _init_l_Lean_initFn___closed__4____x40_Lean_DefEqAttrib___hyg_456_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_DefEqAttrib___hyg_456_);
l_Lean_initFn___closed__5____x40_Lean_DefEqAttrib___hyg_456_ = _init_l_Lean_initFn___closed__5____x40_Lean_DefEqAttrib___hyg_456_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_DefEqAttrib___hyg_456_);
l_Lean_initFn___closed__6____x40_Lean_DefEqAttrib___hyg_456_ = _init_l_Lean_initFn___closed__6____x40_Lean_DefEqAttrib___hyg_456_();
lean_mark_persistent(l_Lean_initFn___closed__6____x40_Lean_DefEqAttrib___hyg_456_);
l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0 = _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0();
lean_mark_persistent(l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1___closed__0);
if (builtin) {res = l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_docString__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0 = _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0();
lean_mark_persistent(l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__0);
l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1 = _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1();
lean_mark_persistent(l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__1);
l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2 = _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2();
lean_mark_persistent(l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__2);
l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3 = _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3();
lean_mark_persistent(l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__3);
l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4 = _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4();
lean_mark_persistent(l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__4);
l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5 = _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5();
lean_mark_persistent(l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__5);
l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6 = _init_l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6();
lean_mark_persistent(l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3___closed__6);
if (builtin) {res = l_Lean_defeqAttr___regBuiltin_Lean_defeqAttr_declRange__3(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_DefEqAttrib___hyg_456_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_defeqAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_defeqAttr);
lean_dec_ref(res);
}l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0 = _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__0);
l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1 = _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__1);
l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2 = _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__2);
l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3 = _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__3);
l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4 = _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__4);
l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5 = _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__5);
l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__6 = _init_l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__6();
lean_mark_persistent(l___private_Lean_DefEqAttrib_0__Lean_isRflProofCore___redArg___closed__6);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__0 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__0();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__0);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__1 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__1();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__1);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__2 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__2();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__2);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__3 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__3();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__3);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__4 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__4();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__4);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__5 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__5();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__5);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__6 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__6();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__6);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__7 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__7();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__7);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__8 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__8();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__8);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__9 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__9();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__9);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__10 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__10();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__10);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__11 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__11();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__11);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__12 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__12();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__12);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__13 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__13();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__13);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__14 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__14();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___lam__1___closed__14);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__0 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__0();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__0);
l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__1 = _init_l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__1();
lean_mark_persistent(l_Lean_TagAttribute_setTag___at___Lean_inferDefEqAttr_spec__0___closed__1);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__0 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__0();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__0);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__1 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__1();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__1);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__2 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__2();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__2);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__3 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__3();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__3);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__4 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__4();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___lam__0___closed__4);
l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___closed__0 = _init_l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___closed__0();
lean_mark_persistent(l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_inferDefEqAttr_spec__1_spec__1_spec__1___closed__0);
l_Lean_inferDefEqAttr___lam__1___closed__0 = _init_l_Lean_inferDefEqAttr___lam__1___closed__0();
lean_mark_persistent(l_Lean_inferDefEqAttr___lam__1___closed__0);
l_Lean_inferDefEqAttr___lam__1___closed__1 = _init_l_Lean_inferDefEqAttr___lam__1___closed__1();
lean_mark_persistent(l_Lean_inferDefEqAttr___lam__1___closed__1);
l_Lean_inferDefEqAttr___lam__1___closed__2 = _init_l_Lean_inferDefEqAttr___lam__1___closed__2();
lean_mark_persistent(l_Lean_inferDefEqAttr___lam__1___closed__2);
l_Lean_inferDefEqAttr___lam__1___closed__3 = _init_l_Lean_inferDefEqAttr___lam__1___closed__3();
lean_mark_persistent(l_Lean_inferDefEqAttr___lam__1___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
