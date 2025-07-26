// Lean compiler output
// Module: Lean.Meta.Eqns
// Imports: Lean.ReservedNameAction Lean.AddDecl Lean.Meta.Basic Lean.Meta.AppBuilder Lean.Meta.Match.MatcherInfo Lean.DefEqAttrib Lean.Meta.LetToHave
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
static lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markAsRecursive___redArg___closed__2;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___Lean_Meta_isEqnReservedNameSuffix_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_5_;
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eqnThmSuffixBasePrefix;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632_(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__10____x40_Lean_Meta_Eqns___hyg_2928_;
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__2___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* l_Lean_Environment_header(lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__0___closed__1____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedEqnsExtState___closed__1;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3;
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__2____x40_Lean_Meta_Eqns___hyg_2928_;
static size_t l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__4;
LEAN_EXPORT uint8_t l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_632_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markAsRecursive___redArg___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__6;
static lean_object* l_Lean_Meta_initFn___lam__1___closed__16____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markAsRecursive___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__21____x40_Lean_Meta_Eqns___hyg_2928_;
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_5_;
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_196__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exceptBoolEmoji___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__8____x40_Lean_Meta_Eqns___hyg_2928_;
static lean_object* l_Lean_Meta_initFn___lam__1___closed__1____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Eqns___hyg_5_;
static lean_object* l_Lean_Meta_generateEagerEqns___closed__2;
extern lean_object* l_Lean_maxRecDepth;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__17____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__3____x40_Lean_Meta_Eqns___hyg_2928_;
LEAN_EXPORT lean_object* l_Lean_Meta_backward_eqns_deepRecursiveSplit;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1;
lean_object* l_Lean_initializing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5_(lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_44_;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3;
static lean_object* l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqn1ThmSuffix___closed__0;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__0;
static lean_object* l_Lean_Meta_initFn___lam__1___closed__18____x40_Lean_Meta_Eqns___hyg_2928_;
static lean_object* l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3;
static lean_object* l_Lean_Meta_instInhabitedEqnsExtState___closed__0;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0;
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_2928____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_registerGetEqnsFn___closed__0;
static lean_object* l_Lean_Meta_generateEagerEqns___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedEqnsExtState;
static lean_object* l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5;
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__3;
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_98_;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__6____x40_Lean_Meta_Eqns___hyg_2928_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Eqns___hyg_2928_(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__2;
static lean_object* l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Eqns___hyg_5_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Eqns___hyg_5_;
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2191_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982_(lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__11____x40_Lean_Meta_Eqns___hyg_2928_;
static lean_object* l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_44_;
lean_object* l_Lean_privateToUserName(lean_object*);
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqUnfoldThmSuffix___closed__0;
lean_object* l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__13____x40_Lean_Meta_Eqns___hyg_2928_;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2928_(lean_object*);
uint8_t l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__5____x40_Lean_Meta_Eqns___hyg_2928_;
static lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lean_Meta_initFn___lam__1___closed__22____x40_Lean_Meta_Eqns___hyg_2928_;
static lean_object* l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_44_;
static lean_object* l_Lean_Meta_generateEagerEqns___closed__1;
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_44_;
lean_object* l_Lean_withoutExporting___at___Lean_Meta_letToHave_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_registerGetEqnsFn___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2;
static lean_object* l_Lean_Meta_initFn___lam__1___closed__20____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_eqnThmSuffixBase;
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_5_;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__15____x40_Lean_Meta_Eqns___hyg_2928_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getEqnsFor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object*);
static lean_object* l_Lean_Meta_markAsRecursive___redArg___closed__0;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getEqnsFor_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eqn1ThmSuffix;
static lean_object* l_Lean_Meta_initFn___lam__1___closed__12____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__9____x40_Lean_Meta_Eqns___hyg_2928_;
static lean_object* l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__2____x40_Lean_Meta_Eqns___hyg_2928_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_recExt;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eqUnfoldThmSuffix;
static lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44_(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isSafeDefinition(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_eqns_nonrecursive;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___closed__0;
static lean_object* l_Lean_Meta_eqnThmSuffixBase___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Eqns___hyg_5_;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_generateEagerEqns_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___closed__0;
static lean_object* l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_eqnsExt;
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_98_;
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldThmSuffix;
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__14____x40_Lean_Meta_Eqns___hyg_2928_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_717_(lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__1___closed__23____x40_Lean_Meta_Eqns___hyg_2928_;
static lean_object* l_Lean_Meta_initFn___lam__1___closed__4____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_5_;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___lam__2___closed__1____x40_Lean_Meta_Eqns___hyg_2928_;
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_982_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generateEagerEqns___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_5_;
static lean_object* l_Lean_Meta_generateEagerEqns___closed__4;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generateEagerEqns___closed__6;
LEAN_EXPORT uint8_t l_String_anyAux___at___Lean_Meta_isEqnReservedNameSuffix_spec__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_generateEagerEqns_spec__0(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Eqns___hyg_5_;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_registerGetEqnsFn___closed__2;
static lean_object* l_Lean_Meta_initFn___lam__1___closed__19____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_632____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldThmSuffix___closed__0;
static lean_object* l_Lean_Meta_initFn___lam__1___closed__7____x40_Lean_Meta_Eqns___hyg_2928_;
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
static lean_object* l_Lean_Meta_declFromEqLikeName___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_eqnAffectingOptions;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_2928_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lean_Meta_generateEagerEqns___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0;
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_44_;
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4;
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backward", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqns", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nonrecursive", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_5_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Eqns___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Create fine-grained equational lemmas even for non-recursive definitions.", 73, 73);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Eqns___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Eqns___hyg_5_;
x_2 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_5_;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Eqns___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Eqns___hyg_5_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Eqns___hyg_5_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_5_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_5_;
x_4 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Eqns___hyg_5_;
x_5 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Eqns___hyg_5_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Eqns___hyg_5_;
x_4 = l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Eqns___hyg_5_;
x_5 = l_Lean_Option_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_196__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("deepRecursiveSplit", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_44_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_5_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_44_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Create equational lemmas for recursive functions like for non-recursive functions. If disabled, match statements in recursive function definitions that do not contain recursive calls do not cause further splits in the equational lemmas. This was the behavior before Lean 4.12, and the purpose of this option is to help migrating old code.", 338, 338);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_44_;
x_2 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_5_;
x_3 = 1;
x_4 = lean_box(x_3);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_44_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_44_;
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_5_;
x_3 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_5_;
x_4 = l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Eqns___hyg_5_;
x_5 = l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Eqns___hyg_5_;
x_6 = l_Lean_Name_mkStr5(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_44_;
x_3 = l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_44_;
x_4 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_44_;
x_5 = l_Lean_Option_register___at___Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ConfigOptions___hyg_196__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_backward_eqns_nonrecursive;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_backward_eqns_deepRecursiveSplit;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_eqnAffectingOptions___closed__0;
x_2 = l_Lean_Meta_eqnAffectingOptions___closed__2;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_eqnAffectingOptions___closed__1;
x_2 = l_Lean_Meta_eqnAffectingOptions___closed__3;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_eqnAffectingOptions___closed__4;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_98_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recExt", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_98_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_98_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_98_;
x_3 = 3;
x_4 = l_Lean_mkTagDeclarationExtension(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_recExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_markAsRecursive___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_markAsRecursive___redArg___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 5);
lean_dec(x_9);
x_10 = l_Lean_Meta_markAsRecursive___redArg___closed__0;
x_11 = l_Lean_TagDeclarationExtension_tag(x_10, x_8, x_1);
x_12 = l_Lean_Meta_markAsRecursive___redArg___closed__3;
lean_ctor_set(x_5, 5, x_12);
lean_ctor_set(x_5, 0, x_11);
x_13 = lean_st_ref_set(x_2, x_5, x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_ctor_get(x_5, 2);
x_23 = lean_ctor_get(x_5, 3);
x_24 = lean_ctor_get(x_5, 4);
x_25 = lean_ctor_get(x_5, 6);
x_26 = lean_ctor_get(x_5, 7);
x_27 = lean_ctor_get(x_5, 8);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_28 = l_Lean_Meta_markAsRecursive___redArg___closed__0;
x_29 = l_Lean_TagDeclarationExtension_tag(x_28, x_20, x_1);
x_30 = l_Lean_Meta_markAsRecursive___redArg___closed__3;
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_21);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_23);
lean_ctor_set(x_31, 4, x_24);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_25);
lean_ctor_set(x_31, 7, x_26);
lean_ctor_set(x_31, 8, x_27);
x_32 = lean_st_ref_set(x_2, x_31, x_6);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_markAsRecursive___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_markAsRecursive___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_markAsRecursive(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_markAsRecursive___redArg___closed__0;
x_9 = l_Lean_TagDeclarationExtension_isTagged(x_8, x_7, x_1);
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_markAsRecursive___redArg___closed__0;
x_15 = l_Lean_TagDeclarationExtension_isTagged(x_14, x_13, x_1);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isRecursiveDefinition___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isRecursiveDefinition___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isRecursiveDefinition(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_eqnThmSuffixBase___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqnThmSuffixBase() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_eqnThmSuffixBase___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqnThmSuffixBasePrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqn1ThmSuffix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_1", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqn1ThmSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_eqn1ThmSuffix___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___Lean_Meta_isEqnReservedNameSuffix_spec__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_5, x_4);
if (x_10 == 0)
{
lean_dec(x_5);
return x_10;
}
else
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get(x_3, x_5);
x_12 = 48;
x_13 = lean_uint32_dec_le(x_12, x_11);
if (x_13 == 0)
{
if (x_13 == 0)
{
x_6 = x_1;
goto block_9;
}
else
{
x_6 = x_2;
goto block_9;
}
}
else
{
uint32_t x_14; uint8_t x_15; 
x_14 = 57;
x_15 = lean_uint32_dec_le(x_11, x_14);
if (x_15 == 0)
{
x_6 = x_1;
goto block_9;
}
else
{
x_6 = x_2;
goto block_9;
}
}
}
block_9:
{
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_string_utf8_next(x_3, x_5);
lean_dec(x_5);
x_5 = x_7;
goto _start;
}
else
{
lean_dec(x_5);
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0;
x_3 = l_String_isPrefixOf(x_2, x_1);
if (x_3 == 0)
{
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_unsigned_to_nat(3u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_1);
lean_inc(x_6);
lean_inc_ref(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Substring_nextn(x_7, x_4, x_5);
lean_dec_ref(x_7);
x_9 = lean_string_utf8_extract(x_1, x_8, x_6);
lean_dec(x_6);
lean_dec(x_8);
lean_dec_ref(x_1);
x_10 = lean_string_utf8_byte_size(x_9);
x_11 = lean_nat_dec_eq(x_10, x_5);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_String_anyAux___at___Lean_Meta_isEqnReservedNameSuffix_spec__0(x_3, x_11, x_9, x_10, x_5);
lean_dec(x_10);
lean_dec_ref(x_9);
if (x_12 == 0)
{
return x_3;
}
else
{
return x_11;
}
}
else
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
x_13 = 0;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___Lean_Meta_isEqnReservedNameSuffix_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = l_String_anyAux___at___Lean_Meta_isEqnReservedNameSuffix_spec__0(x_6, x_7, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_isEqnReservedNameSuffix(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_unfoldThmSuffix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_def", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_unfoldThmSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_unfoldThmSuffix___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqUnfoldThmSuffix___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_unfold", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqUnfoldThmSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_eqUnfoldThmSuffix___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Meta_unfoldThmSuffix___closed__0;
x_6 = lean_string_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Meta_eqUnfoldThmSuffix___closed__0;
x_8 = lean_string_dec_eq(x_1, x_7);
x_2 = x_8;
goto block_4;
}
else
{
x_2 = x_6;
goto block_4;
}
block_4:
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Meta_isEqnReservedNameSuffix(x_1);
return x_3;
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_isEqnLikeSuffix(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_inc_ref(x_6);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_9 = x_5;
} else {
 lean_dec_ref(x_5);
 x_9 = lean_box(0);
}
x_17 = 0;
lean_inc_ref(x_4);
x_18 = l_Lean_Environment_setExporting(x_4, x_17);
lean_inc(x_7);
x_19 = l_Lean_Environment_isSafeDefinition(x_18, x_7);
if (x_19 == 0)
{
x_10 = x_19;
goto block_16;
}
else
{
uint8_t x_20; 
lean_inc(x_7);
lean_inc_ref(x_4);
x_20 = lean_is_matcher(x_4, x_7);
if (x_20 == 0)
{
x_10 = x_19;
goto block_16;
}
else
{
lean_dec(x_9);
lean_dec(x_7);
{
lean_object* _tmp_4 = x_8;
lean_object* _tmp_5 = x_1;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_7);
{
lean_object* _tmp_4 = x_8;
lean_object* _tmp_5 = x_1;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec_ref(x_4);
if (lean_is_scalar(x_9)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_9;
 lean_ctor_set_tag(x_12, 0);
}
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_declFromEqLikeName___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_2);
lean_inc_ref(x_4);
x_5 = l_Lean_Meta_isEqnLikeSuffix(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_3);
x_7 = l_Lean_privateToUserName(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = l_Lean_Meta_declFromEqLikeName___closed__0;
x_13 = l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0___redArg(x_12, x_4, x_11, x_1, x_10, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at___Lean_Meta_declFromEqLikeName_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Environment_header(x_1);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*5 + 4);
lean_dec_ref(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = l_Lean_Name_str___override(x_2, x_3);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
lean_inc_ref(x_1);
x_11 = l_Lean_Environment_setExporting(x_1, x_8);
lean_inc(x_2);
x_12 = l_Lean_Environment_find_x3f(x_11, x_2, x_10);
if (lean_obj_tag(x_12) == 0)
{
goto block_6;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l_Lean_ConstantInfo_hasValue(x_13, x_10);
lean_dec(x_13);
if (x_14 == 0)
{
goto block_6;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_1);
x_15 = l_Lean_Name_str___override(x_2, x_3);
return x_15;
}
}
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Name_str___override(x_2, x_3);
x_5 = l_Lean_mkPrivateName(x_1, x_4);
lean_dec_ref(x_1);
return x_5;
}
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to declare `", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` because `", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has already been declared", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1;
x_7 = l_Lean_MessageData_ofName(x_1);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = 1;
x_12 = l_Lean_MessageData_ofConstName(x_2, x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(x_15, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Name_str___override(x_1, x_2);
x_12 = 1;
lean_inc(x_11);
x_13 = l_Lean_Environment_contains(x_10, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; 
lean_free_object(x_6);
x_15 = l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(x_1, x_11, x_3, x_4, x_9);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_Lean_Name_str___override(x_1, x_2);
x_20 = 1;
lean_inc(x_19);
x_21 = l_Lean_Environment_contains(x_18, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(x_1, x_19, x_3, x_4, x_17);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_eqUnfoldThmSuffix___closed__0;
lean_inc(x_1);
x_6 = l_Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(x_1, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_Meta_unfoldThmSuffix___closed__0;
lean_inc(x_1);
x_9 = l_Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(x_1, x_8, x_2, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Meta_eqn1ThmSuffix___closed__0;
x_12 = l_Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(x_1, x_11, x_2, x_3, x_10);
return x_12;
}
else
{
lean_dec(x_1);
return x_9;
}
}
else
{
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_ensureEqnReservedNamesAvailable(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_632_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_3 = l_Lean_Meta_declFromEqLikeName(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_mkEqLikeNameFor(x_1, x_6, x_7);
x_9 = lean_name_eq(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_632____boxed), 2, 0);
x_3 = l_Lean_registerReservedNamePredicate(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_632____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_632_(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_717_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to register equation getter, this kind of extension can only be registered during initialization", 103, 103);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_registerGetEqnsFn___closed__0;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_initializing(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_Meta_registerGetEqnsFn___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Meta_registerGetEqnsFn___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = l_Lean_Meta_registerGetEqnsFn___closed__2;
x_14 = lean_st_ref_take(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_1);
x_18 = lean_st_ref_set(x_13, x_14, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_st_ref_set(x_13, x_25, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_st_ref_get(x_5, x_6);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = 0;
x_17 = l_Lean_Environment_findAsync_x3f(x_15, x_1, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = x_14;
goto block_11;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_20 = lean_box(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_21);
lean_dec(x_18);
x_22 = lean_task_get_own(x_21);
x_23 = lean_ctor_get(x_22, 2);
lean_inc_ref(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_Meta_isProp(x_23, x_2, x_3, x_4, x_5, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_dec(x_28);
x_29 = 1;
x_30 = lean_box(x_29);
lean_ctor_set(x_24, 0, x_30);
return x_24;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_24, 0);
lean_dec(x_36);
x_37 = lean_box(x_16);
lean_ctor_set(x_24, 0, x_37);
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_box(x_16);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
return x_24;
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = x_14;
goto block_11;
}
}
block_11:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instInhabitedEqnsExtState___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedEqnsExtState___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_982_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Meta_instInhabitedEqnsExtState___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_982_), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = 1;
x_6 = l_Lean_registerEnvExtension___redArg(x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
lean_dec(x_13);
x_14 = lean_box(0);
lean_inc(x_12);
x_15 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_12, x_14);
x_16 = l_Lean_Expr_const___override(x_11, x_15);
x_17 = l_Lean_mkAppN(x_16, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_17);
x_18 = l_Lean_Meta_mkEq(x_17, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = 0;
x_22 = 1;
x_23 = 1;
x_24 = l_Lean_Meta_mkForallFVars(x_3, x_19, x_21, x_22, x_22, x_23, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_27 = l_Lean_Meta_letToHave(x_25, x_5, x_6, x_7, x_8, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_30 = l_Lean_Meta_mkEqRefl(x_17, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Meta_mkLambdaFVars(x_3, x_31, x_21, x_22, x_21, x_22, x_23, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
lean_inc(x_2);
lean_ctor_set(x_1, 2, x_28);
lean_ctor_set(x_1, 0, x_2);
x_36 = lean_box(0);
lean_inc(x_2);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_inc(x_8);
lean_inc_ref(x_7);
x_40 = l_Lean_addDecl(x_39, x_7, x_8, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_inferDefEqAttr(x_2, x_5, x_6, x_7, x_8, x_41);
return x_42;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_40;
}
}
else
{
uint8_t x_43; 
lean_dec(x_28);
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 0);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_33);
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
lean_dec(x_28);
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_30);
if (x_47 == 0)
{
return x_30;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_30, 0);
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_30);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_17);
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_27);
if (x_51 == 0)
{
return x_27;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_27, 0);
x_53 = lean_ctor_get(x_27, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_27);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec_ref(x_17);
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_24);
if (x_55 == 0)
{
return x_24;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_24, 0);
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_24);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec_ref(x_17);
lean_free_object(x_1);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_18);
if (x_59 == 0)
{
return x_18;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
x_61 = lean_ctor_get(x_18, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_18);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_1);
x_65 = lean_box(0);
lean_inc(x_64);
x_66 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_64, x_65);
x_67 = l_Lean_Expr_const___override(x_63, x_66);
x_68 = l_Lean_mkAppN(x_67, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_68);
x_69 = l_Lean_Meta_mkEq(x_68, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = 0;
x_73 = 1;
x_74 = 1;
x_75 = l_Lean_Meta_mkForallFVars(x_3, x_70, x_72, x_73, x_73, x_74, x_5, x_6, x_7, x_8, x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_78 = l_Lean_Meta_letToHave(x_76, x_5, x_6, x_7, x_8, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec_ref(x_78);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_81 = l_Lean_Meta_mkEqRefl(x_68, x_5, x_6, x_7, x_8, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = l_Lean_Meta_mkLambdaFVars(x_3, x_82, x_72, x_73, x_72, x_73, x_74, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
lean_inc(x_2);
x_87 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_87, 0, x_2);
lean_ctor_set(x_87, 1, x_64);
lean_ctor_set(x_87, 2, x_79);
x_88 = lean_box(0);
lean_inc(x_2);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_2);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set(x_90, 2, x_89);
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_90);
lean_inc(x_8);
lean_inc_ref(x_7);
x_92 = l_Lean_addDecl(x_91, x_7, x_8, x_86);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = l_Lean_inferDefEqAttr(x_2, x_5, x_6, x_7, x_8, x_93);
return x_94;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
return x_92;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_79);
lean_dec(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_95 = lean_ctor_get(x_84, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_84, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_97 = x_84;
} else {
 lean_dec_ref(x_84);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_79);
lean_dec(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_99 = lean_ctor_get(x_81, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_81, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_101 = x_81;
} else {
 lean_dec_ref(x_81);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec_ref(x_68);
lean_dec(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_103 = lean_ctor_get(x_78, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_78, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_105 = x_78;
} else {
 lean_dec_ref(x_78);
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
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_68);
lean_dec(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
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
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec_ref(x_68);
lean_dec(x_64);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
x_111 = lean_ctor_get(x_69, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_69, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_113 = x_69;
} else {
 lean_dec_ref(x_69);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed), 9, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
x_11 = 1;
x_12 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_9, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_st_ref_get(x_5, x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_14);
lean_dec(x_12);
x_15 = 0;
lean_inc(x_1);
x_16 = l_Lean_Environment_find_x3f(x_14, x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = x_13;
goto block_10;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = lean_st_ref_get(x_5, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_unfoldThmSuffix___closed__0;
lean_inc(x_1);
x_25 = l_Lean_Meta_mkEqLikeNameFor(x_23, x_1, x_24);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize), 7, 2);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_19);
lean_inc(x_25);
x_27 = l_Lean_Meta_realizeConst(x_1, x_25, x_26, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_16, 0, x_25);
lean_ctor_set(x_27, 0, x_16);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_16, 0, x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_25);
lean_free_object(x_16);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_free_object(x_16);
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = x_13;
goto block_10;
}
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
lean_dec(x_16);
if (lean_obj_tag(x_36) == 1)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_37);
lean_dec_ref(x_36);
x_38 = lean_st_ref_get(x_5, x_13);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec_ref(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc_ref(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_unfoldThmSuffix___closed__0;
lean_inc(x_1);
x_43 = l_Lean_Meta_mkEqLikeNameFor(x_41, x_1, x_42);
lean_inc(x_43);
x_44 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize), 7, 2);
lean_closure_set(x_44, 0, x_43);
lean_closure_set(x_44, 1, x_37);
lean_inc(x_43);
x_45 = l_Lean_Meta_realizeConst(x_1, x_43, x_44, x_2, x_3, x_4, x_5, x_40);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_43);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_52 = x_45;
} else {
 lean_dec_ref(x_45);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_dec(x_36);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_7 = x_13;
goto block_10;
}
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
}
}
static lean_object* _init_l_Lean_Meta_isEqnThm_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_eqnsExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_isEqnThm_x3f___redArg___closed__0;
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_10 = l_Lean_Meta_instInhabitedEqnsExtState;
x_11 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_10, x_8, x_7, x_9);
x_12 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(x_11, x_1);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_isEqnThm_x3f___redArg___closed__0;
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
x_18 = l_Lean_Meta_instInhabitedEqnsExtState;
x_19 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_18, x_16, x_15, x_17);
x_20 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__1___redArg(x_19, x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isEqnThm_x3f___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isEqnThm_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isEqnThm_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_isEqnThm_x3f___redArg___closed__0;
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_10 = l_Lean_Meta_instInhabitedEqnsExtState;
x_11 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_10, x_8, x_7, x_9);
x_12 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0_spec__0___redArg(x_11, x_1);
x_13 = lean_box(x_12);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_16 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_isEqnThm_x3f___redArg___closed__0;
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*3);
x_19 = l_Lean_Meta_instInhabitedEqnsExtState;
x_20 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_19, x_17, x_16, x_18);
x_21 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_containsOnBranch_spec__0_spec__0___redArg(x_20, x_1);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isEqnThm___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_isEqnThm___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isEqnThm(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0___redArg(x_5, x_7, x_1);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_5, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(x_2, x_1, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec_ref(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 5);
lean_dec(x_10);
x_11 = l_Lean_Meta_isEqnThm_x3f___redArg___closed__0;
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
x_14 = l_Lean_EnvExtension_modifyState___redArg(x_11, x_9, x_13, x_12);
x_15 = l_Lean_Meta_markAsRecursive___redArg___closed__3;
lean_ctor_set(x_6, 5, x_15);
lean_ctor_set(x_6, 0, x_14);
x_16 = lean_st_ref_set(x_3, x_6, x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
x_25 = lean_ctor_get(x_6, 2);
x_26 = lean_ctor_get(x_6, 3);
x_27 = lean_ctor_get(x_6, 4);
x_28 = lean_ctor_get(x_6, 6);
x_29 = lean_ctor_get(x_6, 7);
x_30 = lean_ctor_get(x_6, 8);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_31 = l_Lean_Meta_isEqnThm_x3f___redArg___closed__0;
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*3);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_33, 0, x_2);
lean_closure_set(x_33, 1, x_1);
x_34 = l_Lean_EnvExtension_modifyState___redArg(x_31, x_23, x_33, x_32);
x_35 = l_Lean_Meta_markAsRecursive___redArg___closed__3;
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_25);
lean_ctor_set(x_36, 3, x_26);
lean_ctor_set(x_36, 4, x_27);
lean_ctor_set(x_36, 5, x_35);
lean_ctor_set(x_36, 6, x_28);
lean_ctor_set(x_36, 7, x_29);
lean_ctor_set(x_36, 8, x_30);
x_37 = lean_st_ref_set(x_3, x_36, x_7);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0;
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_3, x_7);
lean_dec(x_3);
lean_inc(x_8);
x_9 = l_Nat_reprFast(x_8);
x_10 = lean_string_append(x_6, x_9);
lean_dec_ref(x_9);
lean_inc(x_1);
lean_inc_ref(x_2);
x_11 = l_Lean_Meta_mkEqLikeNameFor(x_2, x_1, x_10);
lean_inc_ref(x_2);
x_12 = l_Lean_Environment_containsOnBranch(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec_ref(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_4, x_11);
x_3 = x_8;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(x_1, x_2, x_3, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_eqn1ThmSuffix___closed__0;
lean_inc(x_1);
lean_inc_ref(x_8);
x_10 = l_Lean_Meta_mkEqLikeNameFor(x_8, x_1, x_9);
x_11 = 1;
lean_inc(x_10);
lean_inc_ref(x_8);
x_12 = l_Lean_Environment_contains(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec(x_1);
x_13 = lean_box(0);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___closed__0;
x_16 = lean_array_push(x_15, x_10);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(x_1, x_8, x_14, x_16, x_7);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc(x_18);
x_20 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(x_1, x_18, x_2, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_18);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; 
x_27 = lean_ctor_get(x_4, 0);
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_4);
x_29 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_eqn1ThmSuffix___closed__0;
lean_inc(x_1);
lean_inc_ref(x_29);
x_31 = l_Lean_Meta_mkEqLikeNameFor(x_29, x_1, x_30);
x_32 = 1;
lean_inc(x_31);
lean_inc_ref(x_29);
x_33 = l_Lean_Environment_contains(x_29, x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec_ref(x_29);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___closed__0;
x_38 = lean_array_push(x_37, x_31);
lean_inc(x_1);
x_39 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___redArg(x_1, x_29, x_36, x_38, x_28);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec_ref(x_39);
lean_inc(x_40);
x_42 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(x_1, x_40, x_2, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
if (lean_is_scalar(x_44)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_44;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_5);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_1);
x_15 = lean_apply_6(x_13, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_free_object(x_4);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc_ref(x_2);
{
lean_object* _tmp_3 = x_14;
lean_object* _tmp_4 = x_2;
lean_object* _tmp_9 = x_17;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_14);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec_ref(x_15);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(x_1, x_20, x_9, x_19);
lean_dec(x_9);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_24);
lean_ctor_set(x_21, 0, x_4);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_16);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_1);
x_34 = lean_apply_6(x_32, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
lean_inc_ref(x_2);
{
lean_object* _tmp_3 = x_33;
lean_object* _tmp_4 = x_2;
lean_object* _tmp_9 = x_36;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_33);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec_ref(x_34);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___redArg(x_1, x_39, x_9, x_38);
lean_dec(x_9);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_35);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_33);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_48 = x_34;
} else {
 lean_dec_ref(x_34);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_7 = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec_ref(x_7);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg(x_1, x_5, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Lean_Meta_registerGetEqnsFn___closed__2;
x_21 = lean_st_ref_get(x_20, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_box(0);
x_25 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___closed__0;
x_26 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___redArg(x_1, x_25, x_24, x_22, x_25, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
lean_ctor_set(x_26, 0, x_18);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_26, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec_ref(x_28);
lean_ctor_set(x_26, 0, x_35);
return x_26;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec_ref(x_28);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_17;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
return x_7;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2;
x_4 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4;
x_3 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5;
x_9 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__6;
x_10 = l_Lean_Meta_withLCtx___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_8, x_9, x_7, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getEqnsFor_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_4, x_6, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_eqnAffectingOptions;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__4() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_72; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_29 = lean_st_ref_get(x_6, x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_32);
x_33 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_5, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_5, 5);
lean_inc(x_36);
x_37 = lean_ctor_get(x_5, 6);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 7);
lean_inc(x_38);
x_39 = lean_ctor_get(x_5, 8);
lean_inc(x_39);
x_40 = lean_ctor_get(x_5, 9);
lean_inc(x_40);
x_41 = lean_ctor_get(x_5, 10);
lean_inc(x_41);
x_42 = lean_ctor_get(x_5, 11);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_5, sizeof(void*)*13 + 1);
x_44 = lean_ctor_get(x_5, 12);
lean_inc_ref(x_44);
lean_dec_ref(x_5);
x_78 = l_Lean_Meta_eqnAffectingOptions;
x_79 = l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2;
x_80 = lean_nat_dec_lt(x_2, x_79);
if (x_80 == 0)
{
x_72 = x_34;
goto block_77;
}
else
{
uint8_t x_81; 
x_81 = l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__3;
if (x_81 == 0)
{
x_72 = x_34;
goto block_77;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__4;
x_84 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_getEqnsFor_x3f_spec__0(x_78, x_82, x_83, x_34);
x_72 = x_84;
goto block_77;
}
}
block_28:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0;
x_25 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__0(x_8, x_24);
x_26 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_8);
lean_ctor_set(x_26, 3, x_12);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set(x_26, 5, x_13);
lean_ctor_set(x_26, 6, x_14);
lean_ctor_set(x_26, 7, x_15);
lean_ctor_set(x_26, 8, x_16);
lean_ctor_set(x_26, 9, x_17);
lean_ctor_set(x_26, 10, x_18);
lean_ctor_set(x_26, 11, x_19);
lean_ctor_set(x_26, 12, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*13, x_9);
lean_ctor_set_uint8(x_26, sizeof(void*)*13 + 1, x_20);
x_27 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(x_1, x_3, x_4, x_26, x_22, x_23);
return x_27;
}
block_71:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_st_ref_take(x_6, x_31);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 5);
lean_dec(x_53);
x_54 = l_Lean_Kernel_enableDiag(x_52, x_46);
x_55 = l_Lean_Meta_markAsRecursive___redArg___closed__3;
lean_ctor_set(x_49, 5, x_55);
lean_ctor_set(x_49, 0, x_54);
x_56 = lean_st_ref_set(x_6, x_49, x_50);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec_ref(x_56);
x_8 = x_45;
x_9 = x_46;
x_10 = x_32;
x_11 = x_33;
x_12 = x_35;
x_13 = x_36;
x_14 = x_37;
x_15 = x_38;
x_16 = x_39;
x_17 = x_40;
x_18 = x_41;
x_19 = x_42;
x_20 = x_43;
x_21 = x_44;
x_22 = x_6;
x_23 = x_57;
goto block_28;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
x_60 = lean_ctor_get(x_49, 2);
x_61 = lean_ctor_get(x_49, 3);
x_62 = lean_ctor_get(x_49, 4);
x_63 = lean_ctor_get(x_49, 6);
x_64 = lean_ctor_get(x_49, 7);
x_65 = lean_ctor_get(x_49, 8);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_66 = l_Lean_Kernel_enableDiag(x_58, x_46);
x_67 = l_Lean_Meta_markAsRecursive___redArg___closed__3;
x_68 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_59);
lean_ctor_set(x_68, 2, x_60);
lean_ctor_set(x_68, 3, x_61);
lean_ctor_set(x_68, 4, x_62);
lean_ctor_set(x_68, 5, x_67);
lean_ctor_set(x_68, 6, x_63);
lean_ctor_set(x_68, 7, x_64);
lean_ctor_set(x_68, 8, x_65);
x_69 = lean_st_ref_set(x_6, x_68, x_50);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec_ref(x_69);
x_8 = x_45;
x_9 = x_46;
x_10 = x_32;
x_11 = x_33;
x_12 = x_35;
x_13 = x_36;
x_14 = x_37;
x_15 = x_38;
x_16 = x_39;
x_17 = x_40;
x_18 = x_41;
x_19 = x_42;
x_20 = x_43;
x_21 = x_44;
x_22 = x_6;
x_23 = x_70;
goto block_28;
}
}
else
{
x_8 = x_45;
x_9 = x_46;
x_10 = x_32;
x_11 = x_33;
x_12 = x_35;
x_13 = x_36;
x_14 = x_37;
x_15 = x_38;
x_16 = x_39;
x_17 = x_40;
x_18 = x_41;
x_19 = x_42;
x_20 = x_43;
x_21 = x_44;
x_22 = x_6;
x_23 = x_31;
goto block_28;
}
}
block_77:
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_73);
lean_dec(x_30);
x_74 = l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1;
x_75 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_72, x_74);
x_76 = l_Lean_Kernel_isDiagnosticsEnabled(x_73);
lean_dec_ref(x_73);
if (x_76 == 0)
{
if (x_75 == 0)
{
x_8 = x_72;
x_9 = x_75;
x_10 = x_32;
x_11 = x_33;
x_12 = x_35;
x_13 = x_36;
x_14 = x_37;
x_15 = x_38;
x_16 = x_39;
x_17 = x_40;
x_18 = x_41;
x_19 = x_42;
x_20 = x_43;
x_21 = x_44;
x_22 = x_6;
x_23 = x_31;
goto block_28;
}
else
{
x_45 = x_72;
x_46 = x_75;
x_47 = x_76;
goto block_71;
}
}
else
{
x_45 = x_72;
x_46 = x_75;
x_47 = x_75;
goto block_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5;
x_10 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__6;
x_11 = l_Lean_Meta_withLCtx___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_9, x_10, x_8, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_getEqnsFor_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_getEqnsFor_x3f_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getEqnsFor_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_generateEagerEqns_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_13; uint8_t x_15; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = 1;
x_15 = l_Lean_Option_get___at___Lean_Compiler_LCNF_toConfigOptions_spec__1(x_1, x_6);
lean_dec_ref(x_6);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_unbox(x_7);
lean_dec(x_7);
if (x_16 == 0)
{
goto block_12;
}
else
{
x_13 = x_15;
goto block_14;
}
}
else
{
uint8_t x_17; 
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = x_17;
goto block_14;
}
block_12:
{
if (x_5 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
}
}
block_14:
{
if (x_13 == 0)
{
return x_8;
}
else
{
goto block_12;
}
}
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
}
static uint8_t _init_l_Lean_Meta_generateEagerEqns___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_5_;
x_2 = l_Lean_Meta_generateEagerEqns___closed__2;
x_3 = l_Lean_Meta_generateEagerEqns___closed__1;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("generating eager equations for ", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_generateEagerEqns___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_generateEagerEqns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_5_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Meta_eqnAffectingOptions;
x_28 = l_Lean_Meta_generateEagerEqns___closed__0;
if (x_28 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
goto block_9;
}
else
{
if (x_28 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_4, 2);
lean_inc(x_29);
x_30 = 0;
x_31 = l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__4;
x_32 = l_Array_anyMUnsafe_any___at___Lean_Meta_generateEagerEqns_spec__0(x_29, x_27, x_30, x_31);
lean_dec(x_29);
if (x_32 == 0)
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
goto block_9;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = l_Lean_Meta_generateEagerEqns___closed__3;
x_34 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_33, x_4, x_6);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec_ref(x_34);
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_37;
goto block_26;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_34, 1);
x_40 = lean_ctor_get(x_34, 0);
lean_dec(x_40);
x_41 = l_Lean_Meta_generateEagerEqns___closed__5;
lean_inc(x_1);
x_42 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_34, 7);
lean_ctor_set(x_34, 1, x_42);
lean_ctor_set(x_34, 0, x_41);
x_43 = l_Lean_Meta_generateEagerEqns___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_33, x_44, x_2, x_3, x_4, x_5, x_39);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_46;
goto block_26;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_dec(x_34);
x_48 = l_Lean_Meta_generateEagerEqns___closed__5;
lean_inc(x_1);
x_49 = l_Lean_MessageData_ofName(x_1);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Meta_generateEagerEqns___closed__6;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_33, x_52, x_2, x_3, x_4, x_5, x_47);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec_ref(x_53);
x_10 = x_2;
x_11 = x_3;
x_12 = x_4;
x_13 = x_5;
x_14 = x_54;
goto block_26;
}
}
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
block_26:
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_generateEagerEqns_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_generateEagerEqns_spec__0(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2191_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_Meta_registerGetUnfoldEqnFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_initializing(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_Meta_registerGetEqnsFn___closed__1;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Meta_registerGetEqnsFn___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = l_Lean_Meta_registerGetUnfoldEqnFn___closed__0;
x_14 = lean_st_ref_take(x_13, x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_16);
lean_ctor_set(x_14, 0, x_1);
x_18 = lean_st_ref_set(x_13, x_14, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_st_ref_set(x_13, x_25, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_5);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_1);
x_15 = lean_apply_6(x_13, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_free_object(x_4);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc_ref(x_2);
{
lean_object* _tmp_3 = x_14;
lean_object* _tmp_4 = x_2;
lean_object* _tmp_9 = x_17;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_10 = _tmp_9;
}
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_21);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
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
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_1);
x_31 = lean_apply_6(x_29, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec_ref(x_31);
lean_inc_ref(x_2);
{
lean_object* _tmp_3 = x_30;
lean_object* _tmp_4 = x_2;
lean_object* _tmp_9 = x_33;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_36 = x_31;
} else {
 lean_dec_ref(x_31);
 x_36 = lean_box(0);
}
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_3);
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_30);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_42 = x_31;
} else {
 lean_dec_ref(x_31);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_getUnfoldEqnFor_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_7, x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_17);
lean_dec(x_15);
x_18 = 1;
lean_inc(x_1);
x_19 = l_Lean_Environment_contains(x_17, x_1, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_13);
lean_dec(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_2);
x_20 = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(x_2, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec_ref(x_20);
x_9 = x_23;
goto block_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec_ref(x_20);
lean_inc(x_2);
x_25 = l_Lean_Meta_isRecursiveDefinition___redArg(x_2, x_7, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
if (x_3 == 0)
{
lean_object* x_28; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec_ref(x_25);
x_9 = x_28;
goto block_12;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec_ref(x_25);
x_30 = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm(x_2, x_4, x_5, x_6, x_7, x_29);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec_ref(x_25);
x_32 = l_Lean_Meta_registerGetUnfoldEqnFn___closed__0;
x_33 = lean_st_ref_get(x_32, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_box(0);
x_37 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___closed__0;
x_38 = l_List_forIn_x27_loop___at___Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(x_2, x_37, x_36, x_34, x_37, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec_ref(x_38);
x_9 = x_41;
goto block_12;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_38, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_40, 0);
lean_inc(x_44);
lean_dec_ref(x_40);
lean_ctor_set(x_38, 0, x_44);
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec_ref(x_40);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_20);
if (x_52 == 0)
{
return x_20;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_20, 0);
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_20);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_13, 0, x_56);
return x_13;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
lean_dec(x_57);
x_60 = 1;
lean_inc(x_1);
x_61 = l_Lean_Environment_contains(x_59, x_1, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_2);
x_62 = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(x_2, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec_ref(x_62);
x_9 = x_65;
goto block_12;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec_ref(x_62);
lean_inc(x_2);
x_67 = l_Lean_Meta_isRecursiveDefinition___redArg(x_2, x_7, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
if (x_3 == 0)
{
lean_object* x_70; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec_ref(x_67);
x_9 = x_70;
goto block_12;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec_ref(x_67);
x_72 = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm(x_2, x_4, x_5, x_6, x_7, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec_ref(x_67);
x_74 = l_Lean_Meta_registerGetUnfoldEqnFn___closed__0;
x_75 = lean_st_ref_get(x_74, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = lean_box(0);
x_79 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___closed__0;
x_80 = l_List_forIn_x27_loop___at___Lean_Meta_getUnfoldEqnFor_x3f_spec__0___redArg(x_2, x_79, x_78, x_76, x_79, x_4, x_5, x_6, x_7, x_77);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec_ref(x_80);
x_9 = x_83;
goto block_12;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_85 = x_80;
} else {
 lean_dec_ref(x_80);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec_ref(x_82);
if (lean_is_scalar(x_85)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_85;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_80, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_90 = x_80;
} else {
 lean_dec_ref(x_80);
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
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_92 = lean_ctor_get(x_62, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_62, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_94 = x_62;
} else {
 lean_dec_ref(x_62);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_1);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_58);
return x_97;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid unfold theorem name `", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has been generated expected `", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_unfoldThmSuffix___closed__0;
lean_inc(x_1);
x_14 = l_Lean_Meta_mkEqLikeNameFor(x_12, x_1, x_13);
x_15 = lean_box(x_2);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 8, 3);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_15);
x_17 = 1;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_18 = l_Lean_withoutExporting___at___Lean_Meta_letToHave_spec__0___redArg(x_16, x_17, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_dec(x_14);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = lean_name_eq(x_21, x_14);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_24 = lean_ctor_get(x_18, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1;
x_27 = l_Lean_MessageData_ofName(x_21);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_26);
x_28 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_28);
lean_ctor_set(x_8, 0, x_18);
x_29 = l_Lean_MessageData_ofName(x_14);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_32, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_18);
x_38 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1;
x_39 = l_Lean_MessageData_ofName(x_21);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_41);
lean_ctor_set(x_8, 0, x_40);
x_42 = l_Lean_MessageData_ofName(x_14);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_8);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_45, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_14);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_18;
}
}
}
else
{
lean_dec(x_14);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_18;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_51 = lean_ctor_get(x_8, 0);
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_8);
x_53 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_unfoldThmSuffix___closed__0;
lean_inc(x_1);
x_55 = l_Lean_Meta_mkEqLikeNameFor(x_53, x_1, x_54);
x_56 = lean_box(x_2);
lean_inc(x_55);
x_57 = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed), 8, 3);
lean_closure_set(x_57, 0, x_55);
lean_closure_set(x_57, 1, x_1);
lean_closure_set(x_57, 2, x_56);
x_58 = 1;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_59 = l_Lean_withoutExporting___at___Lean_Meta_letToHave_spec__0___redArg(x_57, x_58, x_3, x_4, x_5, x_6, x_52);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_dec(x_55);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec_ref(x_60);
x_63 = lean_name_eq(x_62, x_55);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1;
x_66 = l_Lean_MessageData_ofName(x_62);
if (lean_is_scalar(x_64)) {
 x_67 = lean_alloc_ctor(7, 2, 0);
} else {
 x_67 = x_64;
 lean_ctor_set_tag(x_67, 7);
}
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_MessageData_ofName(x_55);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_73, x_3, x_4, x_5, x_6, x_61);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_55);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_59;
}
}
}
else
{
lean_dec(x_55);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5;
x_11 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__6;
x_12 = l_Lean_Meta_withLCtx___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_10, x_11, x_9, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_getUnfoldEqnFor_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_Meta_getUnfoldEqnFor_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_getUnfoldEqnFor_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" Lean.Meta.Eqns reserved name action for ", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__0___closed__1____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_2928_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = l_Lean_Meta_generateEagerEqns___closed__6;
x_7 = l_Lean_exceptBoolEmoji___redArg(x_2);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec_ref(x_7);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Meta_initFn___lam__0___closed__1____x40_Lean_Meta_Eqns___hyg_2928_;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_MessageData_ofName(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__1____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__2____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__3____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__4____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__5____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__6____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__7____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__6____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = l_Lean_Meta_initFn___lam__1___closed__5____x40_Lean_Meta_Eqns___hyg_2928_;
x_3 = l_Lean_Meta_initFn___lam__1___closed__4____x40_Lean_Meta_Eqns___hyg_2928_;
x_4 = l_Lean_Meta_initFn___lam__1___closed__3____x40_Lean_Meta_Eqns___hyg_2928_;
x_5 = l_Lean_Meta_initFn___lam__1___closed__2____x40_Lean_Meta_Eqns___hyg_2928_;
x_6 = l_Lean_Meta_initFn___lam__1___closed__1____x40_Lean_Meta_Eqns___hyg_2928_;
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
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__8____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__9____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__10____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__11____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__12____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__11____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = l_Lean_Meta_initFn___lam__1___closed__10____x40_Lean_Meta_Eqns___hyg_2928_;
x_3 = l_Lean_Meta_initFn___lam__1___closed__9____x40_Lean_Meta_Eqns___hyg_2928_;
x_4 = l_Lean_Meta_initFn___lam__1___closed__8____x40_Lean_Meta_Eqns___hyg_2928_;
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
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__13____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__14____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__13____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__15____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_initFn___lam__1___closed__13____x40_Lean_Meta_Eqns___hyg_2928_;
x_4 = l_Lean_Meta_initFn___lam__1___closed__14____x40_Lean_Meta_Eqns___hyg_2928_;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__16____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__17____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__16____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = l_Lean_Meta_initFn___lam__1___closed__1____x40_Lean_Meta_Eqns___hyg_2928_;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__18____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__17____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = l_Lean_Meta_initFn___lam__1___closed__15____x40_Lean_Meta_Eqns___hyg_2928_;
x_3 = lean_box(1);
x_4 = l_Lean_Meta_initFn___lam__1___closed__12____x40_Lean_Meta_Eqns___hyg_2928_;
x_5 = l_Lean_Meta_initFn___lam__1___closed__7____x40_Lean_Meta_Eqns___hyg_2928_;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__19____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__20____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__1___closed__13____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__21____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_initFn___lam__1___closed__13____x40_Lean_Meta_Eqns___hyg_2928_;
x_4 = l_Lean_Meta_initFn___lam__1___closed__20____x40_Lean_Meta_Eqns___hyg_2928_;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__22____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_Meta_initFn___lam__1___closed__21____x40_Lean_Meta_Eqns___hyg_2928_;
x_3 = l_Lean_Meta_initFn___lam__1___closed__19____x40_Lean_Meta_Eqns___hyg_2928_;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__1___closed__23____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Eqns___hyg_2928_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_st_ref_get(x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_14);
lean_dec(x_11);
lean_inc(x_1);
x_15 = l_Lean_Meta_declFromEqLikeName(x_14, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_13);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_5 = x_12;
goto block_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_3, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_23);
lean_dec(x_20);
lean_inc(x_18);
lean_inc(x_17);
x_24 = l_Lean_Meta_mkEqLikeNameFor(x_23, x_17, x_18);
x_25 = lean_name_eq(x_1, x_24);
lean_dec(x_24);
lean_dec(x_1);
if (x_25 == 0)
{
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = x_21;
goto block_9;
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_inc(x_18);
x_26 = l_Lean_Meta_isEqnReservedNameSuffix(x_18);
if (x_26 == 0)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_22);
x_35 = l_Lean_Meta_unfoldThmSuffix___closed__0;
x_36 = lean_string_dec_eq(x_18, x_35);
lean_dec(x_18);
if (x_36 == 0)
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = x_21;
goto block_9;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_44 = lean_box(1);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Meta_initFn___lam__1___closed__18____x40_Lean_Meta_Eqns___hyg_2928_;
x_47 = lean_st_mk_ref(x_46, x_21);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = 1;
x_51 = 0;
x_52 = 2;
x_53 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_53, 0, x_26);
lean_ctor_set_uint8(x_53, 1, x_26);
lean_ctor_set_uint8(x_53, 2, x_26);
lean_ctor_set_uint8(x_53, 3, x_26);
lean_ctor_set_uint8(x_53, 4, x_26);
lean_ctor_set_uint8(x_53, 5, x_36);
lean_ctor_set_uint8(x_53, 6, x_36);
lean_ctor_set_uint8(x_53, 7, x_26);
lean_ctor_set_uint8(x_53, 8, x_36);
lean_ctor_set_uint8(x_53, 9, x_50);
lean_ctor_set_uint8(x_53, 10, x_51);
lean_ctor_set_uint8(x_53, 11, x_36);
lean_ctor_set_uint8(x_53, 12, x_36);
lean_ctor_set_uint8(x_53, 13, x_36);
lean_ctor_set_uint8(x_53, 14, x_52);
lean_ctor_set_uint8(x_53, 15, x_36);
lean_ctor_set_uint8(x_53, 16, x_36);
lean_ctor_set_uint8(x_53, 17, x_36);
lean_ctor_set_uint8(x_53, 18, x_36);
x_54 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_53);
x_55 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set_uint64(x_55, sizeof(void*)*1, x_54);
x_56 = l_Lean_Meta_initFn___lam__1___closed__22____x40_Lean_Meta_Eqns___hyg_2928_;
x_57 = l_Lean_Meta_initFn___lam__1___closed__23____x40_Lean_Meta_Eqns___hyg_2928_;
x_58 = lean_box(0);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_44);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set(x_60, 4, x_58);
lean_ctor_set(x_60, 5, x_45);
lean_ctor_set(x_60, 6, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*7, x_26);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 1, x_26);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 2, x_26);
lean_inc(x_48);
x_61 = l_Lean_Meta_getUnfoldEqnFor_x3f(x_17, x_36, x_60, x_48, x_2, x_3, x_49);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = lean_st_ref_get(x_48, x_63);
lean_dec(x_48);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec_ref(x_64);
x_37 = x_62;
x_38 = x_65;
goto block_43;
}
else
{
lean_dec(x_48);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec_ref(x_61);
x_37 = x_66;
x_38 = x_67;
goto block_43;
}
else
{
uint8_t x_68; 
lean_dec(x_13);
x_68 = !lean_is_exclusive(x_61);
if (x_68 == 0)
{
return x_61;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_61, 0);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_61);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
block_43:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_box(x_26);
if (lean_is_scalar(x_13)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_13;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_37);
x_41 = lean_box(x_36);
if (lean_is_scalar(x_13)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_13;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_18);
lean_dec(x_13);
x_72 = lean_box(1);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Meta_initFn___lam__1___closed__18____x40_Lean_Meta_Eqns___hyg_2928_;
x_75 = lean_st_mk_ref(x_74, x_21);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec_ref(x_75);
x_78 = 0;
x_79 = 1;
x_80 = 0;
x_81 = 2;
x_82 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_82, 0, x_78);
lean_ctor_set_uint8(x_82, 1, x_78);
lean_ctor_set_uint8(x_82, 2, x_78);
lean_ctor_set_uint8(x_82, 3, x_78);
lean_ctor_set_uint8(x_82, 4, x_78);
lean_ctor_set_uint8(x_82, 5, x_26);
lean_ctor_set_uint8(x_82, 6, x_26);
lean_ctor_set_uint8(x_82, 7, x_78);
lean_ctor_set_uint8(x_82, 8, x_26);
lean_ctor_set_uint8(x_82, 9, x_79);
lean_ctor_set_uint8(x_82, 10, x_80);
lean_ctor_set_uint8(x_82, 11, x_26);
lean_ctor_set_uint8(x_82, 12, x_26);
lean_ctor_set_uint8(x_82, 13, x_26);
lean_ctor_set_uint8(x_82, 14, x_81);
lean_ctor_set_uint8(x_82, 15, x_26);
lean_ctor_set_uint8(x_82, 16, x_26);
lean_ctor_set_uint8(x_82, 17, x_26);
lean_ctor_set_uint8(x_82, 18, x_26);
x_83 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_82);
x_84 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint64(x_84, sizeof(void*)*1, x_83);
x_85 = l_Lean_Meta_initFn___lam__1___closed__22____x40_Lean_Meta_Eqns___hyg_2928_;
x_86 = l_Lean_Meta_initFn___lam__1___closed__23____x40_Lean_Meta_Eqns___hyg_2928_;
x_87 = lean_box(0);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_72);
lean_ctor_set(x_89, 2, x_85);
lean_ctor_set(x_89, 3, x_86);
lean_ctor_set(x_89, 4, x_87);
lean_ctor_set(x_89, 5, x_73);
lean_ctor_set(x_89, 6, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*7, x_78);
lean_ctor_set_uint8(x_89, sizeof(void*)*7 + 1, x_78);
lean_ctor_set_uint8(x_89, sizeof(void*)*7 + 2, x_78);
lean_inc(x_76);
x_90 = l_Lean_Meta_getEqnsFor_x3f(x_17, x_89, x_76, x_2, x_3, x_77);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = lean_st_ref_get(x_76, x_92);
lean_dec(x_76);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec_ref(x_93);
x_27 = x_91;
x_28 = x_94;
goto block_34;
}
else
{
lean_dec(x_76);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
lean_dec_ref(x_90);
x_27 = x_95;
x_28 = x_96;
goto block_34;
}
else
{
uint8_t x_97; 
lean_dec(x_22);
x_97 = !lean_is_exclusive(x_90);
if (x_97 == 0)
{
return x_90;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_90, 0);
x_99 = lean_ctor_get(x_90, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_90);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
block_34:
{
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_box(x_29);
if (lean_is_scalar(x_22)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_22;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_27);
x_32 = lean_box(x_26);
if (lean_is_scalar(x_22)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_22;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
}
}
block_9:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__2___closed__0____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ReservedNameAction", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__2___closed__1____x40_Lean_Meta_Eqns___hyg_2928_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn___lam__2___closed__0____x40_Lean_Meta_Eqns___hyg_2928_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__2____x40_Lean_Meta_Eqns___hyg_2928_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_2928____boxed), 5, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__1____x40_Lean_Meta_Eqns___hyg_2928_), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Meta_initFn___lam__2___closed__1____x40_Lean_Meta_Eqns___hyg_2928_;
x_8 = 1;
x_9 = l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_5_;
x_10 = l_Lean_withTraceNode___at___Lean_Core_wrapAsyncAsSnapshot_spec__18___redArg(x_7, x_5, x_6, x_8, x_9, x_2, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2928_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__2____x40_Lean_Meta_Eqns___hyg_2928_), 4, 0);
x_3 = l_Lean_registerReservedNameAction(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_2928____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_initFn___lam__0____x40_Lean_Meta_Eqns___hyg_2928_(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DefEqAttrib(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_LetToHave(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ReservedNameAction(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DefEqAttrib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_LetToHave(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_5_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_5_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_5_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_5_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_5_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_5_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_5_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_5_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_5_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_5_);
l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Eqns___hyg_5_ = _init_l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Eqns___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__5____x40_Lean_Meta_Eqns___hyg_5_);
l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Eqns___hyg_5_ = _init_l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Eqns___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__6____x40_Lean_Meta_Eqns___hyg_5_);
l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Eqns___hyg_5_ = _init_l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Eqns___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__7____x40_Lean_Meta_Eqns___hyg_5_);
l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Eqns___hyg_5_ = _init_l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Eqns___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__8____x40_Lean_Meta_Eqns___hyg_5_);
l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Eqns___hyg_5_ = _init_l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Eqns___hyg_5_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__9____x40_Lean_Meta_Eqns___hyg_5_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_eqns_nonrecursive = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_eqns_nonrecursive);
lean_dec_ref(res);
}l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_44_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_44_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_44_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_44_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_44_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_44_);
l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_44_ = _init_l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_44_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__2____x40_Lean_Meta_Eqns___hyg_44_);
l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_44_ = _init_l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_44_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__3____x40_Lean_Meta_Eqns___hyg_44_);
l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_44_ = _init_l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_44_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__4____x40_Lean_Meta_Eqns___hyg_44_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_eqns_deepRecursiveSplit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_eqns_deepRecursiveSplit);
lean_dec_ref(res);
}l_Lean_Meta_eqnAffectingOptions___closed__0 = _init_l_Lean_Meta_eqnAffectingOptions___closed__0();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions___closed__0);
l_Lean_Meta_eqnAffectingOptions___closed__1 = _init_l_Lean_Meta_eqnAffectingOptions___closed__1();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions___closed__1);
l_Lean_Meta_eqnAffectingOptions___closed__2 = _init_l_Lean_Meta_eqnAffectingOptions___closed__2();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions___closed__2);
l_Lean_Meta_eqnAffectingOptions___closed__3 = _init_l_Lean_Meta_eqnAffectingOptions___closed__3();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions___closed__3);
l_Lean_Meta_eqnAffectingOptions___closed__4 = _init_l_Lean_Meta_eqnAffectingOptions___closed__4();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions___closed__4);
l_Lean_Meta_eqnAffectingOptions = _init_l_Lean_Meta_eqnAffectingOptions();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions);
l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_98_ = _init_l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_98_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__0____x40_Lean_Meta_Eqns___hyg_98_);
l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_98_ = _init_l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_98_();
lean_mark_persistent(l_Lean_Meta_initFn___closed__1____x40_Lean_Meta_Eqns___hyg_98_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_recExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_recExt);
lean_dec_ref(res);
}l_Lean_Meta_markAsRecursive___redArg___closed__0 = _init_l_Lean_Meta_markAsRecursive___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_markAsRecursive___redArg___closed__0);
l_Lean_Meta_markAsRecursive___redArg___closed__1 = _init_l_Lean_Meta_markAsRecursive___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_markAsRecursive___redArg___closed__1);
l_Lean_Meta_markAsRecursive___redArg___closed__2 = _init_l_Lean_Meta_markAsRecursive___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_markAsRecursive___redArg___closed__2);
l_Lean_Meta_markAsRecursive___redArg___closed__3 = _init_l_Lean_Meta_markAsRecursive___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_markAsRecursive___redArg___closed__3);
l_Lean_Meta_eqnThmSuffixBase___closed__0 = _init_l_Lean_Meta_eqnThmSuffixBase___closed__0();
lean_mark_persistent(l_Lean_Meta_eqnThmSuffixBase___closed__0);
l_Lean_Meta_eqnThmSuffixBase = _init_l_Lean_Meta_eqnThmSuffixBase();
lean_mark_persistent(l_Lean_Meta_eqnThmSuffixBase);
l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0 = _init_l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0();
lean_mark_persistent(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__0);
l_Lean_Meta_eqnThmSuffixBasePrefix = _init_l_Lean_Meta_eqnThmSuffixBasePrefix();
lean_mark_persistent(l_Lean_Meta_eqnThmSuffixBasePrefix);
l_Lean_Meta_eqn1ThmSuffix___closed__0 = _init_l_Lean_Meta_eqn1ThmSuffix___closed__0();
lean_mark_persistent(l_Lean_Meta_eqn1ThmSuffix___closed__0);
l_Lean_Meta_eqn1ThmSuffix = _init_l_Lean_Meta_eqn1ThmSuffix();
lean_mark_persistent(l_Lean_Meta_eqn1ThmSuffix);
l_Lean_Meta_unfoldThmSuffix___closed__0 = _init_l_Lean_Meta_unfoldThmSuffix___closed__0();
lean_mark_persistent(l_Lean_Meta_unfoldThmSuffix___closed__0);
l_Lean_Meta_unfoldThmSuffix = _init_l_Lean_Meta_unfoldThmSuffix();
lean_mark_persistent(l_Lean_Meta_unfoldThmSuffix);
l_Lean_Meta_eqUnfoldThmSuffix___closed__0 = _init_l_Lean_Meta_eqUnfoldThmSuffix___closed__0();
lean_mark_persistent(l_Lean_Meta_eqUnfoldThmSuffix___closed__0);
l_Lean_Meta_eqUnfoldThmSuffix = _init_l_Lean_Meta_eqUnfoldThmSuffix();
lean_mark_persistent(l_Lean_Meta_eqUnfoldThmSuffix);
l_Lean_Meta_declFromEqLikeName___closed__0 = _init_l_Lean_Meta_declFromEqLikeName___closed__0();
lean_mark_persistent(l_Lean_Meta_declFromEqLikeName___closed__0);
l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0 = _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__0);
l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1 = _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__1);
l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2 = _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__2);
l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3 = _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__3);
l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4 = _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__4);
l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5 = _init_l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at___Lean_ensureReservedNameAvailable___at___Lean_Meta_ensureEqnReservedNamesAvailable_spec__0_spec__0___closed__5);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_717_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef);
lean_dec_ref(res);
}l_Lean_Meta_registerGetEqnsFn___closed__0 = _init_l_Lean_Meta_registerGetEqnsFn___closed__0();
lean_mark_persistent(l_Lean_Meta_registerGetEqnsFn___closed__0);
l_Lean_Meta_registerGetEqnsFn___closed__1 = _init_l_Lean_Meta_registerGetEqnsFn___closed__1();
lean_mark_persistent(l_Lean_Meta_registerGetEqnsFn___closed__1);
l_Lean_Meta_registerGetEqnsFn___closed__2 = _init_l_Lean_Meta_registerGetEqnsFn___closed__2();
lean_mark_persistent(l_Lean_Meta_registerGetEqnsFn___closed__2);
l_Lean_Meta_instInhabitedEqnsExtState___closed__0 = _init_l_Lean_Meta_instInhabitedEqnsExtState___closed__0();
lean_mark_persistent(l_Lean_Meta_instInhabitedEqnsExtState___closed__0);
l_Lean_Meta_instInhabitedEqnsExtState___closed__1 = _init_l_Lean_Meta_instInhabitedEqnsExtState___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedEqnsExtState___closed__1);
l_Lean_Meta_instInhabitedEqnsExtState = _init_l_Lean_Meta_instInhabitedEqnsExtState();
lean_mark_persistent(l_Lean_Meta_instInhabitedEqnsExtState);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_eqnsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_eqnsExt);
lean_dec_ref(res);
}l_Lean_Meta_isEqnThm_x3f___redArg___closed__0 = _init_l_Lean_Meta_isEqnThm_x3f___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_isEqnThm_x3f___redArg___closed__0);
l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___closed__0 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___redArg___closed__0);
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___closed__0 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lam__0___closed__0);
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__0);
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1);
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2);
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3);
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4);
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5);
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__6 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__6);
l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0 = _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__0);
l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1 = _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__1);
l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2 = _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__2);
l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__3 = _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__3();
l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__4 = _init_l_Lean_Meta_getEqnsFor_x3f___lam__0___closed__4();
l_Lean_Meta_generateEagerEqns___closed__0 = _init_l_Lean_Meta_generateEagerEqns___closed__0();
l_Lean_Meta_generateEagerEqns___closed__1 = _init_l_Lean_Meta_generateEagerEqns___closed__1();
lean_mark_persistent(l_Lean_Meta_generateEagerEqns___closed__1);
l_Lean_Meta_generateEagerEqns___closed__2 = _init_l_Lean_Meta_generateEagerEqns___closed__2();
lean_mark_persistent(l_Lean_Meta_generateEagerEqns___closed__2);
l_Lean_Meta_generateEagerEqns___closed__3 = _init_l_Lean_Meta_generateEagerEqns___closed__3();
lean_mark_persistent(l_Lean_Meta_generateEagerEqns___closed__3);
l_Lean_Meta_generateEagerEqns___closed__4 = _init_l_Lean_Meta_generateEagerEqns___closed__4();
lean_mark_persistent(l_Lean_Meta_generateEagerEqns___closed__4);
l_Lean_Meta_generateEagerEqns___closed__5 = _init_l_Lean_Meta_generateEagerEqns___closed__5();
lean_mark_persistent(l_Lean_Meta_generateEagerEqns___closed__5);
l_Lean_Meta_generateEagerEqns___closed__6 = _init_l_Lean_Meta_generateEagerEqns___closed__6();
lean_mark_persistent(l_Lean_Meta_generateEagerEqns___closed__6);
if (builtin) {res = l___private_Lean_Meta_Eqns_0__Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2191_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef);
lean_dec_ref(res);
}l_Lean_Meta_registerGetUnfoldEqnFn___closed__0 = _init_l_Lean_Meta_registerGetUnfoldEqnFn___closed__0();
lean_mark_persistent(l_Lean_Meta_registerGetUnfoldEqnFn___closed__0);
l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___closed__0 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__0___closed__0);
l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__0);
l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__1);
l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__2);
l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__3);
l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__4);
l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lam__1___closed__5);
l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__0___closed__1____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__0___closed__1____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__0___closed__1____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__0____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__1____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__1____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__1____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__2____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__2____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__2____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__3____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__3____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__3____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__4____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__4____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__4____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__5____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__5____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__5____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__6____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__6____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__6____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__7____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__7____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__7____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__8____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__8____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__8____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__9____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__9____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__9____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__10____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__10____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__10____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__11____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__11____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__11____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__12____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__12____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__12____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__13____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__13____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__13____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__14____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__14____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__14____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__15____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__15____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__15____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__16____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__16____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__16____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__17____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__17____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__17____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__18____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__18____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__18____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__19____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__19____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__19____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__20____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__20____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__20____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__21____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__21____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__21____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__22____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__22____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__22____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__1___closed__23____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__1___closed__23____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__1___closed__23____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__2___closed__0____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__2___closed__0____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__2___closed__0____x40_Lean_Meta_Eqns___hyg_2928_);
l_Lean_Meta_initFn___lam__2___closed__1____x40_Lean_Meta_Eqns___hyg_2928_ = _init_l_Lean_Meta_initFn___lam__2___closed__1____x40_Lean_Meta_Eqns___hyg_2928_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__2___closed__1____x40_Lean_Meta_Eqns___hyg_2928_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2928_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
