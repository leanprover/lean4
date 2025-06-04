// Lean compiler output
// Module: Lean.Meta.Eqns
// Imports: Lean.ReservedNameAction Lean.AddDecl Lean.Meta.Basic Lean.Meta.AppBuilder Lean.Meta.Match.MatcherInfo
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
static lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1___closed__1;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_isEqnThm___spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_is_matcher(lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNameAction(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2___closed__1;
static lean_object* l_Lean_Meta_markAsRecursive___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__3(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_717_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_eqnThmSuffixBasePrefix;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_declFromEqLikeName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_isEqnThm_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_anyAux___at_String_isNat___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getEqnsFor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____lambda__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_isEqnThm_x3f___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_isEqnThm___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exceptBoolEmoji___rarg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_isEqnThm___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static uint8_t l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__2;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_isEqnThm___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName___lambda__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_generateEagerEqns___closed__2;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static size_t l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__5;
LEAN_EXPORT uint8_t l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_markAsRecursive___closed__4;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lean_Meta_eqnThmSuffixBasePrefix___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_backward_eqns_deepRecursiveSplit;
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__5;
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__2;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_initializing(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5_(lean_object*);
static lean_object* l_Lean_Meta_declFromEqLikeName___closed__3;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__6;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__1;
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982____closed__1;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3;
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static uint8_t l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generateEagerEqns___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedEqnsExtState;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897_(lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__2;
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqn1ThmSuffix___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__2;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__3;
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__4___closed__1;
lean_object* l_Lean_privateToUserName(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqnThmSuffixBasePrefix___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__2;
static lean_object* l_Lean_Meta_getEqnsFor_x3f___lambda__1___closed__1;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_eqUnfoldThmSuffix___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__6;
static lean_object* l_Lean_Meta_markAsRecursive___closed__1;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lean_Meta_generateEagerEqns___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__8;
static lean_object* l_Lean_Meta_registerGetEqnsFn___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__6;
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Meta_isEqnThm___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Meta_eqn1ThmSuffix___closed__1;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at_Lean_executeReservedNameAction___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_eqnThmSuffixBase;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_declFromEqLikeName___closed__2;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnReservedNameSuffix___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__3;
static lean_object* l_Lean_Meta_eqnThmSuffixBase___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__2;
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_registerGetEqnsFn___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eqn1ThmSuffix;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_generateEagerEqns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_recExt;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eqUnfoldThmSuffix;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44_(lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
uint8_t l_String_isPrefixOf(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isSafeDefinition(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2___closed__1;
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_eqns_nonrecursive;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getEqnsFor_x3f___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__5;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_eqnsExt;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_declFromEqLikeName___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_declFromEqLikeName___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldThmSuffix;
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__2;
static lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnLikeSuffix___boxed(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_instantiateForallWithParamInfos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l_Lean_Meta_generateEagerEqns___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2160_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generateEagerEqns___closed__4;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_isEqnThm_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_generateEagerEqns___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_registerGetEqnsFn___closed__2;
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_isEqnThm_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_unfoldThmSuffix___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_ReducibilityAttrs_0__Lean_validate___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_eqnAffectingOptions;
static lean_object* l_Lean_Meta_isEqnThm_x3f___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__1;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5;
static lean_object* l_Lean_Meta_markAsRecursive___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__9;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__2;
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_generateEagerEqns___spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_isEqnThm___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__3;
static lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4;
static lean_object* l_Lean_Meta_eqnAffectingOptions___closed__5;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__1;
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backward", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqns", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nonrecursive", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Create fine-grained equational lemmas even for non-recursive definitions.", 73, 73);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__6;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__9;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__1;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__2;
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__3;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__7;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__10;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("deepRecursiveSplit", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Create equational lemmas for recursive functions like for non-recursive functions. If disabled, match statements in recursive function definitions that do not contain recursive calls do not cause further splits in the equational lemmas. This was the behavior before Lean 4.12, and the purpose of this option is to help migrating old code.", 338, 338);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__8;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__9;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__1;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__2;
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__1;
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__4;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__5;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_eqnAffectingOptions___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_backward_eqns_nonrecursive;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_eqnAffectingOptions___closed__3;
x_2 = l_Lean_Meta_eqnAffectingOptions___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_eqnAffectingOptions___closed__4;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_eqnAffectingOptions() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_eqnAffectingOptions___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recExt", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__2;
x_3 = 3;
x_4 = l_Lean_mkTagDeclarationExtension(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_recExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_markAsRecursive___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_markAsRecursive___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 5);
lean_dec(x_10);
x_11 = l_Lean_Meta_markAsRecursive___closed__1;
x_12 = l_Lean_TagDeclarationExtension_tag(x_11, x_9, x_1);
x_13 = l_Lean_Meta_markAsRecursive___closed__4;
lean_ctor_set(x_6, 5, x_13);
lean_ctor_set(x_6, 0, x_12);
x_14 = lean_st_ref_set(x_3, x_6, x_7);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 2);
x_24 = lean_ctor_get(x_6, 3);
x_25 = lean_ctor_get(x_6, 4);
x_26 = lean_ctor_get(x_6, 6);
x_27 = lean_ctor_get(x_6, 7);
x_28 = lean_ctor_get(x_6, 8);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_29 = l_Lean_Meta_markAsRecursive___closed__1;
x_30 = l_Lean_TagDeclarationExtension_tag(x_29, x_21, x_1);
x_31 = l_Lean_Meta_markAsRecursive___closed__4;
x_32 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_22);
lean_ctor_set(x_32, 2, x_23);
lean_ctor_set(x_32, 3, x_24);
lean_ctor_set(x_32, 4, x_25);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_26);
lean_ctor_set(x_32, 7, x_27);
lean_ctor_set(x_32, 8, x_28);
x_33 = lean_st_ref_set(x_3, x_32, x_7);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_markAsRecursive(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_markAsRecursive___closed__1;
x_10 = l_Lean_TagDeclarationExtension_isTagged(x_9, x_8, x_1);
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_markAsRecursive___closed__1;
x_16 = l_Lean_TagDeclarationExtension_isTagged(x_15, x_14, x_1);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isRecursiveDefinition(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_eqnThmSuffixBase___closed__1() {
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
x_1 = l_Lean_Meta_eqnThmSuffixBase___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqnThmSuffixBasePrefix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqnThmSuffixBasePrefix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_eqnThmSuffixBase;
x_2 = l_Lean_Meta_eqnThmSuffixBasePrefix___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_eqnThmSuffixBasePrefix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_eqnThmSuffixBasePrefix___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqn1ThmSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("1", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqn1ThmSuffix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_eqnThmSuffixBasePrefix;
x_2 = l_Lean_Meta_eqn1ThmSuffix___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_eqn1ThmSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_eqn1ThmSuffix___closed__2;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnReservedNameSuffix(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_eqnThmSuffixBasePrefix;
x_3 = l_String_isPrefixOf(x_2, x_1);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_string_utf8_byte_size(x_1);
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Substring_nextn(x_7, x_8, x_6);
lean_dec(x_7);
x_10 = lean_nat_add(x_6, x_9);
lean_dec(x_9);
x_11 = lean_string_utf8_extract(x_1, x_10, x_5);
lean_dec(x_5);
lean_dec(x_10);
lean_dec(x_1);
x_12 = lean_string_utf8_byte_size(x_11);
x_13 = lean_nat_dec_eq(x_12, x_6);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_String_anyAux___at_String_isNat___spec__1(x_11, x_12, x_6);
lean_dec(x_12);
lean_dec(x_11);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = 0;
return x_17;
}
}
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
static lean_object* _init_l_Lean_Meta_unfoldThmSuffix___closed__1() {
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
x_1 = l_Lean_Meta_unfoldThmSuffix___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_eqUnfoldThmSuffix___closed__1() {
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
x_1 = l_Lean_Meta_eqUnfoldThmSuffix___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isEqnLikeSuffix(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_unfoldThmSuffix;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_eqUnfoldThmSuffix;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Meta_isEqnReservedNameSuffix(x_1);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_1);
x_7 = 1;
return x_7;
}
}
else
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = 1;
return x_8;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_declFromEqLikeName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
lean_inc(x_8);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Environment_setExporting(x_1, x_13);
lean_inc(x_11);
x_15 = l_Lean_Environment_isSafeDefinition(x_14, x_11);
if (x_15 == 0)
{
lean_free_object(x_7);
lean_dec(x_11);
{
lean_object* _tmp_6 = x_12;
lean_object* _tmp_7 = x_5;
lean_object* _tmp_8 = lean_box(0);
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_17; 
lean_inc(x_11);
lean_inc(x_1);
x_17 = lean_is_matcher(x_1, x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
lean_dec(x_1);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 1, x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_7);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_free_object(x_7);
lean_dec(x_11);
{
lean_object* _tmp_6 = x_12;
lean_object* _tmp_7 = x_5;
lean_object* _tmp_8 = lean_box(0);
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_7, 0);
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_7);
x_25 = 0;
lean_inc(x_1);
x_26 = l_Lean_Environment_setExporting(x_1, x_25);
lean_inc(x_23);
x_27 = l_Lean_Environment_isSafeDefinition(x_26, x_23);
if (x_27 == 0)
{
lean_dec(x_23);
{
lean_object* _tmp_6 = x_24;
lean_object* _tmp_7 = x_5;
lean_object* _tmp_8 = lean_box(0);
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_29; 
lean_inc(x_23);
lean_inc(x_1);
x_29 = lean_is_matcher(x_1, x_23);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_2);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
else
{
lean_dec(x_23);
{
lean_object* _tmp_6 = x_24;
lean_object* _tmp_7 = x_5;
lean_object* _tmp_8 = lean_box(0);
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_declFromEqLikeName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_declFromEqLikeName___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_declFromEqLikeName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_declFromEqLikeName___closed__1;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_declFromEqLikeName___closed__3() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
lean_inc(x_4);
x_5 = l_Lean_Meta_isEqnLikeSuffix(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = l_Lean_Meta_declFromEqLikeName___closed__2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_box(0);
lean_inc(x_3);
x_8 = l_Lean_privateToUserName(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_declFromEqLikeName___closed__3;
lean_inc(x_11);
x_13 = l_List_forIn_x27_loop___at_Lean_Meta_declFromEqLikeName___spec__1(x_1, x_4, x_7, x_11, x_12, x_11, x_11, x_12, lean_box(0));
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_declFromEqLikeName___closed__2;
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
return x_16;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Meta_declFromEqLikeName___closed__2;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_declFromEqLikeName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at_Lean_Meta_declFromEqLikeName___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_declFromEqLikeName___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_declFromEqLikeName___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = l_Lean_Environment_header(x_1);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*5 + 4);
lean_dec(x_4);
lean_inc(x_2);
x_6 = l_Lean_Name_str___override(x_2, x_3);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
uint8_t x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = 1;
lean_inc(x_1);
x_8 = l_Lean_Environment_setExporting(x_1, x_7);
x_9 = 0;
x_10 = l_Lean_Environment_find_x3f(x_8, x_2, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = l_Lean_mkPrivateName(x_1, x_6);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_ConstantInfo_hasValue(x_12, x_9);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_mkPrivateName(x_1, x_6);
lean_dec(x_1);
return x_14;
}
else
{
lean_dec(x_1);
return x_6;
}
}
}
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to declare `", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` because `", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has already been declared", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = l_Lean_MessageData_ofName(x_1);
x_7 = l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__2;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__4;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = 1;
x_12 = l_Lean_MessageData_ofConstName(x_2, x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__6;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___private_Lean_ReducibilityAttrs_0__Lean_validate___spec__3(x_15, x_3, x_4, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_6 = l_Lean_Name_str___override(x_1, x_2);
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
lean_inc(x_6);
x_13 = l_Lean_Environment_contains(x_11, x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; 
lean_free_object(x_7);
x_15 = l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2(x_1, x_6, x_3, x_4, x_10);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
lean_inc(x_6);
x_20 = l_Lean_Environment_contains(x_18, x_6, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2(x_1, x_6, x_3, x_4, x_17);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_eqUnfoldThmSuffix;
lean_inc(x_1);
x_6 = l_Lean_ensureReservedNameAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__1(x_1, x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_1);
x_9 = l_Lean_ensureReservedNameAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__1(x_1, x_8, x_2, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_eqn1ThmSuffix;
x_12 = l_Lean_ensureReservedNameAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__1(x_1, x_11, x_2, x_3, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ensureReservedNameAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_ensureEqnReservedNamesAvailable(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Lean_Meta_declFromEqLikeName(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
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
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____lambda__1___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____closed__1;
x_3 = l_Lean_registerReservedNamePredicate(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____lambda__1(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_717_(lean_object* x_1) {
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
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Meta_registerGetEqnsFn___lambda__1___closed__1;
x_5 = lean_st_ref_take(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_7);
lean_ctor_set(x_5, 0, x_1);
x_9 = lean_st_ref_set(x_4, x_5, x_8);
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
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_st_ref_set(x_4, x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to register equation getter, this kind of extension can only be registered during initialization", 103, 103);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_registerGetEqnsFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_registerGetEqnsFn___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_Meta_registerGetEqnsFn___closed__2;
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
x_10 = l_Lean_Meta_registerGetEqnsFn___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_registerGetEqnsFn___lambda__1(x_1, x_13, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetEqnsFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_registerGetEqnsFn___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = l_Lean_Environment_findAsync_x3f(x_11, x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_17 = lean_box(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_7);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_task_get_own(x_18);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Meta_isProp(x_20, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_21, 0);
lean_dec(x_33);
x_34 = lean_box(x_12);
lean_ctor_set(x_21, 0, x_34);
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_box(x_12);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_21);
if (x_38 == 0)
{
return x_21;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_21, 0);
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_21);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_42);
return x_7;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = 0;
x_47 = l_Lean_Environment_findAsync_x3f(x_45, x_1, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = lean_box(x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get_uint8(x_50, sizeof(void*)*3);
x_52 = lean_box(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_task_get_own(x_53);
x_55 = lean_ctor_get(x_54, 2);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_Meta_isProp(x_55, x_2, x_3, x_4, x_5, x_44);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
x_61 = 1;
x_62 = lean_box(x_61);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_65 = x_56;
} else {
 lean_dec_ref(x_56);
 x_65 = lean_box(0);
}
x_66 = lean_box(x_46);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_56, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_70 = x_56;
} else {
 lean_dec_ref(x_56);
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
lean_object* x_72; lean_object* x_73; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_box(x_46);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_44);
return x_73;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedEqnsExtState() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_markAsRecursive___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_markAsRecursive___closed__3;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982____closed__1;
x_4 = 1;
x_5 = l_Lean_registerEnvExtension___rarg(x_3, x_2, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = 0;
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_10, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 2);
lean_dec(x_14);
x_15 = lean_box(0);
lean_inc(x_13);
x_16 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_13, x_15);
x_17 = l_Lean_Expr_const___override(x_12, x_16);
x_18 = l_Lean_mkAppN(x_17, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_18);
x_19 = l_Lean_Meta_mkEq(x_18, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 0;
x_23 = 1;
x_24 = 1;
x_25 = l_Lean_Meta_mkForallFVars(x_3, x_20, x_22, x_23, x_24, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Lean_Meta_mkEqRefl(x_18, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_mkLambdaFVars(x_3, x_29, x_22, x_23, x_22, x_24, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_2);
lean_ctor_set(x_10, 2, x_26);
lean_ctor_set(x_10, 0, x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_15);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_addDecl(x_36, x_7, x_8, x_33);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
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
lean_dec(x_26);
lean_free_object(x_10);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
return x_28;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 0);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_28);
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
lean_free_object(x_10);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
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
lean_dec(x_18);
lean_free_object(x_10);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_19);
if (x_50 == 0)
{
return x_19;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_19, 0);
x_52 = lean_ctor_get(x_19, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_19);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_10, 0);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_10);
x_56 = lean_box(0);
lean_inc(x_55);
x_57 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_55, x_56);
x_58 = l_Lean_Expr_const___override(x_54, x_57);
x_59 = l_Lean_mkAppN(x_58, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_59);
x_60 = l_Lean_Meta_mkEq(x_59, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = 0;
x_64 = 1;
x_65 = 1;
x_66 = l_Lean_Meta_mkForallFVars(x_3, x_61, x_63, x_64, x_65, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_69 = l_Lean_Meta_mkEqRefl(x_59, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Meta_mkLambdaFVars(x_3, x_70, x_63, x_64, x_63, x_65, x_5, x_6, x_7, x_8, x_71);
lean_dec(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_2);
x_75 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_75, 0, x_2);
lean_ctor_set(x_75, 1, x_55);
lean_ctor_set(x_75, 2, x_67);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_2);
lean_ctor_set(x_76, 1, x_56);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_76);
x_78 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Lean_addDecl(x_78, x_7, x_8, x_74);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_80 = lean_ctor_get(x_72, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_82 = x_72;
} else {
 lean_dec_ref(x_72);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_67);
lean_dec(x_55);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_84 = lean_ctor_get(x_69, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_69, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_86 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_88 = lean_ctor_get(x_66, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_66, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_90 = x_66;
} else {
 lean_dec_ref(x_66);
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
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_92 = lean_ctor_get(x_60, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_60, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_94 = x_60;
} else {
 lean_dec_ref(x_60);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lambda__1___boxed), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = 1;
x_11 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1___rarg(x_8, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Lean_Environment_find_x3f(x_11, x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_5, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_1);
x_23 = l_Lean_Meta_mkEqLikeNameFor(x_21, x_1, x_22);
lean_inc(x_23);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize), 7, 2);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_17);
lean_inc(x_23);
x_25 = l_Lean_Meta_realizeConst(x_1, x_23, x_24, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_13, 0, x_23);
lean_ctor_set(x_25, 0, x_13);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_13, 0, x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_23);
lean_free_object(x_13);
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
lean_object* x_34; 
lean_free_object(x_13);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_box(0);
lean_ctor_set(x_7, 0, x_34);
return x_7;
}
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_13, 0);
lean_inc(x_35);
lean_dec(x_13);
if (lean_obj_tag(x_35) == 1)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_7);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_5, x_10);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_1);
x_42 = l_Lean_Meta_mkEqLikeNameFor(x_40, x_1, x_41);
lean_inc(x_42);
x_43 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize), 7, 2);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_36);
lean_inc(x_42);
x_44 = l_Lean_Meta_realizeConst(x_1, x_42, x_43, x_2, x_3, x_4, x_5, x_39);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_42);
x_49 = lean_ctor_get(x_44, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_51 = x_44;
} else {
 lean_dec_ref(x_44);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; 
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_box(0);
lean_ctor_set(x_7, 0, x_53);
return x_7;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = 0;
lean_inc(x_1);
x_58 = l_Lean_Environment_find_x3f(x_56, x_1, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_55);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
if (lean_obj_tag(x_61) == 1)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_st_ref_get(x_5, x_55);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_1);
x_69 = l_Lean_Meta_mkEqLikeNameFor(x_67, x_1, x_68);
lean_inc(x_69);
x_70 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize), 7, 2);
lean_closure_set(x_70, 0, x_69);
lean_closure_set(x_70, 1, x_63);
lean_inc(x_69);
x_71 = l_Lean_Meta_realizeConst(x_1, x_69, x_70, x_2, x_3, x_4, x_5, x_66);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_62;
}
lean_ctor_set(x_74, 0, x_69);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_69);
lean_dec(x_62);
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_78 = x_71;
} else {
 lean_dec_ref(x_71);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_55);
return x_81;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_isEqnThm_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_name_eq(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_name_eq(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_isEqnThm_x3f___spec__3(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_isEqnThm_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2(x_1, x_4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_isEqnThm_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_eqnsExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_eqnsExt;
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_11 = l_Lean_Meta_instInhabitedEqnsExtState;
x_12 = l_Lean_Meta_isEqnThm_x3f___closed__1;
x_13 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___rarg(x_11, x_12, x_8, x_10);
x_14 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_isEqnThm_x3f___spec__1(x_13, x_1);
lean_ctor_set(x_5, 0, x_14);
return x_5;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_eqnsExt;
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_20 = l_Lean_Meta_instInhabitedEqnsExtState;
x_21 = l_Lean_Meta_isEqnThm_x3f___closed__1;
x_22 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___rarg(x_20, x_21, x_17, x_19);
x_23 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_isEqnThm_x3f___spec__1(x_22, x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_isEqnThm_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_isEqnThm_x3f___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_isEqnThm_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_isEqnThm_x3f___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isEqnThm_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_isEqnThm___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_4);
x_14 = 1;
return x_14;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_isEqnThm___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_usize_shift_right(x_2, x_5);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_isEqnThm___spec__3(x_17, x_18, lean_box(0), x_19, x_3);
lean_dec(x_18);
lean_dec(x_17);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_Lean_Meta_isEqnThm___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_isEqnThm___spec__2(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_eqnsExt;
x_10 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_11 = l_Lean_Meta_instInhabitedEqnsExtState;
x_12 = l_Lean_Meta_isEqnThm_x3f___closed__1;
x_13 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___rarg(x_11, x_12, x_8, x_10);
x_14 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_isEqnThm___spec__1(x_13, x_1);
x_15 = lean_box(x_14);
lean_ctor_set(x_5, 0, x_15);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_5);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_eqnsExt;
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_21 = l_Lean_Meta_instInhabitedEqnsExtState;
x_22 = l_Lean_Meta_isEqnThm_x3f___closed__1;
x_23 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___rarg(x_21, x_22, x_18, x_20);
x_24 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_isEqnThm___spec__1(x_23, x_1);
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_isEqnThm___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_PersistentHashMap_containsAtAux___at_Lean_Meta_isEqnThm___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_isEqnThm___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at_Lean_Meta_isEqnThm___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_Lean_Meta_isEqnThm___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at_Lean_Meta_isEqnThm___spec__1(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isEqnThm___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_isEqnThm(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__3(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash___override(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__4(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__3(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__4(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__3(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_PersistentHashMap_insert___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__1(x_5, x_7, x_1);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_3;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__5(x_2, x_1, x_8, x_9, x_3);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_st_ref_take(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 5);
lean_dec(x_11);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_1);
x_13 = l_Lean_Meta_eqnsExt;
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
x_15 = l_Lean_Meta_isEqnThm_x3f___closed__1;
x_16 = l_Lean_EnvExtension_modifyState___rarg(x_15, x_10, x_12, x_14);
x_17 = l_Lean_Meta_markAsRecursive___closed__4;
lean_ctor_set(x_7, 5, x_17);
lean_ctor_set(x_7, 0, x_16);
x_18 = lean_st_ref_set(x_4, x_7, x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
x_27 = lean_ctor_get(x_7, 2);
x_28 = lean_ctor_get(x_7, 3);
x_29 = lean_ctor_get(x_7, 4);
x_30 = lean_ctor_get(x_7, 6);
x_31 = lean_ctor_get(x_7, 7);
x_32 = lean_ctor_get(x_7, 8);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___lambda__1___boxed), 3, 2);
lean_closure_set(x_33, 0, x_2);
lean_closure_set(x_33, 1, x_1);
x_34 = l_Lean_Meta_eqnsExt;
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*3);
x_36 = l_Lean_Meta_isEqnThm_x3f___closed__1;
x_37 = l_Lean_EnvExtension_modifyState___rarg(x_36, x_25, x_33, x_35);
x_38 = l_Lean_Meta_markAsRecursive___closed__4;
x_39 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_27);
lean_ctor_set(x_39, 3, x_28);
lean_ctor_set(x_39, 4, x_29);
lean_ctor_set(x_39, 5, x_38);
lean_ctor_set(x_39, 6, x_30);
lean_ctor_set(x_39, 7, x_31);
lean_ctor_set(x_39, 8, x_32);
x_40 = lean_st_ref_set(x_4, x_39, x_8);
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
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__3(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__5(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___lambda__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5;
x_2 = l_Lean_Meta_eqnThmSuffixBasePrefix;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
lean_inc(x_11);
x_12 = l_Nat_reprFast(x_11);
x_13 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5;
x_16 = lean_string_append(x_14, x_15);
lean_inc(x_1);
lean_inc(x_2);
x_17 = l_Lean_Meta_mkEqLikeNameFor(x_2, x_1, x_16);
lean_inc(x_2);
x_18 = l_Lean_Environment_containsOnBranch(x_2, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_array_push(x_4, x_17);
x_3 = x_11;
x_4 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_eqn1ThmSuffix;
lean_inc(x_1);
lean_inc(x_11);
x_13 = l_Lean_Meta_mkEqLikeNameFor(x_11, x_1, x_12);
x_14 = 1;
lean_inc(x_13);
lean_inc(x_11);
x_15 = l_Lean_Environment_contains(x_11, x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_1);
x_16 = lean_box(0);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_free_object(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_mk(x_18);
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_21 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(x_1, x_11, x_20, x_19, x_2, x_3, x_4, x_5, x_10);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(x_1, x_22, x_4, x_5, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_eqn1ThmSuffix;
lean_inc(x_1);
lean_inc(x_33);
x_35 = l_Lean_Meta_mkEqLikeNameFor(x_33, x_1, x_34);
x_36 = 1;
lean_inc(x_35);
lean_inc(x_33);
x_37 = l_Lean_Environment_contains(x_33, x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_mk(x_41);
x_43 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_44 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop(x_1, x_33, x_43, x_42, x_2, x_3, x_4, x_5, x_32);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_45);
x_47 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(x_1, x_45, x_4, x_5, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_45);
if (lean_is_scalar(x_49)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_49;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_18 = lean_apply_6(x_16, x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_free_object(x_6);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_4);
{
lean_object* _tmp_5 = x_17;
lean_object* _tmp_6 = x_4;
lean_object* _tmp_7 = lean_box(0);
lean_object* _tmp_12 = x_20;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(x_1, x_24, x_11, x_12, x_22);
lean_dec(x_12);
lean_dec(x_11);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_19);
x_29 = lean_box(0);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_29);
lean_ctor_set(x_6, 0, x_28);
lean_ctor_set(x_25, 0, x_6);
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_19);
x_32 = lean_box(0);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_32);
lean_ctor_set(x_6, 0, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
lean_dec(x_19);
lean_inc(x_34);
x_35 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(x_1, x_34, x_11, x_12, x_22);
lean_dec(x_12);
lean_dec(x_11);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_box(0);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_40);
lean_ctor_set(x_6, 0, x_39);
if (lean_is_scalar(x_37)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_37;
}
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_18);
if (x_42 == 0)
{
return x_18;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_18, 0);
x_44 = lean_ctor_get(x_18, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_18);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_48 = lean_apply_6(x_46, x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_4);
{
lean_object* _tmp_5 = x_47;
lean_object* _tmp_6 = x_4;
lean_object* _tmp_7 = lean_box(0);
lean_object* _tmp_12 = x_50;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_54 = x_49;
} else {
 lean_dec_ref(x_49);
 x_54 = lean_box(0);
}
lean_inc(x_53);
x_55 = l___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms(x_1, x_53, x_11, x_12, x_52);
lean_dec(x_12);
lean_dec(x_11);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_54;
}
lean_ctor_set(x_58, 0, x_53);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_63 = lean_ctor_get(x_48, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_65 = x_48;
} else {
 lean_dec_ref(x_48);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_Meta_registerGetEqnsFn___lambda__1___closed__1;
x_9 = lean_st_ref_get(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_declFromEqLikeName___closed__3;
lean_inc(x_10);
x_15 = l_List_forIn_x27_loop___at___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___spec__1(x_1, x_10, x_12, x_14, x_10, x_10, x_14, lean_box(0), x_3, x_4, x_5, x_6, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
}
else
{
uint8_t x_28; 
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_8, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_8, 0, x_17);
return x_8;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_20 = x_9;
} else {
 lean_dec_ref(x_9);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(1, 1, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__3(x_1, x_17, x_2, x_3, x_4, x_5, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__2;
x_3 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__1;
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
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_markAsRecursive___closed__3;
x_3 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__4), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4;
x_9 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5;
x_10 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore___spec__2___rarg(x_8, x_9, x_7, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getEqnsFor_x3f___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_9 = l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(x_4, x_6, x_8);
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
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_dec(x_12);
x_13 = l_Lean_Meta_getEqnsFor_x3f___lambda__1___closed__1;
x_14 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_13);
lean_ctor_set(x_7, 4, x_14);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*13, x_2);
x_15 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(x_3, x_4, x_5, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
x_18 = lean_ctor_get(x_7, 3);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get(x_7, 11);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_27 = lean_ctor_get(x_7, 12);
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
lean_dec(x_7);
x_28 = l_Lean_Meta_getEqnsFor_x3f___lambda__1___closed__1;
x_29 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_28);
x_30 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_1);
lean_ctor_set(x_30, 3, x_18);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_19);
lean_ctor_set(x_30, 6, x_20);
lean_ctor_set(x_30, 7, x_21);
lean_ctor_set(x_30, 8, x_22);
lean_ctor_set(x_30, 9, x_23);
lean_ctor_set(x_30, 10, x_24);
lean_ctor_set(x_30, 11, x_25);
lean_ctor_set(x_30, 12, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_30, sizeof(void*)*13 + 1, x_26);
x_31 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(x_3, x_4, x_5, x_30, x_8, x_9);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_eqnAffectingOptions;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__1;
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint8_t _init_l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__1;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__5() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__1;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_71; 
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
x_9 = lean_st_ref_get(x_6, x_7);
x_71 = l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__2;
if (x_71 == 0)
{
x_10 = x_8;
goto block_70;
}
else
{
uint8_t x_72; 
x_72 = l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__4;
if (x_72 == 0)
{
x_10 = x_8;
goto block_70;
}
else
{
size_t x_73; lean_object* x_74; size_t x_75; lean_object* x_76; 
x_73 = 0;
x_74 = l_Lean_Meta_eqnAffectingOptions;
x_75 = l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__5;
x_76 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getEqnsFor_x3f___spec__1(x_74, x_73, x_75, x_8);
x_10 = x_76;
goto block_70;
}
}
block_70:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_63; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__3;
x_14 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_10, x_13);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_63 = l_Lean_Kernel_isDiagnosticsEnabled(x_15);
lean_dec(x_15);
if (x_63 == 0)
{
if (x_14 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
x_64 = lean_box(0);
x_65 = l_Lean_Meta_getEqnsFor_x3f___lambda__1(x_10, x_14, x_1, x_3, x_4, x_64, x_5, x_6, x_12);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_box(0);
x_16 = x_66;
goto block_62;
}
}
else
{
if (x_14 == 0)
{
lean_object* x_67; 
x_67 = lean_box(0);
x_16 = x_67;
goto block_62;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_2);
x_68 = lean_box(0);
x_69 = l_Lean_Meta_getEqnsFor_x3f___lambda__1(x_10, x_14, x_1, x_3, x_4, x_68, x_5, x_6, x_12);
return x_69;
}
}
block_62:
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_16);
x_17 = lean_st_ref_take(x_6, x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 5);
lean_dec(x_23);
x_24 = l_Lean_Kernel_enableDiag(x_22, x_14);
lean_inc(x_2);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_19, 5, x_17);
lean_ctor_set(x_19, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_19, x_21);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Meta_getEqnsFor_x3f___lambda__1(x_10, x_14, x_1, x_3, x_4, x_27, x_5, x_6, x_26);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_17, 1);
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
x_32 = lean_ctor_get(x_19, 2);
x_33 = lean_ctor_get(x_19, 3);
x_34 = lean_ctor_get(x_19, 4);
x_35 = lean_ctor_get(x_19, 6);
x_36 = lean_ctor_get(x_19, 7);
x_37 = lean_ctor_get(x_19, 8);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_38 = l_Lean_Kernel_enableDiag(x_30, x_14);
lean_inc(x_2);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 0, x_2);
x_39 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_33);
lean_ctor_set(x_39, 4, x_34);
lean_ctor_set(x_39, 5, x_17);
lean_ctor_set(x_39, 6, x_35);
lean_ctor_set(x_39, 7, x_36);
lean_ctor_set(x_39, 8, x_37);
x_40 = lean_st_ref_set(x_6, x_39, x_29);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_box(0);
x_43 = l_Lean_Meta_getEqnsFor_x3f___lambda__1(x_10, x_14, x_1, x_3, x_4, x_42, x_5, x_6, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_44 = lean_ctor_get(x_17, 0);
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_17);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 4);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 6);
lean_inc(x_51);
x_52 = lean_ctor_get(x_44, 7);
lean_inc(x_52);
x_53 = lean_ctor_get(x_44, 8);
lean_inc(x_53);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 lean_ctor_release(x_44, 4);
 lean_ctor_release(x_44, 5);
 lean_ctor_release(x_44, 6);
 lean_ctor_release(x_44, 7);
 lean_ctor_release(x_44, 8);
 x_54 = x_44;
} else {
 lean_dec_ref(x_44);
 x_54 = lean_box(0);
}
x_55 = l_Lean_Kernel_enableDiag(x_46, x_14);
lean_inc(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_2);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 9, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_47);
lean_ctor_set(x_57, 2, x_48);
lean_ctor_set(x_57, 3, x_49);
lean_ctor_set(x_57, 4, x_50);
lean_ctor_set(x_57, 5, x_56);
lean_ctor_set(x_57, 6, x_51);
lean_ctor_set(x_57, 7, x_52);
lean_ctor_set(x_57, 8, x_53);
x_58 = lean_st_ref_set(x_6, x_57, x_45);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_box(0);
x_61 = l_Lean_Meta_getEqnsFor_x3f___lambda__1(x_10, x_14, x_1, x_3, x_4, x_60, x_5, x_6, x_59);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_Meta_markAsRecursive___closed__3;
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_getEqnsFor_x3f___lambda__2), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4;
x_10 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5;
x_11 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore___spec__2___rarg(x_9, x_10, x_8, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_getEqnsFor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_getEqnsFor_x3f___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getEqnsFor_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_getEqnsFor_x3f___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Meta_generateEagerEqns___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unbox(x_8);
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
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
else
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
goto _start;
}
}
}
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
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
x_1 = l_Lean_Meta_generateEagerEqns___closed__1;
x_2 = l_Lean_Meta_generateEagerEqns___closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
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
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__2;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; size_t x_11; lean_object* x_12; size_t x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = 0;
x_12 = l_Lean_Meta_eqnAffectingOptions;
x_13 = l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__5;
x_14 = l_Array_anyMUnsafe_any___at_Lean_Meta_generateEagerEqns___spec__1(x_10, x_12, x_11, x_13);
lean_dec(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = l_Lean_Meta_generateEagerEqns___closed__3;
x_18 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_17, x_2, x_3, x_4, x_5, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_generateEagerEqns___lambda__1(x_1, x_22, x_2, x_3, x_4, x_5, x_21);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_18, 1);
x_26 = lean_ctor_get(x_18, 0);
lean_dec(x_26);
lean_inc(x_1);
x_27 = l_Lean_MessageData_ofName(x_1);
x_28 = l_Lean_Meta_generateEagerEqns___closed__5;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_27);
lean_ctor_set(x_18, 0, x_28);
x_29 = l_Lean_Meta_generateEagerEqns___closed__6;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_18);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_17, x_30, x_2, x_3, x_4, x_5, x_25);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Meta_generateEagerEqns___lambda__1(x_1, x_32, x_2, x_3, x_4, x_5, x_33);
lean_dec(x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_dec(x_18);
lean_inc(x_1);
x_36 = l_Lean_MessageData_ofName(x_1);
x_37 = l_Lean_Meta_generateEagerEqns___closed__5;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Meta_generateEagerEqns___closed__6;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_17, x_40, x_2, x_3, x_4, x_5, x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_generateEagerEqns___lambda__1(x_1, x_42, x_2, x_3, x_4, x_5, x_43);
lean_dec(x_42);
return x_44;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_generateEagerEqns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Meta_generateEagerEqns___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_generateEagerEqns___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_generateEagerEqns___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2160_(lean_object* x_1) {
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
static lean_object* _init_l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1___closed__1;
x_5 = lean_st_ref_take(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 1, x_7);
lean_ctor_set(x_5, 0, x_1);
x_9 = lean_st_ref_set(x_4, x_5, x_8);
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
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_st_ref_set(x_4, x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
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
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_Meta_registerGetEqnsFn___closed__2;
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
x_10 = l_Lean_Meta_registerGetEqnsFn___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1(x_1, x_13, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_7);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_18 = lean_apply_6(x_16, x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_free_object(x_6);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_4);
{
lean_object* _tmp_5 = x_17;
lean_object* _tmp_6 = x_4;
lean_object* _tmp_7 = lean_box(0);
lean_object* _tmp_12 = x_20;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_19);
x_26 = lean_box(0);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_25);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(0);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_30);
lean_ctor_set(x_6, 0, x_29);
lean_ctor_set(x_18, 0, x_6);
return x_18;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_33 = x_19;
} else {
 lean_dec_ref(x_19);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_box(0);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_36);
lean_ctor_set(x_6, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_6);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_44 = lean_apply_6(x_42, x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_4);
{
lean_object* _tmp_5 = x_43;
lean_object* _tmp_6 = x_4;
lean_object* _tmp_7 = lean_box(0);
lean_object* _tmp_12 = x_46;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_43);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_49 = x_44;
} else {
 lean_dec_ref(x_44);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_45, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
if (lean_is_scalar(x_49)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_49;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_48);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_43);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_59 = x_44;
} else {
 lean_dec_ref(x_44);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
}
}
static lean_object* _init_l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_markAsRecursive___closed__3;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_st_ref_get(x_5, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*8);
lean_dec(x_23);
x_25 = lean_st_ref_take(x_5, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 5);
lean_dec(x_30);
x_31 = 0;
x_32 = l_Lean_Environment_setExporting(x_29, x_31);
x_33 = l_Lean_Meta_markAsRecursive___closed__4;
lean_ctor_set(x_26, 5, x_33);
lean_ctor_set(x_26, 0, x_32);
x_34 = lean_st_ref_set(x_5, x_26, x_27);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_take(x_3, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_37, 1);
lean_dec(x_40);
x_41 = l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2___closed__1;
lean_ctor_set(x_37, 1, x_41);
x_42 = lean_st_ref_set(x_3, x_37, x_38);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_5);
lean_inc(x_3);
x_44 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_take(x_5, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_ctor_get(x_48, 5);
lean_dec(x_52);
x_53 = l_Lean_Environment_setExporting(x_51, x_24);
lean_ctor_set(x_48, 5, x_33);
lean_ctor_set(x_48, 0, x_53);
x_54 = lean_st_ref_set(x_5, x_48, x_49);
lean_dec(x_5);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_3, x_55);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_56, 1);
x_61 = lean_ctor_get(x_58, 1);
lean_dec(x_61);
lean_ctor_set(x_58, 1, x_41);
x_62 = lean_st_ref_set(x_3, x_58, x_60);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
x_65 = lean_box(0);
lean_ctor_set(x_56, 1, x_65);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_62, 0, x_56);
x_7 = x_62;
goto block_19;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_box(0);
lean_ctor_set(x_56, 1, x_67);
lean_ctor_set(x_56, 0, x_45);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_56);
lean_ctor_set(x_68, 1, x_66);
x_7 = x_68;
goto block_19;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_69 = lean_ctor_get(x_56, 1);
x_70 = lean_ctor_get(x_58, 0);
x_71 = lean_ctor_get(x_58, 2);
x_72 = lean_ctor_get(x_58, 3);
x_73 = lean_ctor_get(x_58, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_58);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_41);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_73);
x_75 = lean_st_ref_set(x_3, x_74, x_69);
lean_dec(x_3);
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
lean_ctor_set(x_56, 1, x_78);
lean_ctor_set(x_56, 0, x_45);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_56);
lean_ctor_set(x_79, 1, x_76);
x_7 = x_79;
goto block_19;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_80 = lean_ctor_get(x_56, 0);
x_81 = lean_ctor_get(x_56, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_56);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 2);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 3);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 4);
lean_inc(x_85);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 lean_ctor_release(x_80, 2);
 lean_ctor_release(x_80, 3);
 lean_ctor_release(x_80, 4);
 x_86 = x_80;
} else {
 lean_dec_ref(x_80);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 5, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_41);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_84);
lean_ctor_set(x_87, 4, x_85);
x_88 = lean_st_ref_set(x_3, x_87, x_81);
lean_dec(x_3);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_45);
lean_ctor_set(x_92, 1, x_91);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_89);
x_7 = x_93;
goto block_19;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_94 = lean_ctor_get(x_48, 0);
x_95 = lean_ctor_get(x_48, 1);
x_96 = lean_ctor_get(x_48, 2);
x_97 = lean_ctor_get(x_48, 3);
x_98 = lean_ctor_get(x_48, 4);
x_99 = lean_ctor_get(x_48, 6);
x_100 = lean_ctor_get(x_48, 7);
x_101 = lean_ctor_get(x_48, 8);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_48);
x_102 = l_Lean_Environment_setExporting(x_94, x_24);
x_103 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_95);
lean_ctor_set(x_103, 2, x_96);
lean_ctor_set(x_103, 3, x_97);
lean_ctor_set(x_103, 4, x_98);
lean_ctor_set(x_103, 5, x_33);
lean_ctor_set(x_103, 6, x_99);
lean_ctor_set(x_103, 7, x_100);
lean_ctor_set(x_103, 8, x_101);
x_104 = lean_st_ref_set(x_5, x_103, x_49);
lean_dec(x_5);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_st_ref_take(x_3, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 3);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 4);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 lean_ctor_release(x_107, 4);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 5, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_41);
lean_ctor_set(x_115, 2, x_111);
lean_ctor_set(x_115, 3, x_112);
lean_ctor_set(x_115, 4, x_113);
x_116 = lean_st_ref_set(x_3, x_115, x_108);
lean_dec(x_3);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_109;
}
lean_ctor_set(x_120, 0, x_45);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_117);
x_7 = x_121;
goto block_19;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_44, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_44, 1);
lean_inc(x_123);
lean_dec(x_44);
x_124 = lean_st_ref_take(x_5, x_123);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = !lean_is_exclusive(x_125);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_128 = lean_ctor_get(x_125, 0);
x_129 = lean_ctor_get(x_125, 5);
lean_dec(x_129);
x_130 = l_Lean_Environment_setExporting(x_128, x_24);
lean_ctor_set(x_125, 5, x_33);
lean_ctor_set(x_125, 0, x_130);
x_131 = lean_st_ref_set(x_5, x_125, x_126);
lean_dec(x_5);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_st_ref_take(x_3, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_134, 1);
lean_dec(x_137);
lean_ctor_set(x_134, 1, x_41);
x_138 = lean_st_ref_set(x_3, x_134, x_135);
lean_dec(x_3);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
lean_ctor_set_tag(x_138, 1);
lean_ctor_set(x_138, 0, x_122);
x_7 = x_138;
goto block_19;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_122);
lean_ctor_set(x_142, 1, x_141);
x_7 = x_142;
goto block_19;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_134, 0);
x_144 = lean_ctor_get(x_134, 2);
x_145 = lean_ctor_get(x_134, 3);
x_146 = lean_ctor_get(x_134, 4);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_134);
x_147 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_41);
lean_ctor_set(x_147, 2, x_144);
lean_ctor_set(x_147, 3, x_145);
lean_ctor_set(x_147, 4, x_146);
x_148 = lean_st_ref_set(x_3, x_147, x_135);
lean_dec(x_3);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_122);
lean_ctor_set(x_151, 1, x_149);
x_7 = x_151;
goto block_19;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_152 = lean_ctor_get(x_125, 0);
x_153 = lean_ctor_get(x_125, 1);
x_154 = lean_ctor_get(x_125, 2);
x_155 = lean_ctor_get(x_125, 3);
x_156 = lean_ctor_get(x_125, 4);
x_157 = lean_ctor_get(x_125, 6);
x_158 = lean_ctor_get(x_125, 7);
x_159 = lean_ctor_get(x_125, 8);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_125);
x_160 = l_Lean_Environment_setExporting(x_152, x_24);
x_161 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_153);
lean_ctor_set(x_161, 2, x_154);
lean_ctor_set(x_161, 3, x_155);
lean_ctor_set(x_161, 4, x_156);
lean_ctor_set(x_161, 5, x_33);
lean_ctor_set(x_161, 6, x_157);
lean_ctor_set(x_161, 7, x_158);
lean_ctor_set(x_161, 8, x_159);
x_162 = lean_st_ref_set(x_5, x_161, x_126);
lean_dec(x_5);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_164 = lean_st_ref_take(x_3, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_165, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_165, 4);
lean_inc(x_170);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 lean_ctor_release(x_165, 2);
 lean_ctor_release(x_165, 3);
 lean_ctor_release(x_165, 4);
 x_171 = x_165;
} else {
 lean_dec_ref(x_165);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 5, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_167);
lean_ctor_set(x_172, 1, x_41);
lean_ctor_set(x_172, 2, x_168);
lean_ctor_set(x_172, 3, x_169);
lean_ctor_set(x_172, 4, x_170);
x_173 = lean_st_ref_set(x_3, x_172, x_166);
lean_dec(x_3);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
 lean_ctor_set_tag(x_176, 1);
}
lean_ctor_set(x_176, 0, x_122);
lean_ctor_set(x_176, 1, x_174);
x_7 = x_176;
goto block_19;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_177 = lean_ctor_get(x_37, 0);
x_178 = lean_ctor_get(x_37, 2);
x_179 = lean_ctor_get(x_37, 3);
x_180 = lean_ctor_get(x_37, 4);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_37);
x_181 = l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2___closed__1;
x_182 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_182, 0, x_177);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_182, 2, x_178);
lean_ctor_set(x_182, 3, x_179);
lean_ctor_set(x_182, 4, x_180);
x_183 = lean_st_ref_set(x_3, x_182, x_38);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
lean_inc(x_5);
lean_inc(x_3);
x_185 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_st_ref_take(x_5, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_189, 2);
lean_inc(x_193);
x_194 = lean_ctor_get(x_189, 3);
lean_inc(x_194);
x_195 = lean_ctor_get(x_189, 4);
lean_inc(x_195);
x_196 = lean_ctor_get(x_189, 6);
lean_inc(x_196);
x_197 = lean_ctor_get(x_189, 7);
lean_inc(x_197);
x_198 = lean_ctor_get(x_189, 8);
lean_inc(x_198);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 lean_ctor_release(x_189, 5);
 lean_ctor_release(x_189, 6);
 lean_ctor_release(x_189, 7);
 lean_ctor_release(x_189, 8);
 x_199 = x_189;
} else {
 lean_dec_ref(x_189);
 x_199 = lean_box(0);
}
x_200 = l_Lean_Environment_setExporting(x_191, x_24);
if (lean_is_scalar(x_199)) {
 x_201 = lean_alloc_ctor(0, 9, 0);
} else {
 x_201 = x_199;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_192);
lean_ctor_set(x_201, 2, x_193);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set(x_201, 4, x_195);
lean_ctor_set(x_201, 5, x_33);
lean_ctor_set(x_201, 6, x_196);
lean_ctor_set(x_201, 7, x_197);
lean_ctor_set(x_201, 8, x_198);
x_202 = lean_st_ref_set(x_5, x_201, x_190);
lean_dec(x_5);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = lean_st_ref_take(x_3, x_203);
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
x_209 = lean_ctor_get(x_205, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_205, 3);
lean_inc(x_210);
x_211 = lean_ctor_get(x_205, 4);
lean_inc(x_211);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 lean_ctor_release(x_205, 4);
 x_212 = x_205;
} else {
 lean_dec_ref(x_205);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(0, 5, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_208);
lean_ctor_set(x_213, 1, x_181);
lean_ctor_set(x_213, 2, x_209);
lean_ctor_set(x_213, 3, x_210);
lean_ctor_set(x_213, 4, x_211);
x_214 = lean_st_ref_set(x_3, x_213, x_206);
lean_dec(x_3);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
x_217 = lean_box(0);
if (lean_is_scalar(x_207)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_207;
}
lean_ctor_set(x_218, 0, x_186);
lean_ctor_set(x_218, 1, x_217);
if (lean_is_scalar(x_216)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_216;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_215);
x_7 = x_219;
goto block_19;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_220 = lean_ctor_get(x_185, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_185, 1);
lean_inc(x_221);
lean_dec(x_185);
x_222 = lean_st_ref_take(x_5, x_221);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_ctor_get(x_223, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_223, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_223, 3);
lean_inc(x_228);
x_229 = lean_ctor_get(x_223, 4);
lean_inc(x_229);
x_230 = lean_ctor_get(x_223, 6);
lean_inc(x_230);
x_231 = lean_ctor_get(x_223, 7);
lean_inc(x_231);
x_232 = lean_ctor_get(x_223, 8);
lean_inc(x_232);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 lean_ctor_release(x_223, 2);
 lean_ctor_release(x_223, 3);
 lean_ctor_release(x_223, 4);
 lean_ctor_release(x_223, 5);
 lean_ctor_release(x_223, 6);
 lean_ctor_release(x_223, 7);
 lean_ctor_release(x_223, 8);
 x_233 = x_223;
} else {
 lean_dec_ref(x_223);
 x_233 = lean_box(0);
}
x_234 = l_Lean_Environment_setExporting(x_225, x_24);
if (lean_is_scalar(x_233)) {
 x_235 = lean_alloc_ctor(0, 9, 0);
} else {
 x_235 = x_233;
}
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_226);
lean_ctor_set(x_235, 2, x_227);
lean_ctor_set(x_235, 3, x_228);
lean_ctor_set(x_235, 4, x_229);
lean_ctor_set(x_235, 5, x_33);
lean_ctor_set(x_235, 6, x_230);
lean_ctor_set(x_235, 7, x_231);
lean_ctor_set(x_235, 8, x_232);
x_236 = lean_st_ref_set(x_5, x_235, x_224);
lean_dec(x_5);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_st_ref_take(x_3, x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_ctor_get(x_239, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_239, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_239, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_239, 4);
lean_inc(x_244);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 lean_ctor_release(x_239, 2);
 lean_ctor_release(x_239, 3);
 lean_ctor_release(x_239, 4);
 x_245 = x_239;
} else {
 lean_dec_ref(x_239);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(0, 5, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_241);
lean_ctor_set(x_246, 1, x_181);
lean_ctor_set(x_246, 2, x_242);
lean_ctor_set(x_246, 3, x_243);
lean_ctor_set(x_246, 4, x_244);
x_247 = lean_st_ref_set(x_3, x_246, x_240);
lean_dec(x_3);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_249 = x_247;
} else {
 lean_dec_ref(x_247);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
 lean_ctor_set_tag(x_250, 1);
}
lean_ctor_set(x_250, 0, x_220);
lean_ctor_set(x_250, 1, x_248);
x_7 = x_250;
goto block_19;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_251 = lean_ctor_get(x_26, 0);
x_252 = lean_ctor_get(x_26, 1);
x_253 = lean_ctor_get(x_26, 2);
x_254 = lean_ctor_get(x_26, 3);
x_255 = lean_ctor_get(x_26, 4);
x_256 = lean_ctor_get(x_26, 6);
x_257 = lean_ctor_get(x_26, 7);
x_258 = lean_ctor_get(x_26, 8);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_26);
x_259 = 0;
x_260 = l_Lean_Environment_setExporting(x_251, x_259);
x_261 = l_Lean_Meta_markAsRecursive___closed__4;
x_262 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_252);
lean_ctor_set(x_262, 2, x_253);
lean_ctor_set(x_262, 3, x_254);
lean_ctor_set(x_262, 4, x_255);
lean_ctor_set(x_262, 5, x_261);
lean_ctor_set(x_262, 6, x_256);
lean_ctor_set(x_262, 7, x_257);
lean_ctor_set(x_262, 8, x_258);
x_263 = lean_st_ref_set(x_5, x_262, x_27);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_265 = lean_st_ref_take(x_3, x_264);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 2);
lean_inc(x_269);
x_270 = lean_ctor_get(x_266, 3);
lean_inc(x_270);
x_271 = lean_ctor_get(x_266, 4);
lean_inc(x_271);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 lean_ctor_release(x_266, 2);
 lean_ctor_release(x_266, 3);
 lean_ctor_release(x_266, 4);
 x_272 = x_266;
} else {
 lean_dec_ref(x_266);
 x_272 = lean_box(0);
}
x_273 = l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2___closed__1;
if (lean_is_scalar(x_272)) {
 x_274 = lean_alloc_ctor(0, 5, 0);
} else {
 x_274 = x_272;
}
lean_ctor_set(x_274, 0, x_268);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set(x_274, 2, x_269);
lean_ctor_set(x_274, 3, x_270);
lean_ctor_set(x_274, 4, x_271);
x_275 = lean_st_ref_set(x_3, x_274, x_267);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
lean_inc(x_5);
lean_inc(x_3);
x_277 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_276);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_st_ref_take(x_5, x_279);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_ctor_get(x_281, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_281, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_281, 3);
lean_inc(x_286);
x_287 = lean_ctor_get(x_281, 4);
lean_inc(x_287);
x_288 = lean_ctor_get(x_281, 6);
lean_inc(x_288);
x_289 = lean_ctor_get(x_281, 7);
lean_inc(x_289);
x_290 = lean_ctor_get(x_281, 8);
lean_inc(x_290);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 lean_ctor_release(x_281, 2);
 lean_ctor_release(x_281, 3);
 lean_ctor_release(x_281, 4);
 lean_ctor_release(x_281, 5);
 lean_ctor_release(x_281, 6);
 lean_ctor_release(x_281, 7);
 lean_ctor_release(x_281, 8);
 x_291 = x_281;
} else {
 lean_dec_ref(x_281);
 x_291 = lean_box(0);
}
x_292 = l_Lean_Environment_setExporting(x_283, x_24);
if (lean_is_scalar(x_291)) {
 x_293 = lean_alloc_ctor(0, 9, 0);
} else {
 x_293 = x_291;
}
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_284);
lean_ctor_set(x_293, 2, x_285);
lean_ctor_set(x_293, 3, x_286);
lean_ctor_set(x_293, 4, x_287);
lean_ctor_set(x_293, 5, x_261);
lean_ctor_set(x_293, 6, x_288);
lean_ctor_set(x_293, 7, x_289);
lean_ctor_set(x_293, 8, x_290);
x_294 = lean_st_ref_set(x_5, x_293, x_282);
lean_dec(x_5);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_st_ref_take(x_3, x_295);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_299 = x_296;
} else {
 lean_dec_ref(x_296);
 x_299 = lean_box(0);
}
x_300 = lean_ctor_get(x_297, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_297, 2);
lean_inc(x_301);
x_302 = lean_ctor_get(x_297, 3);
lean_inc(x_302);
x_303 = lean_ctor_get(x_297, 4);
lean_inc(x_303);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 lean_ctor_release(x_297, 2);
 lean_ctor_release(x_297, 3);
 lean_ctor_release(x_297, 4);
 x_304 = x_297;
} else {
 lean_dec_ref(x_297);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(0, 5, 0);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_300);
lean_ctor_set(x_305, 1, x_273);
lean_ctor_set(x_305, 2, x_301);
lean_ctor_set(x_305, 3, x_302);
lean_ctor_set(x_305, 4, x_303);
x_306 = lean_st_ref_set(x_3, x_305, x_298);
lean_dec(x_3);
x_307 = lean_ctor_get(x_306, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_308 = x_306;
} else {
 lean_dec_ref(x_306);
 x_308 = lean_box(0);
}
x_309 = lean_box(0);
if (lean_is_scalar(x_299)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_299;
}
lean_ctor_set(x_310, 0, x_278);
lean_ctor_set(x_310, 1, x_309);
if (lean_is_scalar(x_308)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_308;
}
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_307);
x_7 = x_311;
goto block_19;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_312 = lean_ctor_get(x_277, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_277, 1);
lean_inc(x_313);
lean_dec(x_277);
x_314 = lean_st_ref_take(x_5, x_313);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_315, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_315, 2);
lean_inc(x_319);
x_320 = lean_ctor_get(x_315, 3);
lean_inc(x_320);
x_321 = lean_ctor_get(x_315, 4);
lean_inc(x_321);
x_322 = lean_ctor_get(x_315, 6);
lean_inc(x_322);
x_323 = lean_ctor_get(x_315, 7);
lean_inc(x_323);
x_324 = lean_ctor_get(x_315, 8);
lean_inc(x_324);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 lean_ctor_release(x_315, 2);
 lean_ctor_release(x_315, 3);
 lean_ctor_release(x_315, 4);
 lean_ctor_release(x_315, 5);
 lean_ctor_release(x_315, 6);
 lean_ctor_release(x_315, 7);
 lean_ctor_release(x_315, 8);
 x_325 = x_315;
} else {
 lean_dec_ref(x_315);
 x_325 = lean_box(0);
}
x_326 = l_Lean_Environment_setExporting(x_317, x_24);
if (lean_is_scalar(x_325)) {
 x_327 = lean_alloc_ctor(0, 9, 0);
} else {
 x_327 = x_325;
}
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_318);
lean_ctor_set(x_327, 2, x_319);
lean_ctor_set(x_327, 3, x_320);
lean_ctor_set(x_327, 4, x_321);
lean_ctor_set(x_327, 5, x_261);
lean_ctor_set(x_327, 6, x_322);
lean_ctor_set(x_327, 7, x_323);
lean_ctor_set(x_327, 8, x_324);
x_328 = lean_st_ref_set(x_5, x_327, x_316);
lean_dec(x_5);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = lean_st_ref_take(x_3, x_329);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_ctor_get(x_331, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_331, 2);
lean_inc(x_334);
x_335 = lean_ctor_get(x_331, 3);
lean_inc(x_335);
x_336 = lean_ctor_get(x_331, 4);
lean_inc(x_336);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 lean_ctor_release(x_331, 2);
 lean_ctor_release(x_331, 3);
 lean_ctor_release(x_331, 4);
 x_337 = x_331;
} else {
 lean_dec_ref(x_331);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(0, 5, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_273);
lean_ctor_set(x_338, 2, x_334);
lean_ctor_set(x_338, 3, x_335);
lean_ctor_set(x_338, 4, x_336);
x_339 = lean_st_ref_set(x_3, x_338, x_332);
lean_dec(x_3);
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_341 = x_339;
} else {
 lean_dec_ref(x_339);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 2, 0);
} else {
 x_342 = x_341;
 lean_ctor_set_tag(x_342, 1);
}
lean_ctor_set(x_342, 0, x_312);
lean_ctor_set(x_342, 1, x_340);
x_7 = x_342;
goto block_19;
}
}
block_19:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_Eqns_0__Lean_Meta_shouldGenerateEqnThms(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2___closed__1;
x_13 = lean_unbox(x_10);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_apply_6(x_12, x_14, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_1);
x_16 = l_Lean_Meta_isRecursiveDefinition(x_1, x_6, x_7, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
if (x_2 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = lean_apply_6(x_12, x_20, x_4, x_5, x_6, x_7, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = l___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm(x_1, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
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
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_dec(x_16);
x_33 = l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1___closed__1;
x_34 = lean_st_ref_get(x_33, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = l_Lean_Meta_declFromEqLikeName___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_35);
x_39 = l_List_forIn_x27_loop___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__1(x_1, x_35, x_37, x_38, x_35, x_35, x_38, lean_box(0), x_4, x_5, x_6, x_7, x_36);
lean_dec(x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = lean_apply_6(x_12, x_43, x_4, x_5, x_6, x_7, x_42);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_39);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_39, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_47);
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_9, 0);
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_9);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
lean_inc(x_3);
x_15 = l_Lean_Environment_contains(x_13, x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_9);
lean_dec(x_3);
x_16 = lean_box(0);
x_17 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_12);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_9);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
lean_inc(x_3);
x_23 = l_Lean_Environment_contains(x_21, x_3, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2(x_1, x_2, x_24, x_4, x_5, x_6, x_7, x_20);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_3);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
}
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid unfold theorem name `", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has been generated expected `", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_1);
x_14 = l_Lean_Meta_mkEqLikeNameFor(x_12, x_1, x_13);
x_15 = lean_box(x_2);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__3___boxed), 8, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_15);
lean_closure_set(x_16, 2, x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2(x_16, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_14);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
x_27 = lean_name_eq(x_26, x_14);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_free_object(x_17);
lean_dec(x_18);
x_28 = l_Lean_MessageData_ofName(x_26);
x_29 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__2;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_28);
lean_ctor_set(x_8, 0, x_29);
x_30 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_ofName(x_14);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__6;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Meta_instantiateForallWithParamInfos___spec__1(x_35, x_3, x_4, x_5, x_6, x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_dec(x_26);
lean_dec(x_14);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_dec(x_17);
x_42 = lean_ctor_get(x_18, 0);
lean_inc(x_42);
x_43 = lean_name_eq(x_42, x_14);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_18);
x_44 = l_Lean_MessageData_ofName(x_42);
x_45 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__2;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_44);
lean_ctor_set(x_8, 0, x_45);
x_46 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__4;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_MessageData_ofName(x_14);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__6;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at_Lean_Meta_instantiateForallWithParamInfos___spec__1(x_51, x_3, x_4, x_5, x_6, x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; 
lean_dec(x_42);
lean_dec(x_14);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_18);
lean_ctor_set(x_57, 1, x_41);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_14);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
return x_17;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_17, 0);
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_17);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_8, 0);
x_63 = lean_ctor_get(x_8, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_8);
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_1);
x_66 = l_Lean_Meta_mkEqLikeNameFor(x_64, x_1, x_65);
x_67 = lean_box(x_2);
lean_inc(x_66);
x_68 = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__3___boxed), 8, 3);
lean_closure_set(x_68, 0, x_1);
lean_closure_set(x_68, 1, x_67);
lean_closure_set(x_68, 2, x_66);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_69 = l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2(x_68, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_75 = x_69;
} else {
 lean_dec_ref(x_69);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_name_eq(x_76, x_66);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_75);
lean_dec(x_70);
x_78 = l_Lean_MessageData_ofName(x_76);
x_79 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__2;
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__4;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_MessageData_ofName(x_66);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__6;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at_Lean_Meta_instantiateForallWithParamInfos___spec__1(x_86, x_3, x_4, x_5, x_6, x_74);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 2, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
else
{
lean_object* x_92; 
lean_dec(x_76);
lean_dec(x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_75)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_75;
}
lean_ctor_set(x_92, 0, x_70);
lean_ctor_set(x_92, 1, x_74);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = lean_ctor_get(x_69, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_69, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_95 = x_69;
} else {
 lean_dec_ref(x_69);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___boxed), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
x_10 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__4;
x_11 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__5;
x_12 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore___spec__2___rarg(x_10, x_11, x_9, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_forIn_x27_loop___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__3(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_getUnfoldEqnFor_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" Lean.Meta.Eqns reserved name action for ", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = l_Lean_exceptBoolEmoji___rarg(x_2);
x_7 = l_Lean_stringToMessageData(x_6);
lean_dec(x_6);
x_8 = l_Lean_Meta_generateEagerEqns___closed__6;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__2;
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_MessageData_ofName(x_1);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 0;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = 2;
x_6 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, 1, x_1);
lean_ctor_set_uint8(x_6, 2, x_1);
lean_ctor_set_uint8(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, 5, x_2);
lean_ctor_set_uint8(x_6, 6, x_2);
lean_ctor_set_uint8(x_6, 7, x_1);
lean_ctor_set_uint8(x_6, 8, x_2);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_4);
lean_ctor_set_uint8(x_6, 11, x_2);
lean_ctor_set_uint8(x_6, 12, x_2);
lean_ctor_set_uint8(x_6, 13, x_2);
lean_ctor_set_uint8(x_6, 14, x_5);
lean_ctor_set_uint8(x_6, 15, x_2);
lean_ctor_set_uint8(x_6, 16, x_2);
lean_ctor_set_uint8(x_6, 17, x_2);
return x_6;
}
}
static uint64_t _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__1;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_markAsRecursive___closed__3;
x_3 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__1;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__2;
x_5 = 0;
x_6 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__3;
x_7 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__4;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_2);
lean_ctor_set(x_9, 5, x_8);
lean_ctor_set(x_9, 6, x_2);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 8, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 9, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 10, x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_markAsRecursive___closed__3;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_markAsRecursive___closed__3;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__6;
x_3 = l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2___closed__1;
x_4 = l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFor_x3fCore___closed__3;
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_unfoldThmSuffix;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_4(x_2, x_10, x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_12 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__8;
x_13 = lean_st_mk_ref(x_12, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__5;
lean_inc(x_14);
x_18 = l_Lean_Meta_getUnfoldEqnFor_x3f(x_3, x_16, x_17, x_14, x_5, x_6, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_14, x_20);
lean_dec(x_14);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = 0;
x_25 = lean_box(x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_19);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = lean_box(x_16);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_box(x_16);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__4___closed__1;
lean_inc(x_1);
x_10 = l_Lean_Meta_declFromEqLikeName(x_8, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_apply_4(x_9, x_11, x_2, x_3, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_3, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_15);
lean_inc(x_14);
x_20 = l_Lean_Meta_mkEqLikeNameFor(x_19, x_14, x_15);
x_21 = lean_name_eq(x_1, x_20);
lean_dec(x_20);
lean_dec(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_15);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = lean_apply_4(x_9, x_22, x_2, x_3, x_18);
return x_23;
}
else
{
uint8_t x_24; 
lean_inc(x_15);
x_24 = l_Lean_Meta_isEqnReservedNameSuffix(x_15);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3(x_15, x_9, x_14, x_25, x_2, x_3, x_18);
lean_dec(x_15);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_15);
x_27 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__8;
x_28 = lean_st_mk_ref(x_27, x_18);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__5;
lean_inc(x_29);
x_32 = l_Lean_Meta_getEqnsFor_x3f(x_14, x_31, x_29, x_2, x_3, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_29, x_34);
lean_dec(x_29);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = 0;
x_39 = lean_box(x_38);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = 0;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_33);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
x_46 = 1;
x_47 = lean_box(x_46);
lean_ctor_set(x_35, 0, x_47);
return x_35;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_dec(x_35);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_29);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
return x_32;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_32, 0);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_32);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ReservedNameAction", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___boxed), 5, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__4), 4, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__2;
x_8 = 1;
x_9 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5;
x_10 = l_Lean_withTraceNode___at_Lean_executeReservedNameAction___spec__2(x_7, x_5, x_6, x_8, x_9, x_2, x_3, x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____closed__1;
x_3 = l_Lean_registerReservedNameAction(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin, lean_object*);
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
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5____closed__10);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_eqns_nonrecursive = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_eqns_nonrecursive);
lean_dec_ref(res);
}l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44____closed__5);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_44_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_eqns_deepRecursiveSplit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_eqns_deepRecursiveSplit);
lean_dec_ref(res);
}l_Lean_Meta_eqnAffectingOptions___closed__1 = _init_l_Lean_Meta_eqnAffectingOptions___closed__1();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions___closed__1);
l_Lean_Meta_eqnAffectingOptions___closed__2 = _init_l_Lean_Meta_eqnAffectingOptions___closed__2();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions___closed__2);
l_Lean_Meta_eqnAffectingOptions___closed__3 = _init_l_Lean_Meta_eqnAffectingOptions___closed__3();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions___closed__3);
l_Lean_Meta_eqnAffectingOptions___closed__4 = _init_l_Lean_Meta_eqnAffectingOptions___closed__4();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions___closed__4);
l_Lean_Meta_eqnAffectingOptions___closed__5 = _init_l_Lean_Meta_eqnAffectingOptions___closed__5();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions___closed__5);
l_Lean_Meta_eqnAffectingOptions = _init_l_Lean_Meta_eqnAffectingOptions();
lean_mark_persistent(l_Lean_Meta_eqnAffectingOptions);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98____closed__2);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_98_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_recExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_recExt);
lean_dec_ref(res);
}l_Lean_Meta_markAsRecursive___closed__1 = _init_l_Lean_Meta_markAsRecursive___closed__1();
lean_mark_persistent(l_Lean_Meta_markAsRecursive___closed__1);
l_Lean_Meta_markAsRecursive___closed__2 = _init_l_Lean_Meta_markAsRecursive___closed__2();
lean_mark_persistent(l_Lean_Meta_markAsRecursive___closed__2);
l_Lean_Meta_markAsRecursive___closed__3 = _init_l_Lean_Meta_markAsRecursive___closed__3();
lean_mark_persistent(l_Lean_Meta_markAsRecursive___closed__3);
l_Lean_Meta_markAsRecursive___closed__4 = _init_l_Lean_Meta_markAsRecursive___closed__4();
lean_mark_persistent(l_Lean_Meta_markAsRecursive___closed__4);
l_Lean_Meta_eqnThmSuffixBase___closed__1 = _init_l_Lean_Meta_eqnThmSuffixBase___closed__1();
lean_mark_persistent(l_Lean_Meta_eqnThmSuffixBase___closed__1);
l_Lean_Meta_eqnThmSuffixBase = _init_l_Lean_Meta_eqnThmSuffixBase();
lean_mark_persistent(l_Lean_Meta_eqnThmSuffixBase);
l_Lean_Meta_eqnThmSuffixBasePrefix___closed__1 = _init_l_Lean_Meta_eqnThmSuffixBasePrefix___closed__1();
lean_mark_persistent(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__1);
l_Lean_Meta_eqnThmSuffixBasePrefix___closed__2 = _init_l_Lean_Meta_eqnThmSuffixBasePrefix___closed__2();
lean_mark_persistent(l_Lean_Meta_eqnThmSuffixBasePrefix___closed__2);
l_Lean_Meta_eqnThmSuffixBasePrefix = _init_l_Lean_Meta_eqnThmSuffixBasePrefix();
lean_mark_persistent(l_Lean_Meta_eqnThmSuffixBasePrefix);
l_Lean_Meta_eqn1ThmSuffix___closed__1 = _init_l_Lean_Meta_eqn1ThmSuffix___closed__1();
lean_mark_persistent(l_Lean_Meta_eqn1ThmSuffix___closed__1);
l_Lean_Meta_eqn1ThmSuffix___closed__2 = _init_l_Lean_Meta_eqn1ThmSuffix___closed__2();
lean_mark_persistent(l_Lean_Meta_eqn1ThmSuffix___closed__2);
l_Lean_Meta_eqn1ThmSuffix = _init_l_Lean_Meta_eqn1ThmSuffix();
lean_mark_persistent(l_Lean_Meta_eqn1ThmSuffix);
l_Lean_Meta_unfoldThmSuffix___closed__1 = _init_l_Lean_Meta_unfoldThmSuffix___closed__1();
lean_mark_persistent(l_Lean_Meta_unfoldThmSuffix___closed__1);
l_Lean_Meta_unfoldThmSuffix = _init_l_Lean_Meta_unfoldThmSuffix();
lean_mark_persistent(l_Lean_Meta_unfoldThmSuffix);
l_Lean_Meta_eqUnfoldThmSuffix___closed__1 = _init_l_Lean_Meta_eqUnfoldThmSuffix___closed__1();
lean_mark_persistent(l_Lean_Meta_eqUnfoldThmSuffix___closed__1);
l_Lean_Meta_eqUnfoldThmSuffix = _init_l_Lean_Meta_eqUnfoldThmSuffix();
lean_mark_persistent(l_Lean_Meta_eqUnfoldThmSuffix);
l_Lean_Meta_declFromEqLikeName___closed__1 = _init_l_Lean_Meta_declFromEqLikeName___closed__1();
lean_mark_persistent(l_Lean_Meta_declFromEqLikeName___closed__1);
l_Lean_Meta_declFromEqLikeName___closed__2 = _init_l_Lean_Meta_declFromEqLikeName___closed__2();
lean_mark_persistent(l_Lean_Meta_declFromEqLikeName___closed__2);
l_Lean_Meta_declFromEqLikeName___closed__3 = _init_l_Lean_Meta_declFromEqLikeName___closed__3();
lean_mark_persistent(l_Lean_Meta_declFromEqLikeName___closed__3);
l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__1 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__1();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__1);
l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__2 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__2();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__2);
l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__3 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__3();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__3);
l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__4 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__4();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__4);
l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__5 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__5();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__5);
l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__6 = _init_l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__6();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___at_Lean_Meta_ensureEqnReservedNamesAvailable___spec__2___closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632____closed__1);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_632_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_717_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getEqnsFnsRef);
lean_dec_ref(res);
}l_Lean_Meta_registerGetEqnsFn___lambda__1___closed__1 = _init_l_Lean_Meta_registerGetEqnsFn___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_registerGetEqnsFn___lambda__1___closed__1);
l_Lean_Meta_registerGetEqnsFn___closed__1 = _init_l_Lean_Meta_registerGetEqnsFn___closed__1();
lean_mark_persistent(l_Lean_Meta_registerGetEqnsFn___closed__1);
l_Lean_Meta_registerGetEqnsFn___closed__2 = _init_l_Lean_Meta_registerGetEqnsFn___closed__2();
lean_mark_persistent(l_Lean_Meta_registerGetEqnsFn___closed__2);
l_Lean_Meta_instInhabitedEqnsExtState = _init_l_Lean_Meta_instInhabitedEqnsExtState();
lean_mark_persistent(l_Lean_Meta_instInhabitedEqnsExtState);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982____closed__1);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_982_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_eqnsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_eqnsExt);
lean_dec_ref(res);
}l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_isEqnThm_x3f___spec__2___closed__2();
l_Lean_Meta_isEqnThm_x3f___closed__1 = _init_l_Lean_Meta_isEqnThm_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_isEqnThm_x3f___closed__1);
l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___private_Lean_Meta_Eqns_0__Lean_Meta_registerEqnThms___spec__2___closed__1);
l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__1 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__1);
l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__2 = _init_l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_alreadyGenerated_x3f_loop___closed__2);
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
l_Lean_Meta_getEqnsFor_x3f___lambda__1___closed__1 = _init_l_Lean_Meta_getEqnsFor_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_getEqnsFor_x3f___lambda__1___closed__1);
l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__1);
l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__2();
l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__3 = _init_l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__3);
l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__4 = _init_l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__4();
l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__5 = _init_l_Lean_Meta_getEqnsFor_x3f___lambda__2___closed__5();
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
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2160_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Eqns_0__Lean_Meta_getUnfoldEqnFnsRef);
lean_dec_ref(res);
}l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1___closed__1 = _init_l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_registerGetUnfoldEqnFn___lambda__1___closed__1);
l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2___closed__1 = _init_l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2___closed__1();
lean_mark_persistent(l_Lean_withoutExporting___at_Lean_Meta_getUnfoldEqnFor_x3f___spec__2___closed__1);
l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__2___closed__1);
l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__1 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__1);
l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__2 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__2);
l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__3 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__3);
l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__4 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__4);
l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__5 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__5);
l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__6 = _init_l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Meta_getUnfoldEqnFor_x3f___lambda__4___closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__1___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__2();
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__3___closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__4___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__4___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____lambda__5___closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897____closed__1);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Eqns___hyg_2897_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
