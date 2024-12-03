// Lean compiler output
// Module: Lean.Server.Completion.CompletionCollectors
// Imports: Lean.Data.FuzzyMatching Lean.Elab.Tactic.Doc Lean.Server.Completion.CompletionResolution Lean.Server.Completion.EligibleHeaderDecls
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
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getNumParts(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureParentInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__5;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseReps___at_Lean_computeStructureResolutionOrder___spec__8(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___closed__1;
static double l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__1;
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__16(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Server_Completion_allowCompletion(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_div(double, double);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_matchNamespace___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findDocString_x3f(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_optionCompletion___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__26___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__7(lean_object*, lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__15(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2;
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__4;
lean_object* l_Lean_getAliasState(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19(size_t, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_getTokenTable(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(lean_object*, lean_object*);
extern lean_object* l_Lean_projectionFnInfoExt;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Server_Completion_dotCompletion___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedDeprecationEntry;
static double l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__22(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___private_Lean_Structure_0__Lean_setStructureResolutionOrder___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_matchNamespace(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Server_Completion_dotCompletion___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_tacticCompletion___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Server_Completion_fieldIdCompletion___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_tacticCompletion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___at_Lean_addAliasEntry___spec__16(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isTheorem(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_matchNamespace___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Data_Trie_findPrefix_go___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_erase___at_Lean_getAllParentStructures___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___boxed(lean_object**);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4;
double lean_uint64_to_float(uint64_t);
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isCtor(lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__1;
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__7(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__2;
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__28(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1;
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_visitNamespaces(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Server_Completion_dotCompletion___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSSet_instInhabited;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivatePrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecls(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_optionCompletion___closed__4;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2;
lean_object* l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(lean_object*, lean_object*, double);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_optionCompletion___closed__2;
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Server_Completion_dotIdCompletion___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getEligibleHeaderDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__2(lean_object*);
static lean_object* l_Lean_Server_Completion_optionCompletion___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__1(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3;
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__28(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__27(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___boxed(lean_object**);
lean_object* l_Lean_Elab_Tactic_Doc_allTacticDocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedProjectionFunctionInfo;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__7;
lean_object* l_Lean_Syntax_getSubstring_x3f(lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2;
extern lean_object* l_Lean_structureResolutionExt;
static lean_object* l_Lean_Server_Completion_optionCompletion___closed__1;
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2;
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem(lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_deprecatedAttr;
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Server_Completion_dotCompletion___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces_visitNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2;
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__4;
lean_object* l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Server_Completion_dotIdCompletion___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Server_Completion_dotCompletion___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
uint8_t l_Lean_Meta_allowCompletion(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__3;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13(lean_object*, lean_object*, size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isInductive(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_computeStructureResolutionOrder___spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Server_Completion_dotIdCompletion___spec__1(lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_instInhabitedScoredCompletionItem;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__5;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_namespacesExt;
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Server_Completion_dotCompletion___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_completeNamespaces___closed__1;
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__8(lean_object*, lean_object*, lean_object*, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__26(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20(lean_object*, lean_object*, size_t, size_t);
uint8_t l_Lean_Name_isSuffixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(lean_object*, lean_object*, uint8_t, double, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__23(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407_(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__6;
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__4;
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__4;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27(uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces_visitNamespaces(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1;
lean_object* l_Lean_Elab_ContextInfo_runMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertIdx_loop___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_data_value_to_string(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_3 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
return x_3;
}
}
static double _init_l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__3() {
_start:
{
uint64_t x_1; double x_2; 
x_1 = 0;
x_2 = lean_uint64_to_float(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__4() {
_start:
{
lean_object* x_1; double x_2; lean_object* x_3; 
x_1 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__2;
x_2 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__3;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_float(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Completion_instInhabitedScoredCompletionItem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(lean_object* x_1, double x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_inc(x_11);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_3);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = lean_ctor_get(x_1, 6);
lean_dec(x_15);
x_16 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407_(x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_1, 6, x_17);
x_18 = lean_st_ref_take(x_5, x_10);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set_float(x_21, sizeof(void*)*1, x_2);
x_22 = lean_array_push(x_19, x_21);
x_23 = lean_st_ref_set(x_5, x_22, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_ctor_get(x_1, 2);
x_33 = lean_ctor_get(x_1, 3);
x_34 = lean_ctor_get(x_1, 4);
x_35 = lean_ctor_get(x_1, 5);
x_36 = lean_ctor_get(x_1, 7);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_1);
x_37 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407_(x_13);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_31);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_33);
lean_ctor_set(x_39, 4, x_34);
lean_ctor_set(x_39, 5, x_35);
lean_ctor_set(x_39, 6, x_38);
lean_ctor_set(x_39, 7, x_36);
x_40 = lean_st_ref_take(x_5, x_10);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set_float(x_43, sizeof(void*)*1, x_2);
x_44 = lean_array_push(x_41, x_43);
x_45 = lean_st_ref_set(x_5, x_44, x_42);
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
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
double x_11; lean_object* x_12; 
x_11 = lean_unbox_float(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = 1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, double x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__1;
x_16 = 1;
x_17 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2;
x_18 = l_Lean_Name_toString(x_1, x_16, x_17);
x_19 = lean_box(0);
x_20 = lean_box(x_2);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_3);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_21);
lean_ctor_set(x_23, 4, x_19);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_19);
lean_ctor_set(x_23, 7, x_5);
x_24 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(x_23, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_apply_1(x_15, x_25);
x_27 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_26);
lean_ctor_set(x_27, 3, x_21);
lean_ctor_set(x_27, 4, x_19);
lean_ctor_set(x_27, 5, x_19);
lean_ctor_set(x_27, 6, x_19);
lean_ctor_set(x_27, 7, x_5);
x_28 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(x_27, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_28;
}
}
else
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_4, 0);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_apply_1(x_15, x_29);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_21);
lean_ctor_set(x_31, 4, x_19);
lean_ctor_set(x_31, 5, x_19);
lean_ctor_set(x_31, 6, x_19);
lean_ctor_set(x_31, 7, x_5);
x_32 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(x_31, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
lean_dec(x_4);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
lean_dec(x_7);
x_35 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_36 = lean_string_append(x_35, x_33);
lean_dec(x_33);
x_37 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__3;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_string_append(x_38, x_34);
lean_dec(x_34);
x_40 = lean_string_append(x_39, x_35);
x_41 = lean_apply_1(x_15, x_40);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_18);
lean_ctor_set(x_42, 1, x_19);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_21);
lean_ctor_set(x_42, 4, x_19);
lean_ctor_set(x_42, 5, x_19);
lean_ctor_set(x_42, 6, x_19);
lean_ctor_set(x_42, 7, x_5);
x_43 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(x_42, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_43;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Linter_deprecatedAttr;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__2;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has been deprecated.", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has been deprecated, use `", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` instead.", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(lean_object* x_1, lean_object* x_2, uint8_t x_3, double x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
x_28 = l_Lean_Linter_instInhabitedDeprecationEntry;
x_29 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__1;
lean_inc(x_27);
x_30 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_28, x_29, x_15, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_27);
x_31 = lean_box(0);
x_16 = x_31;
x_17 = x_31;
goto block_26;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = 1;
x_37 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2;
x_38 = l_Lean_Name_toString(x_27, x_36, x_37);
x_39 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__5;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__6;
x_42 = lean_string_append(x_40, x_41);
lean_ctor_set(x_30, 0, x_42);
x_43 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4;
x_16 = x_30;
x_17 = x_43;
goto block_26;
}
else
{
uint8_t x_44; 
lean_free_object(x_30);
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_35, 0);
x_46 = 1;
x_47 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2;
x_48 = l_Lean_Name_toString(x_27, x_46, x_47);
x_49 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__5;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__7;
x_52 = lean_string_append(x_50, x_51);
x_53 = l_Lean_Name_toString(x_45, x_46, x_47);
x_54 = lean_string_append(x_52, x_53);
lean_dec(x_53);
x_55 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__8;
x_56 = lean_string_append(x_54, x_55);
lean_ctor_set(x_35, 0, x_56);
x_57 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4;
x_16 = x_35;
x_17 = x_57;
goto block_26;
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_58 = lean_ctor_get(x_35, 0);
lean_inc(x_58);
lean_dec(x_35);
x_59 = 1;
x_60 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2;
x_61 = l_Lean_Name_toString(x_27, x_59, x_60);
x_62 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__5;
x_63 = lean_string_append(x_62, x_61);
lean_dec(x_61);
x_64 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__7;
x_65 = lean_string_append(x_63, x_64);
x_66 = l_Lean_Name_toString(x_58, x_59, x_60);
x_67 = lean_string_append(x_65, x_66);
lean_dec(x_66);
x_68 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__8;
x_69 = lean_string_append(x_67, x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4;
x_16 = x_70;
x_17 = x_71;
goto block_26;
}
}
}
else
{
uint8_t x_72; 
lean_free_object(x_30);
lean_dec(x_33);
lean_dec(x_27);
x_72 = !lean_is_exclusive(x_34);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4;
x_16 = x_34;
x_17 = x_73;
goto block_26;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_34, 0);
lean_inc(x_74);
lean_dec(x_34);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4;
x_16 = x_75;
x_17 = x_76;
goto block_26;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_30, 0);
lean_inc(x_77);
lean_dec(x_30);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
lean_dec(x_77);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = 1;
x_81 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2;
x_82 = l_Lean_Name_toString(x_27, x_80, x_81);
x_83 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__5;
x_84 = lean_string_append(x_83, x_82);
lean_dec(x_82);
x_85 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__6;
x_86 = lean_string_append(x_84, x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4;
x_16 = x_87;
x_17 = x_88;
goto block_26;
}
else
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_89 = lean_ctor_get(x_79, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 x_90 = x_79;
} else {
 lean_dec_ref(x_79);
 x_90 = lean_box(0);
}
x_91 = 1;
x_92 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2;
x_93 = l_Lean_Name_toString(x_27, x_91, x_92);
x_94 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__5;
x_95 = lean_string_append(x_94, x_93);
lean_dec(x_93);
x_96 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__7;
x_97 = lean_string_append(x_95, x_96);
x_98 = l_Lean_Name_toString(x_89, x_91, x_92);
x_99 = lean_string_append(x_97, x_98);
lean_dec(x_98);
x_100 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__8;
x_101 = lean_string_append(x_99, x_100);
if (lean_is_scalar(x_90)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_90;
}
lean_ctor_set(x_102, 0, x_101);
x_103 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4;
x_16 = x_102;
x_17 = x_103;
goto block_26;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_77);
lean_dec(x_27);
x_104 = lean_ctor_get(x_78, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_105 = x_78;
} else {
 lean_dec_ref(x_78);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
x_107 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4;
x_16 = x_106;
x_17 = x_107;
goto block_26;
}
}
}
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
x_16 = x_108;
x_17 = x_108;
goto block_26;
}
block_26:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = 1;
x_20 = l_Lean_findDocString_x3f(x_15, x_18, x_19, x_14);
lean_dec(x_15);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3(x_1, x_3, x_2, x_16, x_17, x_4, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
x_24 = lean_box(0);
x_25 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3(x_1, x_3, x_2, x_16, x_17, x_4, x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; double x_16; lean_object* x_17; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_float(x_6);
lean_dec(x_6);
x_17 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3(x_1, x_15, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; double x_13; lean_object* x_14; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox_float(x_4);
lean_dec(x_4);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
static lean_object* _init_l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_projectionFnInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_instInhabitedProjectionFunctionInfo;
x_14 = l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1;
x_15 = l_Lean_MapDeclarationExtension_contains___rarg(x_13, x_14, x_12, x_1);
lean_dec(x_12);
x_16 = lean_box(x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_instInhabitedProjectionFunctionInfo;
x_21 = l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1;
x_22 = l_Lean_MapDeclarationExtension_contains___rarg(x_20, x_21, x_19, x_1);
lean_dec(x_19);
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_18);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_tag(x_10, 1);
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
lean_inc(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown constant '", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Environment_find_x3f(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_9);
x_15 = 0;
x_16 = l_Lean_MessageData_ofConstName(x_1, x_15);
x_17 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Environment_find_x3f(x_25, x_1);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = 0;
x_28 = l_Lean_MessageData_ofConstName(x_1, x_27);
x_29 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_24);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_24);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_22; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_22 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 6)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_26);
x_15 = x_28;
x_16 = x_24;
goto block_21;
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_dec(x_23);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = 0;
x_15 = x_30;
x_16 = x_29;
goto block_21;
}
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_13);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
return x_22;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
block_21:
{
if (x_15 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
x_17 = 0;
x_18 = lean_box(x_17);
if (lean_is_scalar(x_14)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_14;
 lean_ctor_set_tag(x_19, 0);
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_dec(x_14);
x_1 = x_13;
x_8 = x_16;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 5)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Expr_isProp(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_InductiveVal_numTypeFormers(x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_14);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_14, 2);
lean_inc(x_23);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
uint8_t x_26; lean_object* x_27; 
lean_dec(x_14);
x_26 = 0;
x_27 = lean_box(x_26);
lean_ctor_set(x_9, 0, x_27);
return x_9;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
x_29 = lean_nat_dec_eq(x_28, x_24);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; 
lean_dec(x_14);
x_30 = 0;
x_31 = lean_box(x_30);
lean_ctor_set(x_9, 0, x_31);
return x_9;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_14, 4);
lean_inc(x_32);
x_33 = l_List_isEmpty___rarg(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = lean_ctor_get_uint8(x_14, sizeof(void*)*6 + 1);
lean_dec(x_14);
if (x_35 == 0)
{
lean_object* x_36; 
lean_free_object(x_9);
x_36 = l_List_allM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_36;
}
else
{
uint8_t x_37; lean_object* x_38; 
lean_dec(x_32);
x_37 = 0;
x_38 = lean_box(x_37);
lean_ctor_set(x_9, 0, x_38);
return x_9;
}
}
else
{
uint8_t x_39; lean_object* x_40; 
lean_dec(x_32);
lean_dec(x_14);
x_39 = 0;
x_40 = lean_box(x_39);
lean_ctor_set(x_9, 0, x_40);
return x_9;
}
}
else
{
uint8_t x_41; lean_object* x_42; 
lean_dec(x_32);
lean_dec(x_14);
x_41 = 0;
x_42 = lean_box(x_41);
lean_ctor_set(x_9, 0, x_42);
return x_9;
}
}
}
}
}
else
{
uint8_t x_43; lean_object* x_44; 
lean_dec(x_14);
x_43 = 0;
x_44 = lean_box(x_43);
lean_ctor_set(x_9, 0, x_44);
return x_9;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_dec(x_9);
x_46 = lean_ctor_get(x_10, 0);
lean_inc(x_46);
lean_dec(x_10);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 2);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Expr_isProp(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Lean_InductiveVal_numTypeFormers(x_46);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_dec_eq(x_50, x_51);
lean_dec(x_50);
if (x_52 == 0)
{
uint8_t x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_46);
x_53 = 0;
x_54 = lean_box(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_45);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_46, 2);
lean_inc(x_56);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_dec_eq(x_56, x_57);
lean_dec(x_56);
if (x_58 == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_46);
x_59 = 0;
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_45);
return x_61;
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_46, 1);
lean_inc(x_62);
x_63 = lean_nat_dec_eq(x_62, x_57);
lean_dec(x_62);
if (x_63 == 0)
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_46);
x_64 = 0;
x_65 = lean_box(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_45);
return x_66;
}
else
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_46, 4);
lean_inc(x_67);
x_68 = l_List_isEmpty___rarg(x_67);
if (x_68 == 0)
{
uint8_t x_69; 
x_69 = lean_ctor_get_uint8(x_46, sizeof(void*)*6);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = lean_ctor_get_uint8(x_46, sizeof(void*)*6 + 1);
lean_dec(x_46);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = l_List_allM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_45);
return x_71;
}
else
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_67);
x_72 = 0;
x_73 = lean_box(x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_45);
return x_74;
}
}
else
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_67);
lean_dec(x_46);
x_75 = 0;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_45);
return x_77;
}
}
else
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_67);
lean_dec(x_46);
x_78 = 0;
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_45);
return x_80;
}
}
}
}
}
else
{
uint8_t x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_46);
x_81 = 0;
x_82 = lean_box(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_45);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_10);
x_84 = !lean_is_exclusive(x_9);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_9, 0);
lean_dec(x_85);
x_86 = 0;
x_87 = lean_box(x_86);
lean_ctor_set(x_9, 0, x_87);
return x_9;
}
else
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_9, 1);
lean_inc(x_88);
lean_dec(x_9);
x_89 = 0;
x_90 = lean_box(x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_9);
if (x_92 == 0)
{
return x_9;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_9, 0);
x_94 = lean_ctor_get(x_9, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_9);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_ConstantInfo_isCtor(x_1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_ConstantInfo_isInductive(x_1);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = l_Lean_ConstantInfo_isTheorem(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_free_object(x_9);
x_17 = l_Lean_ConstantInfo_name(x_1);
x_18 = l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_ConstantInfo_type(x_1);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 9);
lean_dec(x_24);
x_25 = lean_unsigned_to_nat(0u);
lean_ctor_set(x_6, 9, x_25);
x_26 = lean_whnf(x_22, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Expr_isForall(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; lean_object* x_31; 
x_30 = 20;
x_31 = lean_box(x_30);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
uint8_t x_32; lean_object* x_33; 
x_32 = 2;
x_33 = lean_box(x_32);
lean_ctor_set(x_26, 0, x_33);
return x_26;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
x_36 = l_Lean_Expr_isForall(x_34);
lean_dec(x_34);
if (x_36 == 0)
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 20;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = 2;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_26);
if (x_43 == 0)
{
return x_26;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_26, 0);
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_26);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_47 = lean_ctor_get(x_6, 0);
x_48 = lean_ctor_get(x_6, 1);
x_49 = lean_ctor_get(x_6, 2);
x_50 = lean_ctor_get(x_6, 3);
x_51 = lean_ctor_get(x_6, 4);
x_52 = lean_ctor_get(x_6, 5);
x_53 = lean_ctor_get(x_6, 6);
x_54 = lean_ctor_get(x_6, 7);
x_55 = lean_ctor_get(x_6, 8);
x_56 = lean_ctor_get(x_6, 10);
x_57 = lean_ctor_get_uint8(x_6, sizeof(void*)*12);
x_58 = lean_ctor_get(x_6, 11);
x_59 = lean_ctor_get_uint8(x_6, sizeof(void*)*12 + 1);
lean_inc(x_58);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_6);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_48);
lean_ctor_set(x_61, 2, x_49);
lean_ctor_set(x_61, 3, x_50);
lean_ctor_set(x_61, 4, x_51);
lean_ctor_set(x_61, 5, x_52);
lean_ctor_set(x_61, 6, x_53);
lean_ctor_set(x_61, 7, x_54);
lean_ctor_set(x_61, 8, x_55);
lean_ctor_set(x_61, 9, x_60);
lean_ctor_set(x_61, 10, x_56);
lean_ctor_set(x_61, 11, x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*12, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*12 + 1, x_59);
x_62 = lean_whnf(x_22, x_4, x_5, x_61, x_7, x_21);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = l_Lean_Expr_isForall(x_63);
lean_dec(x_63);
if (x_66 == 0)
{
uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_67 = 20;
x_68 = lean_box(x_67);
if (lean_is_scalar(x_65)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_65;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
else
{
uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_70 = 2;
x_71 = lean_box(x_70);
if (lean_is_scalar(x_65)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_65;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_64);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_62, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_75 = x_62;
} else {
 lean_dec_ref(x_62);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_18);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_18, 0);
lean_dec(x_78);
x_79 = 4;
x_80 = lean_box(x_79);
lean_ctor_set(x_18, 0, x_80);
return x_18;
}
else
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_18, 1);
lean_inc(x_81);
lean_dec(x_18);
x_82 = 4;
x_83 = lean_box(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
}
else
{
uint8_t x_85; lean_object* x_86; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_85 = 22;
x_86 = lean_box(x_85);
lean_ctor_set(x_9, 0, x_86);
return x_9;
}
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_87);
x_88 = lean_is_class(x_13, x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_free_object(x_9);
x_89 = l_Lean_isEnumType___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2(x_87, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 0);
lean_dec(x_93);
x_94 = 21;
x_95 = lean_box(x_94);
lean_ctor_set(x_89, 0, x_95);
return x_89;
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_dec(x_89);
x_97 = 21;
x_98 = lean_box(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_89);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_89, 0);
lean_dec(x_101);
x_102 = 12;
x_103 = lean_box(x_102);
lean_ctor_set(x_89, 0, x_103);
return x_89;
}
else
{
lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_89, 1);
lean_inc(x_104);
lean_dec(x_89);
x_105 = 12;
x_106 = lean_box(x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
return x_107;
}
}
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_89);
if (x_108 == 0)
{
return x_89;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_89, 0);
x_110 = lean_ctor_get(x_89, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_89);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; lean_object* x_113; 
lean_dec(x_87);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = 6;
x_113 = lean_box(x_112);
lean_ctor_set(x_9, 0, x_113);
return x_9;
}
}
}
else
{
uint8_t x_114; lean_object* x_115; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_114 = 3;
x_115 = lean_box(x_114);
lean_ctor_set(x_9, 0, x_115);
return x_9;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_ctor_get(x_9, 0);
x_117 = lean_ctor_get(x_9, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_9);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_ConstantInfo_isCtor(x_1);
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = l_Lean_ConstantInfo_isInductive(x_1);
if (x_120 == 0)
{
uint8_t x_121; 
lean_dec(x_118);
x_121 = l_Lean_ConstantInfo_isTheorem(x_1);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = l_Lean_ConstantInfo_name(x_1);
x_123 = l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_117);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_127 = l_Lean_ConstantInfo_type(x_1);
x_128 = lean_ctor_get(x_6, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_6, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_6, 2);
lean_inc(x_130);
x_131 = lean_ctor_get(x_6, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_6, 4);
lean_inc(x_132);
x_133 = lean_ctor_get(x_6, 5);
lean_inc(x_133);
x_134 = lean_ctor_get(x_6, 6);
lean_inc(x_134);
x_135 = lean_ctor_get(x_6, 7);
lean_inc(x_135);
x_136 = lean_ctor_get(x_6, 8);
lean_inc(x_136);
x_137 = lean_ctor_get(x_6, 10);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_6, sizeof(void*)*12);
x_139 = lean_ctor_get(x_6, 11);
lean_inc(x_139);
x_140 = lean_ctor_get_uint8(x_6, sizeof(void*)*12 + 1);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 lean_ctor_release(x_6, 10);
 lean_ctor_release(x_6, 11);
 x_141 = x_6;
} else {
 lean_dec_ref(x_6);
 x_141 = lean_box(0);
}
x_142 = lean_unsigned_to_nat(0u);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 12, 2);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_128);
lean_ctor_set(x_143, 1, x_129);
lean_ctor_set(x_143, 2, x_130);
lean_ctor_set(x_143, 3, x_131);
lean_ctor_set(x_143, 4, x_132);
lean_ctor_set(x_143, 5, x_133);
lean_ctor_set(x_143, 6, x_134);
lean_ctor_set(x_143, 7, x_135);
lean_ctor_set(x_143, 8, x_136);
lean_ctor_set(x_143, 9, x_142);
lean_ctor_set(x_143, 10, x_137);
lean_ctor_set(x_143, 11, x_139);
lean_ctor_set_uint8(x_143, sizeof(void*)*12, x_138);
lean_ctor_set_uint8(x_143, sizeof(void*)*12 + 1, x_140);
x_144 = lean_whnf(x_127, x_4, x_5, x_143, x_7, x_126);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
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
x_148 = l_Lean_Expr_isForall(x_145);
lean_dec(x_145);
if (x_148 == 0)
{
uint8_t x_149; lean_object* x_150; lean_object* x_151; 
x_149 = 20;
x_150 = lean_box(x_149);
if (lean_is_scalar(x_147)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_147;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_146);
return x_151;
}
else
{
uint8_t x_152; lean_object* x_153; lean_object* x_154; 
x_152 = 2;
x_153 = lean_box(x_152);
if (lean_is_scalar(x_147)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_147;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_146);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_144, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_144, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_157 = x_144;
} else {
 lean_dec_ref(x_144);
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
}
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_159 = lean_ctor_get(x_123, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_160 = x_123;
} else {
 lean_dec_ref(x_123);
 x_160 = lean_box(0);
}
x_161 = 4;
x_162 = lean_box(x_161);
if (lean_is_scalar(x_160)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_160;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_159);
return x_163;
}
}
else
{
uint8_t x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_164 = 22;
x_165 = lean_box(x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_117);
return x_166;
}
}
else
{
lean_object* x_167; uint8_t x_168; 
x_167 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_167);
x_168 = lean_is_class(x_118, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = l_Lean_isEnumType___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2(x_167, x_2, x_3, x_4, x_5, x_6, x_7, x_117);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_173 = x_169;
} else {
 lean_dec_ref(x_169);
 x_173 = lean_box(0);
}
x_174 = 21;
x_175 = lean_box(x_174);
if (lean_is_scalar(x_173)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_173;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_172);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_169, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_178 = x_169;
} else {
 lean_dec_ref(x_169);
 x_178 = lean_box(0);
}
x_179 = 12;
x_180 = lean_box(x_179);
if (lean_is_scalar(x_178)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_178;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_177);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_169, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_169, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_184 = x_169;
} else {
 lean_dec_ref(x_169);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
uint8_t x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_167);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_186 = 6;
x_187 = lean_box(x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_117);
return x_188;
}
}
}
else
{
uint8_t x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_118);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_189 = 3;
x_190 = lean_box(x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_117);
return x_191;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_allM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isEnumType___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(lean_object* x_1, lean_object* x_2, double x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Environment_find_x3f(x_15, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
uint8_t x_18; 
lean_free_object(x_11);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_2);
x_23 = lean_unbox(x_21);
lean_dec(x_21);
x_24 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_1, x_16, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
else
{
uint8_t x_25; 
lean_free_object(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl(x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_2);
x_34 = lean_unbox(x_31);
lean_dec(x_31);
x_35 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_1, x_33, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Environment_find_x3f(x_42, x_2);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_47 = x_43;
} else {
 lean_dec_ref(x_43);
 x_47 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_48 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl(x_46, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
if (lean_is_scalar(x_47)) {
 x_51 = lean_alloc_ctor(0, 1, 0);
} else {
 x_51 = x_47;
 lean_ctor_set_tag(x_51, 0);
}
lean_ctor_set(x_51, 0, x_2);
x_52 = lean_unbox(x_49);
lean_dec(x_49);
x_53 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_1, x_51, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
double x_11; lean_object* x_12; 
x_11 = lean_unbox_float(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("keyword", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 13;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem(lean_object* x_1, double x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_box(0);
x_11 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2;
x_12 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3;
x_13 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_10);
lean_ctor_set(x_13, 5, x_10);
lean_ctor_set(x_13, 6, x_10);
lean_ctor_set(x_13, 7, x_10);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(x_13, x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
double x_10; lean_object* x_11; 
x_10 = lean_unbox_float(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("namespace", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 8;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(lean_object* x_1, double x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = 1;
x_11 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2;
x_12 = l_Lean_Name_toString(x_1, x_10, x_11);
x_13 = lean_box(0);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2;
x_15 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3;
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_15);
lean_ctor_set(x_16, 4, x_13);
lean_ctor_set(x_16, 5, x_13);
lean_ctor_set(x_16, 6, x_13);
lean_ctor_set(x_16, 7, x_13);
x_17 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(x_16, x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
double x_10; lean_object* x_11; 
x_10 = lean_unbox_float(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_st_mk_ref(x_1, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_10);
x_12 = lean_apply_7(x_2, x_3, x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_10, x_13);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_10);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
x_8 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_7);
x_10 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_3, x_4, x_9, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = lean_private_to_user_name(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_st_ref_get(x_5, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_11);
x_16 = l_Lean_mkPrivateName(x_15, x_11);
lean_dec(x_15);
x_17 = lean_name_eq(x_16, x_1);
lean_dec(x_1);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_7);
lean_dec(x_11);
x_18 = lean_box(0);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_11);
x_22 = l_Lean_mkPrivateName(x_21, x_11);
lean_dec(x_21);
x_23 = lean_name_eq(x_22, x_1);
lean_dec(x_1);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_7);
lean_dec(x_11);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_7, 0);
lean_inc(x_27);
lean_dec(x_7);
x_28 = lean_st_ref_get(x_5, x_6);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_27);
x_33 = l_Lean_mkPrivateName(x_32, x_27);
lean_dec(x_32);
x_34 = lean_name_eq(x_33, x_1);
lean_dec(x_1);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
x_35 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_31;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_27);
if (lean_is_scalar(x_31)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_31;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__1___boxed), 6, 0);
return x_1;
}
}
static double _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; double x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = l_Float_ofScientific(x_1, x_2, x_1);
return x_3;
}
}
static double _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; double x_4; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 0;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Float_ofScientific(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1() {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3;
x_2 = lean_box_float(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = l_Lean_Name_replacePrefix(x_1, x_2, x_11);
x_13 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1;
if (x_3 == 0)
{
if (lean_obj_tag(x_4) == 1)
{
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
x_18 = lean_name_eq(x_14, x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Name_isAnonymous(x_14);
lean_dec(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
x_20 = lean_box(0);
x_21 = lean_apply_6(x_13, x_20, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
else
{
double x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2;
x_23 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_15, x_17, x_22);
lean_dec(x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
lean_dec(x_12);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; double x_33; double x_34; double x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = l_Lean_Name_getNumParts(x_16);
lean_dec(x_16);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_28, x_29);
lean_dec(x_28);
x_31 = 0;
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Float_ofScientific(x_30, x_31, x_32);
lean_dec(x_30);
x_34 = lean_unbox_float(x_27);
lean_dec(x_27);
x_35 = lean_float_div(x_34, x_33);
x_36 = lean_box_float(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_12);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_23, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_23);
lean_ctor_set(x_38, 1, x_10);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; double x_45; double x_46; double x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_39 = lean_ctor_get(x_23, 0);
lean_inc(x_39);
lean_dec(x_23);
x_40 = l_Lean_Name_getNumParts(x_16);
lean_dec(x_16);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_40, x_41);
lean_dec(x_40);
x_43 = 0;
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Float_ofScientific(x_42, x_43, x_44);
lean_dec(x_42);
x_46 = lean_unbox_float(x_39);
lean_dec(x_39);
x_47 = lean_float_div(x_46, x_45);
x_48 = lean_box_float(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_12);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_10);
return x_51;
}
}
}
}
else
{
double x_52; lean_object* x_53; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_52 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2;
x_53 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_15, x_17, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_17);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_10);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = l_Lean_Name_str___override(x_11, x_17);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_53, 0, x_59);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_10);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
lean_dec(x_53);
x_62 = l_Lean_Name_str___override(x_11, x_17);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_10);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_12);
lean_dec(x_4);
x_66 = lean_box(0);
x_67 = lean_apply_6(x_13, x_66, x_6, x_7, x_8, x_9, x_10);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_12);
lean_dec(x_4);
x_68 = lean_box(0);
x_69 = lean_apply_6(x_13, x_68, x_6, x_7, x_8, x_9, x_10);
return x_69;
}
}
else
{
uint8_t x_70; 
x_70 = l_Lean_Name_isPrefixOf(x_4, x_12);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_12);
lean_dec(x_4);
x_71 = lean_box(0);
x_72 = lean_apply_6(x_13, x_71, x_6, x_7, x_8, x_9, x_10);
return x_72;
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = l_Lean_Name_replacePrefix(x_12, x_4, x_11);
lean_dec(x_4);
x_74 = l_Lean_Name_isAtomic(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_73);
x_75 = lean_box(0);
x_76 = lean_apply_6(x_13, x_75, x_6, x_7, x_8, x_9, x_10);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = l_Lean_Name_isAnonymous(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_78 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_10);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_73);
x_82 = lean_box(0);
x_83 = lean_apply_6(x_13, x_82, x_6, x_7, x_8, x_9, x_10);
return x_83;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_Name_isPrefixOf(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_23 = lean_box(0);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_10);
x_24 = lean_box(0);
x_25 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2(x_21, x_1, x_3, x_2, x_24, x_5, x_6, x_7, x_8, x_19);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_dec(x_10);
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = l_Lean_Name_isPrefixOf(x_1, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
x_32 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2(x_27, x_1, x_3, x_2, x_31, x_5, x_6, x_7, x_8, x_26);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; double x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2;
x_9 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___lambda__1(x_1, x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_panic___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedName;
x_2 = l_instInhabitedNat;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___spec__1___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Server.Completion.CompletionCollectors", 43, 43);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Server.Completion.CompletionCollectors.0.Lean.Server.Completion.truncate.go", 89, 89);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1;
x_2 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2;
x_3 = lean_unsigned_to_nat(203u);
x_4 = lean_unsigned_to_nat(26u);
x_5 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_7 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(x_1, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_10, x_11);
x_13 = lean_nat_dec_le(x_1, x_12);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_9);
x_14 = l_Lean_Name_isAnonymous(x_5);
x_15 = lean_string_length(x_6);
if (x_14 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_nat_add(x_12, x_15);
lean_dec(x_15);
lean_dec(x_12);
x_17 = lean_nat_dec_le(x_16, x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_2);
x_18 = lean_nat_sub(x_1, x_11);
x_19 = lean_nat_sub(x_18, x_10);
lean_dec(x_10);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_string_utf8_extract(x_6, x_20, x_19);
lean_dec(x_19);
lean_dec(x_6);
x_22 = l_Lean_Name_str___override(x_5, x_21);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_12);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_add(x_10, x_23);
x_25 = lean_nat_add(x_24, x_15);
lean_dec(x_15);
lean_dec(x_24);
x_26 = lean_nat_dec_le(x_25, x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_2);
x_27 = lean_nat_sub(x_1, x_23);
x_28 = lean_nat_sub(x_27, x_10);
lean_dec(x_10);
lean_dec(x_27);
x_29 = lean_string_utf8_extract(x_6, x_23, x_28);
lean_dec(x_28);
lean_dec(x_6);
x_30 = l_Lean_Name_str___override(x_5, x_29);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_30);
return x_7;
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_2);
return x_7;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_7, 0);
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_7);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_32, x_33);
x_35 = lean_nat_dec_le(x_1, x_34);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; 
lean_dec(x_31);
x_36 = l_Lean_Name_isAnonymous(x_5);
x_37 = lean_string_length(x_6);
if (x_36 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_nat_add(x_34, x_37);
lean_dec(x_37);
lean_dec(x_34);
x_39 = lean_nat_dec_le(x_38, x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_38);
lean_dec(x_2);
x_40 = lean_nat_sub(x_1, x_33);
x_41 = lean_nat_sub(x_40, x_32);
lean_dec(x_32);
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_string_utf8_extract(x_6, x_42, x_41);
lean_dec(x_41);
lean_dec(x_6);
x_44 = l_Lean_Name_str___override(x_5, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_1);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_34);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_add(x_32, x_47);
x_49 = lean_nat_add(x_48, x_37);
lean_dec(x_37);
lean_dec(x_48);
x_50 = lean_nat_dec_le(x_49, x_1);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_49);
lean_dec(x_2);
x_51 = lean_nat_sub(x_1, x_47);
x_52 = lean_nat_sub(x_51, x_32);
lean_dec(x_32);
lean_dec(x_51);
x_53 = lean_string_utf8_extract(x_6, x_47, x_52);
lean_dec(x_52);
lean_dec(x_6);
x_54 = l_Lean_Name_str___override(x_5, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_1);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_34);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_31);
lean_ctor_set(x_57, 1, x_32);
return x_57;
}
}
}
default: 
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_2);
lean_dec(x_1);
x_58 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__4;
x_59 = l_panic___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___spec__1(x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go(x_2, x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1() {
_start:
{
double x_1; lean_object* x_2; 
x_1 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3;
x_2 = lean_box_float(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Completion_matchNamespace___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_matchNamespace(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_name_eq(x_4, x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_7);
x_9 = lean_box(0);
return x_9;
}
else
{
double x_10; lean_object* x_11; 
x_10 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2;
x_11 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_7, x_5, x_10);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_2);
x_13 = lean_box(0);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = lean_name_eq(x_2, x_1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Name_isPrefixOf(x_2, x_1);
lean_dec(x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Server_Completion_matchNamespace___closed__1;
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_box(0);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_matchNamespace___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Server_Completion_matchNamespace(x_1, x_2, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces_visitNamespaces(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
lean_inc(x_5);
x_13 = l_Lean_Name_append(x_5, x_1);
x_14 = l_Lean_Server_Completion_matchNamespace(x_4, x_13, x_2);
if (lean_obj_tag(x_14) == 0)
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_apply_10(x_3, x_4, x_5, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces_visitNamespaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Server_Completion_completeNamespaces_visitNamespaces(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_9);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_1);
lean_inc(x_21);
x_22 = l_Lean_Name_append(x_21, x_1);
lean_inc(x_22);
x_23 = l_Lean_Server_Completion_matchNamespace(x_3, x_22, x_2);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_22);
lean_dec(x_21);
lean_inc(x_6);
{
lean_object* _tmp_7 = x_20;
lean_object* _tmp_8 = x_6;
lean_object* _tmp_9 = lean_box(0);
x_8 = _tmp_7;
x_9 = _tmp_8;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_1);
if (x_2 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; double x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = l_Lean_Name_replacePrefix(x_3, x_21, x_26);
lean_dec(x_21);
x_28 = lean_unbox_float(x_25);
lean_dec(x_25);
x_29 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(x_27, x_28, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2;
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; double x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_21);
x_36 = lean_ctor_get(x_23, 0);
lean_inc(x_36);
lean_dec(x_23);
x_37 = lean_box(0);
x_38 = l_Lean_Name_replacePrefix(x_3, x_22, x_37);
lean_dec(x_22);
x_39 = lean_unbox_float(x_36);
lean_dec(x_36);
x_40 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(x_38, x_39, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2;
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_19);
x_47 = lean_ctor_get(x_8, 1);
lean_inc(x_47);
lean_dec(x_8);
lean_inc(x_6);
{
lean_object* _tmp_7 = x_47;
lean_object* _tmp_8 = x_6;
lean_object* _tmp_9 = lean_box(0);
x_8 = _tmp_7;
x_9 = _tmp_8;
x_10 = _tmp_9;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = lean_apply_9(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_2 = x_16;
x_3 = x_14;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = lean_apply_10(x_1, x_5, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
case 1:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_28 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_1, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_5 = x_29;
x_12 = x_30;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
default: 
{
size_t x_38; size_t x_39; 
x_38 = 1;
x_39 = lean_usize_add(x_3, x_38);
x_3 = x_39;
goto _start;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg___boxed), 12, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_2);
x_15 = lean_nat_dec_lt(x_5, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_fget(x_2, x_5);
x_18 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = lean_apply_10(x_1, x_6, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_23;
x_6 = x_20;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg___boxed), 13, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_12, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg(x_1, x_11, x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg___boxed), 10, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_apply_9(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed), 11, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_box(0);
x_12 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_10, x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
x_15 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__3(x_1, x_15, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_10, 1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 1);
x_16 = l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_18 = lean_ctor_get(x_1, 1);
x_19 = l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9(x_2, x_11, x_20, x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_1, 1);
x_26 = l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
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
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, double x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_1 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = l_Lean_Name_replacePrefix(x_3, x_4, x_13);
lean_dec(x_4);
x_15 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Name_append(x_4, x_2);
x_17 = lean_box(0);
x_18 = l_Lean_Name_replacePrefix(x_3, x_16, x_17);
lean_dec(x_16);
x_19 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Server_Completion_completeNamespaces_visitNamespaces(x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
static lean_object* _init_l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1() {
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
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_Lean_Name_isInternal(x_6);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Environment_contains(x_1, x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_17, 5);
lean_inc(x_18);
x_19 = lean_box(0);
x_20 = l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1;
lean_inc(x_18);
lean_inc(x_6);
lean_inc(x_3);
x_21 = l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1(x_3, x_4, x_6, x_18, x_19, x_20, x_18, x_18, x_20, lean_box(0), x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l_Lean_Server_Completion_completeNamespaces___lambda__2(x_17, x_3, x_4, x_5, x_6, x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_29);
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_14);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_14);
return x_36;
}
}
}
static lean_object* _init_l_Lean_Server_Completion_completeNamespaces___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_namespacesExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(x_3);
lean_inc(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completeNamespaces___lambda__1___boxed), 12, 2);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_2);
x_17 = l_Lean_NameSSet_instInhabited;
x_18 = l_Lean_Server_Completion_completeNamespaces___closed__1;
x_19 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_17, x_18, x_14);
x_20 = lean_box(x_3);
x_21 = lean_alloc_closure((void*)(l_Lean_Server_Completion_completeNamespaces___lambda__3___boxed), 14, 5);
lean_closure_set(x_21, 0, x_14);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_20);
lean_closure_set(x_21, 4, x_16);
x_22 = l_Lean_SMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__2(x_19, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_19);
return x_22;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_2);
lean_dec(x_2);
x_19 = l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__7___rarg(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentHashMap_foldlMAux_traverse___at_Lean_Server_Completion_completeNamespaces___spec__8___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_foldlM___at_Lean_Server_Completion_completeNamespaces___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Server_Completion_completeNamespaces___spec__9(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_SMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; double x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_float(x_5);
lean_dec(x_5);
x_15 = l_Lean_Server_Completion_completeNamespaces___lambda__1(x_13, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Server_Completion_completeNamespaces___lambda__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Server_Completion_completeNamespaces___lambda__3(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_completeNamespaces___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Server_Completion_completeNamespaces(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_unfoldDefinition_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Exception_isInterrupt(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Exception_isRuntime(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
return x_7;
}
}
else
{
return x_7;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = l_Lean_Exception_isInterrupt(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Exception_isRuntime(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(x_20, x_2, x_4, x_5, x_6, x_7, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_9);
x_10 = lean_private_to_user_name(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1(x_1, x_2, x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_9);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_name_eq(x_17, x_2);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1(x_1, x_2, x_19, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
x_24 = lean_box(0);
x_25 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1(x_1, x_2, x_24, x_3, x_4, x_5, x_6, x_7);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_16 = lean_array_uget(x_5, x_7);
x_17 = l_Lean_Expr_fvarId_x21(x_16);
lean_dec(x_16);
lean_inc(x_9);
x_18 = l_Lean_FVarId_getDecl(x_17, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
x_22 = l_Lean_Expr_consumeMData(x_21);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(x_22, x_1, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = 1;
x_28 = lean_usize_add(x_7, x_27);
lean_inc(x_4);
{
size_t _tmp_6 = x_28;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_12 = x_26;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
x_32 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__2;
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 1);
lean_inc(x_33);
lean_dec(x_23);
x_34 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__2;
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_18);
if (x_40 == 0)
{
return x_18;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_box(0);
x_10 = lean_array_size(x_2);
x_11 = 0;
x_12 = l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1(x_1, x_2, x_9, x_12, x_2, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1;
x_18 = lean_box(0);
x_19 = lean_apply_6(x_17, x_18, x_4, x_5, x_6, x_7, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = l_Lean_ConstantInfo_type(x_2);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = 0;
x_11 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_8, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Expr_consumeMData(x_3);
x_10 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDefEqToAppOf(x_9, x_1, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = l_Lean_ConstantInfo_type(x_2);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = 0;
x_11 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_8, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
uint8_t x_5; 
x_5 = l_Lean_isPrivatePrefix(x_1);
if (x_5 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_stripPrivatePrefix(x_2);
lean_dec(x_2);
switch (lean_obj_tag(x_3)) {
case 0:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_string_dec_lt(x_8, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_string_dec_eq(x_8, x_10);
lean_dec(x_10);
lean_dec(x_8);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_7);
x_13 = 2;
return x_13;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_15 = 0;
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = 2;
return x_16;
}
}
default: 
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = 2;
return x_17;
}
case 1:
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_3);
x_18 = 0;
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_nat_dec_lt(x_20, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = lean_nat_dec_eq(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_21);
lean_dec(x_19);
x_25 = 2;
return x_25;
}
else
{
x_1 = x_19;
x_2 = x_21;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_27 = 0;
return x_27;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_inc(x_2);
x_13 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(x_2, x_10);
switch (x_13) {
case 0:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_9, x_2, x_3);
x_15 = 0;
lean_ctor_set(x_1, 0, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_15);
return x_1;
}
case 1:
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
default: 
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_12, x_2, x_3);
x_18 = 0;
lean_ctor_set(x_1, 3, x_17);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_18);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_20);
lean_inc(x_2);
x_23 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(x_2, x_20);
switch (x_23) {
case 0:
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_19, x_2, x_3);
x_25 = 0;
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_20);
lean_ctor_set(x_26, 2, x_21);
lean_ctor_set(x_26, 3, x_22);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_25);
return x_26;
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_22, x_2, x_3);
x_30 = 0;
x_31 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
return x_31;
}
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
lean_inc(x_2);
x_37 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(x_2, x_34);
switch (x_37) {
case 0:
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_33, x_2, x_3);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*4);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_38, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 0);
lean_dec(x_44);
lean_ctor_set(x_38, 0, x_41);
x_45 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_38, 1);
x_47 = lean_ctor_get(x_38, 2);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_39);
x_49 = 1;
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_49);
return x_1;
}
}
else
{
uint8_t x_50; 
x_50 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_38, 1);
x_53 = lean_ctor_get(x_38, 2);
x_54 = lean_ctor_get(x_38, 3);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_41);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_41, 0);
x_58 = lean_ctor_get(x_41, 1);
x_59 = lean_ctor_get(x_41, 2);
x_60 = lean_ctor_get(x_41, 3);
x_61 = 1;
lean_ctor_set(x_41, 3, x_57);
lean_ctor_set(x_41, 2, x_53);
lean_ctor_set(x_41, 1, x_52);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_61);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_60);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_61);
x_62 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; uint8_t x_69; 
x_63 = lean_ctor_get(x_41, 0);
x_64 = lean_ctor_get(x_41, 1);
x_65 = lean_ctor_get(x_41, 2);
x_66 = lean_ctor_get(x_41, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_41);
x_67 = 1;
x_68 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_68, 0, x_40);
lean_ctor_set(x_68, 1, x_52);
lean_ctor_set(x_68, 2, x_53);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_66);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_67);
x_69 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_65);
lean_ctor_set(x_1, 1, x_64);
lean_ctor_set(x_1, 0, x_68);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_70 = lean_ctor_get(x_38, 1);
x_71 = lean_ctor_get(x_38, 2);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_38);
x_72 = lean_ctor_get(x_41, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_41, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_41, 2);
lean_inc(x_74);
x_75 = lean_ctor_get(x_41, 3);
lean_inc(x_75);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_76 = x_41;
} else {
 lean_dec_ref(x_41);
 x_76 = lean_box(0);
}
x_77 = 1;
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(1, 4, 1);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_40);
lean_ctor_set(x_78, 1, x_70);
lean_ctor_set(x_78, 2, x_71);
lean_ctor_set(x_78, 3, x_72);
lean_ctor_set_uint8(x_78, sizeof(void*)*4, x_77);
x_79 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_34);
lean_ctor_set(x_79, 2, x_35);
lean_ctor_set(x_79, 3, x_36);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_77);
x_80 = 0;
lean_ctor_set(x_1, 3, x_79);
lean_ctor_set(x_1, 2, x_74);
lean_ctor_set(x_1, 1, x_73);
lean_ctor_set(x_1, 0, x_78);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_80);
return x_1;
}
}
else
{
uint8_t x_81; 
lean_free_object(x_1);
x_81 = !lean_is_exclusive(x_41);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_41, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_41, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_41, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_41, 0);
lean_dec(x_85);
x_86 = 1;
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 2, x_35);
lean_ctor_set(x_41, 1, x_34);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_86);
return x_41;
}
else
{
uint8_t x_87; lean_object* x_88; 
lean_dec(x_41);
x_87 = 1;
x_88 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_88, 0, x_38);
lean_ctor_set(x_88, 1, x_34);
lean_ctor_set(x_88, 2, x_35);
lean_ctor_set(x_88, 3, x_36);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
x_89 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_89 == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_38);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_91 = lean_ctor_get(x_38, 1);
x_92 = lean_ctor_get(x_38, 2);
x_93 = lean_ctor_get(x_38, 3);
x_94 = lean_ctor_get(x_38, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_40);
if (x_95 == 0)
{
uint8_t x_96; uint8_t x_97; 
x_96 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_96);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_96);
x_97 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_40);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; uint8_t x_104; 
x_98 = lean_ctor_get(x_40, 0);
x_99 = lean_ctor_get(x_40, 1);
x_100 = lean_ctor_get(x_40, 2);
x_101 = lean_ctor_get(x_40, 3);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_40);
x_102 = 1;
x_103 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_99);
lean_ctor_set(x_103, 2, x_100);
lean_ctor_set(x_103, 3, x_101);
lean_ctor_set_uint8(x_103, sizeof(void*)*4, x_102);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 0, x_93);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_102);
x_104 = 0;
lean_ctor_set(x_1, 3, x_38);
lean_ctor_set(x_1, 2, x_92);
lean_ctor_set(x_1, 1, x_91);
lean_ctor_set(x_1, 0, x_103);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_104);
return x_1;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_105 = lean_ctor_get(x_38, 1);
x_106 = lean_ctor_get(x_38, 2);
x_107 = lean_ctor_get(x_38, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_38);
x_108 = lean_ctor_get(x_40, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_40, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_40, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_40, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_112 = x_40;
} else {
 lean_dec_ref(x_40);
 x_112 = lean_box(0);
}
x_113 = 1;
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 4, 1);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_109);
lean_ctor_set(x_114, 2, x_110);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*4, x_113);
x_115 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_34);
lean_ctor_set(x_115, 2, x_35);
lean_ctor_set(x_115, 3, x_36);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_113);
x_116 = 0;
lean_ctor_set(x_1, 3, x_115);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_114);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_116);
return x_1;
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_38, 3);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
lean_free_object(x_1);
x_118 = !lean_is_exclusive(x_40);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_119 = lean_ctor_get(x_40, 3);
lean_dec(x_119);
x_120 = lean_ctor_get(x_40, 2);
lean_dec(x_120);
x_121 = lean_ctor_get(x_40, 1);
lean_dec(x_121);
x_122 = lean_ctor_get(x_40, 0);
lean_dec(x_122);
x_123 = 1;
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_123);
return x_40;
}
else
{
uint8_t x_124; lean_object* x_125; 
lean_dec(x_40);
x_124 = 1;
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_38);
lean_ctor_set(x_125, 1, x_34);
lean_ctor_set(x_125, 2, x_35);
lean_ctor_set(x_125, 3, x_36);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_124);
return x_125;
}
}
else
{
uint8_t x_126; 
x_126 = lean_ctor_get_uint8(x_117, sizeof(void*)*4);
if (x_126 == 0)
{
uint8_t x_127; 
lean_free_object(x_1);
x_127 = !lean_is_exclusive(x_38);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_38, 1);
x_129 = lean_ctor_get(x_38, 2);
x_130 = lean_ctor_get(x_38, 3);
lean_dec(x_130);
x_131 = lean_ctor_get(x_38, 0);
lean_dec(x_131);
x_132 = !lean_is_exclusive(x_117);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_117, 0);
x_134 = lean_ctor_get(x_117, 1);
x_135 = lean_ctor_get(x_117, 2);
x_136 = lean_ctor_get(x_117, 3);
x_137 = 1;
lean_inc(x_40);
lean_ctor_set(x_117, 3, x_133);
lean_ctor_set(x_117, 2, x_129);
lean_ctor_set(x_117, 1, x_128);
lean_ctor_set(x_117, 0, x_40);
x_138 = !lean_is_exclusive(x_40);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_139 = lean_ctor_get(x_40, 3);
lean_dec(x_139);
x_140 = lean_ctor_get(x_40, 2);
lean_dec(x_140);
x_141 = lean_ctor_get(x_40, 1);
lean_dec(x_141);
x_142 = lean_ctor_get(x_40, 0);
lean_dec(x_142);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 2, x_35);
lean_ctor_set(x_40, 1, x_34);
lean_ctor_set(x_40, 0, x_136);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_137);
x_143 = 0;
lean_ctor_set(x_38, 3, x_40);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_143);
return x_38;
}
else
{
lean_object* x_144; uint8_t x_145; 
lean_dec(x_40);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_137);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_34);
lean_ctor_set(x_144, 2, x_35);
lean_ctor_set(x_144, 3, x_36);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_137);
x_145 = 0;
lean_ctor_set(x_38, 3, x_144);
lean_ctor_set(x_38, 2, x_135);
lean_ctor_set(x_38, 1, x_134);
lean_ctor_set(x_38, 0, x_117);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_145);
return x_38;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_146 = lean_ctor_get(x_117, 0);
x_147 = lean_ctor_get(x_117, 1);
x_148 = lean_ctor_get(x_117, 2);
x_149 = lean_ctor_get(x_117, 3);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_117);
x_150 = 1;
lean_inc(x_40);
x_151 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_151, 0, x_40);
lean_ctor_set(x_151, 1, x_128);
lean_ctor_set(x_151, 2, x_129);
lean_ctor_set(x_151, 3, x_146);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_152 = x_40;
} else {
 lean_dec_ref(x_40);
 x_152 = lean_box(0);
}
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 4, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_34);
lean_ctor_set(x_153, 2, x_35);
lean_ctor_set(x_153, 3, x_36);
lean_ctor_set_uint8(x_153, sizeof(void*)*4, x_150);
x_154 = 0;
lean_ctor_set(x_38, 3, x_153);
lean_ctor_set(x_38, 2, x_148);
lean_ctor_set(x_38, 1, x_147);
lean_ctor_set(x_38, 0, x_151);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_154);
return x_38;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_155 = lean_ctor_get(x_38, 1);
x_156 = lean_ctor_get(x_38, 2);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_38);
x_157 = lean_ctor_get(x_117, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_117, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_117, 2);
lean_inc(x_159);
x_160 = lean_ctor_get(x_117, 3);
lean_inc(x_160);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 lean_ctor_release(x_117, 2);
 lean_ctor_release(x_117, 3);
 x_161 = x_117;
} else {
 lean_dec_ref(x_117);
 x_161 = lean_box(0);
}
x_162 = 1;
lean_inc(x_40);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_40);
lean_ctor_set(x_163, 1, x_155);
lean_ctor_set(x_163, 2, x_156);
lean_ctor_set(x_163, 3, x_157);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_164 = x_40;
} else {
 lean_dec_ref(x_40);
 x_164 = lean_box(0);
}
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_162);
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 4, 1);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_160);
lean_ctor_set(x_165, 1, x_34);
lean_ctor_set(x_165, 2, x_35);
lean_ctor_set(x_165, 3, x_36);
lean_ctor_set_uint8(x_165, sizeof(void*)*4, x_162);
x_166 = 0;
x_167 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_167, 0, x_163);
lean_ctor_set(x_167, 1, x_158);
lean_ctor_set(x_167, 2, x_159);
lean_ctor_set(x_167, 3, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*4, x_166);
return x_167;
}
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_38);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_38, 3);
lean_dec(x_169);
x_170 = lean_ctor_get(x_38, 0);
lean_dec(x_170);
x_171 = !lean_is_exclusive(x_40);
if (x_171 == 0)
{
uint8_t x_172; 
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_126);
x_172 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_172);
return x_1;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_173 = lean_ctor_get(x_40, 0);
x_174 = lean_ctor_get(x_40, 1);
x_175 = lean_ctor_get(x_40, 2);
x_176 = lean_ctor_get(x_40, 3);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_40);
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
lean_ctor_set(x_177, 2, x_175);
lean_ctor_set(x_177, 3, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_126);
lean_ctor_set(x_38, 0, x_177);
x_178 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_178);
return x_1;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_179 = lean_ctor_get(x_38, 1);
x_180 = lean_ctor_get(x_38, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_38);
x_181 = lean_ctor_get(x_40, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 3);
lean_inc(x_184);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 x_185 = x_40;
} else {
 lean_dec_ref(x_40);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 4, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_181);
lean_ctor_set(x_186, 1, x_182);
lean_ctor_set(x_186, 2, x_183);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_126);
x_187 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
lean_ctor_set(x_187, 2, x_180);
lean_ctor_set(x_187, 3, x_117);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_39);
x_188 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_188);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_189; 
x_189 = 1;
lean_ctor_set(x_1, 0, x_38);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_189);
return x_1;
}
}
case 1:
{
uint8_t x_190; 
lean_dec(x_35);
lean_dec(x_34);
x_190 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
default: 
{
lean_object* x_191; uint8_t x_192; 
x_191 = l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_36, x_2, x_3);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*4);
if (x_192 == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 3);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_191, 3);
lean_dec(x_196);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
lean_ctor_set(x_191, 0, x_194);
x_198 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_198);
return x_1;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_191, 1);
x_200 = lean_ctor_get(x_191, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_191);
x_201 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_201, 0, x_194);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_194);
lean_ctor_set_uint8(x_201, sizeof(void*)*4, x_192);
x_202 = 1;
lean_ctor_set(x_1, 3, x_201);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_203 == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_191);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_191, 1);
x_206 = lean_ctor_get(x_191, 2);
x_207 = lean_ctor_get(x_191, 3);
lean_dec(x_207);
x_208 = lean_ctor_get(x_191, 0);
lean_dec(x_208);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; 
x_210 = lean_ctor_get(x_194, 0);
x_211 = lean_ctor_get(x_194, 1);
x_212 = lean_ctor_get(x_194, 2);
x_213 = lean_ctor_get(x_194, 3);
x_214 = 1;
lean_ctor_set(x_194, 3, x_193);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_214);
lean_ctor_set(x_191, 3, x_213);
lean_ctor_set(x_191, 2, x_212);
lean_ctor_set(x_191, 1, x_211);
lean_ctor_set(x_191, 0, x_210);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_214);
x_215 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_215);
return x_1;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; uint8_t x_222; 
x_216 = lean_ctor_get(x_194, 0);
x_217 = lean_ctor_get(x_194, 1);
x_218 = lean_ctor_get(x_194, 2);
x_219 = lean_ctor_get(x_194, 3);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_194);
x_220 = 1;
x_221 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_221, 0, x_33);
lean_ctor_set(x_221, 1, x_34);
lean_ctor_set(x_221, 2, x_35);
lean_ctor_set(x_221, 3, x_193);
lean_ctor_set_uint8(x_221, sizeof(void*)*4, x_220);
lean_ctor_set(x_191, 3, x_219);
lean_ctor_set(x_191, 2, x_218);
lean_ctor_set(x_191, 1, x_217);
lean_ctor_set(x_191, 0, x_216);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_220);
x_222 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_221);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_222);
return x_1;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_223 = lean_ctor_get(x_191, 1);
x_224 = lean_ctor_get(x_191, 2);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_191);
x_225 = lean_ctor_get(x_194, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_194, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_194, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_194, 3);
lean_inc(x_228);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_229 = x_194;
} else {
 lean_dec_ref(x_194);
 x_229 = lean_box(0);
}
x_230 = 1;
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 4, 1);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_33);
lean_ctor_set(x_231, 1, x_34);
lean_ctor_set(x_231, 2, x_35);
lean_ctor_set(x_231, 3, x_193);
lean_ctor_set_uint8(x_231, sizeof(void*)*4, x_230);
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_225);
lean_ctor_set(x_232, 1, x_226);
lean_ctor_set(x_232, 2, x_227);
lean_ctor_set(x_232, 3, x_228);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_230);
x_233 = 0;
lean_ctor_set(x_1, 3, x_232);
lean_ctor_set(x_1, 2, x_224);
lean_ctor_set(x_1, 1, x_223);
lean_ctor_set(x_1, 0, x_231);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_234; 
lean_free_object(x_1);
x_234 = !lean_is_exclusive(x_194);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_194, 3);
lean_dec(x_235);
x_236 = lean_ctor_get(x_194, 2);
lean_dec(x_236);
x_237 = lean_ctor_get(x_194, 1);
lean_dec(x_237);
x_238 = lean_ctor_get(x_194, 0);
lean_dec(x_238);
x_239 = 1;
lean_ctor_set(x_194, 3, x_191);
lean_ctor_set(x_194, 2, x_35);
lean_ctor_set(x_194, 1, x_34);
lean_ctor_set(x_194, 0, x_33);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_239);
return x_194;
}
else
{
uint8_t x_240; lean_object* x_241; 
lean_dec(x_194);
x_240 = 1;
x_241 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_241, 0, x_33);
lean_ctor_set(x_241, 1, x_34);
lean_ctor_set(x_241, 2, x_35);
lean_ctor_set(x_241, 3, x_191);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_240);
return x_241;
}
}
}
}
else
{
uint8_t x_242; 
x_242 = lean_ctor_get_uint8(x_193, sizeof(void*)*4);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_191);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_191, 0);
lean_dec(x_244);
x_245 = !lean_is_exclusive(x_193);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; uint8_t x_251; 
x_246 = lean_ctor_get(x_193, 0);
x_247 = lean_ctor_get(x_193, 1);
x_248 = lean_ctor_get(x_193, 2);
x_249 = lean_ctor_get(x_193, 3);
x_250 = 1;
lean_ctor_set(x_193, 3, x_246);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_250);
lean_ctor_set(x_191, 0, x_249);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_250);
x_251 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_193);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_251);
return x_1;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_252 = lean_ctor_get(x_193, 0);
x_253 = lean_ctor_get(x_193, 1);
x_254 = lean_ctor_get(x_193, 2);
x_255 = lean_ctor_get(x_193, 3);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_193);
x_256 = 1;
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_33);
lean_ctor_set(x_257, 1, x_34);
lean_ctor_set(x_257, 2, x_35);
lean_ctor_set(x_257, 3, x_252);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_256);
lean_ctor_set(x_191, 0, x_255);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_256);
x_258 = 0;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set(x_1, 2, x_254);
lean_ctor_set(x_1, 1, x_253);
lean_ctor_set(x_1, 0, x_257);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_258);
return x_1;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_259 = lean_ctor_get(x_191, 1);
x_260 = lean_ctor_get(x_191, 2);
x_261 = lean_ctor_get(x_191, 3);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_191);
x_262 = lean_ctor_get(x_193, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_193, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_193, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_193, 3);
lean_inc(x_265);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_266 = x_193;
} else {
 lean_dec_ref(x_193);
 x_266 = lean_box(0);
}
x_267 = 1;
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(1, 4, 1);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_33);
lean_ctor_set(x_268, 1, x_34);
lean_ctor_set(x_268, 2, x_35);
lean_ctor_set(x_268, 3, x_262);
lean_ctor_set_uint8(x_268, sizeof(void*)*4, x_267);
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_265);
lean_ctor_set(x_269, 1, x_259);
lean_ctor_set(x_269, 2, x_260);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_267);
x_270 = 0;
lean_ctor_set(x_1, 3, x_269);
lean_ctor_set(x_1, 2, x_264);
lean_ctor_set(x_1, 1, x_263);
lean_ctor_set(x_1, 0, x_268);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_191, 3);
lean_inc(x_271);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
lean_free_object(x_1);
x_272 = !lean_is_exclusive(x_193);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_273 = lean_ctor_get(x_193, 3);
lean_dec(x_273);
x_274 = lean_ctor_get(x_193, 2);
lean_dec(x_274);
x_275 = lean_ctor_get(x_193, 1);
lean_dec(x_275);
x_276 = lean_ctor_get(x_193, 0);
lean_dec(x_276);
x_277 = 1;
lean_ctor_set(x_193, 3, x_191);
lean_ctor_set(x_193, 2, x_35);
lean_ctor_set(x_193, 1, x_34);
lean_ctor_set(x_193, 0, x_33);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_277);
return x_193;
}
else
{
uint8_t x_278; lean_object* x_279; 
lean_dec(x_193);
x_278 = 1;
x_279 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_279, 0, x_33);
lean_ctor_set(x_279, 1, x_34);
lean_ctor_set(x_279, 2, x_35);
lean_ctor_set(x_279, 3, x_191);
lean_ctor_set_uint8(x_279, sizeof(void*)*4, x_278);
return x_279;
}
}
else
{
uint8_t x_280; 
x_280 = lean_ctor_get_uint8(x_271, sizeof(void*)*4);
if (x_280 == 0)
{
uint8_t x_281; 
lean_free_object(x_1);
x_281 = !lean_is_exclusive(x_191);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_191, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_191, 0);
lean_dec(x_283);
x_284 = !lean_is_exclusive(x_271);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; 
x_285 = lean_ctor_get(x_271, 0);
x_286 = lean_ctor_get(x_271, 1);
x_287 = lean_ctor_get(x_271, 2);
x_288 = lean_ctor_get(x_271, 3);
x_289 = 1;
lean_inc(x_193);
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 2, x_35);
lean_ctor_set(x_271, 1, x_34);
lean_ctor_set(x_271, 0, x_33);
x_290 = !lean_is_exclusive(x_193);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_291 = lean_ctor_get(x_193, 3);
lean_dec(x_291);
x_292 = lean_ctor_get(x_193, 2);
lean_dec(x_292);
x_293 = lean_ctor_get(x_193, 1);
lean_dec(x_293);
x_294 = lean_ctor_get(x_193, 0);
lean_dec(x_294);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
lean_ctor_set(x_193, 3, x_288);
lean_ctor_set(x_193, 2, x_287);
lean_ctor_set(x_193, 1, x_286);
lean_ctor_set(x_193, 0, x_285);
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_289);
x_295 = 0;
lean_ctor_set(x_191, 3, x_193);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_295);
return x_191;
}
else
{
lean_object* x_296; uint8_t x_297; 
lean_dec(x_193);
lean_ctor_set_uint8(x_271, sizeof(void*)*4, x_289);
x_296 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_286);
lean_ctor_set(x_296, 2, x_287);
lean_ctor_set(x_296, 3, x_288);
lean_ctor_set_uint8(x_296, sizeof(void*)*4, x_289);
x_297 = 0;
lean_ctor_set(x_191, 3, x_296);
lean_ctor_set(x_191, 0, x_271);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_297);
return x_191;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_298 = lean_ctor_get(x_271, 0);
x_299 = lean_ctor_get(x_271, 1);
x_300 = lean_ctor_get(x_271, 2);
x_301 = lean_ctor_get(x_271, 3);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_271);
x_302 = 1;
lean_inc(x_193);
x_303 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_303, 0, x_33);
lean_ctor_set(x_303, 1, x_34);
lean_ctor_set(x_303, 2, x_35);
lean_ctor_set(x_303, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_304 = x_193;
} else {
 lean_dec_ref(x_193);
 x_304 = lean_box(0);
}
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_302);
if (lean_is_scalar(x_304)) {
 x_305 = lean_alloc_ctor(1, 4, 1);
} else {
 x_305 = x_304;
}
lean_ctor_set(x_305, 0, x_298);
lean_ctor_set(x_305, 1, x_299);
lean_ctor_set(x_305, 2, x_300);
lean_ctor_set(x_305, 3, x_301);
lean_ctor_set_uint8(x_305, sizeof(void*)*4, x_302);
x_306 = 0;
lean_ctor_set(x_191, 3, x_305);
lean_ctor_set(x_191, 0, x_303);
lean_ctor_set_uint8(x_191, sizeof(void*)*4, x_306);
return x_191;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; 
x_307 = lean_ctor_get(x_191, 1);
x_308 = lean_ctor_get(x_191, 2);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_191);
x_309 = lean_ctor_get(x_271, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_271, 2);
lean_inc(x_311);
x_312 = lean_ctor_get(x_271, 3);
lean_inc(x_312);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 lean_ctor_release(x_271, 2);
 lean_ctor_release(x_271, 3);
 x_313 = x_271;
} else {
 lean_dec_ref(x_271);
 x_313 = lean_box(0);
}
x_314 = 1;
lean_inc(x_193);
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(1, 4, 1);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_33);
lean_ctor_set(x_315, 1, x_34);
lean_ctor_set(x_315, 2, x_35);
lean_ctor_set(x_315, 3, x_193);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_316 = x_193;
} else {
 lean_dec_ref(x_193);
 x_316 = lean_box(0);
}
lean_ctor_set_uint8(x_315, sizeof(void*)*4, x_314);
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 4, 1);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_310);
lean_ctor_set(x_317, 2, x_311);
lean_ctor_set(x_317, 3, x_312);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_314);
x_318 = 0;
x_319 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_319, 0, x_315);
lean_ctor_set(x_319, 1, x_307);
lean_ctor_set(x_319, 2, x_308);
lean_ctor_set(x_319, 3, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*4, x_318);
return x_319;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_191);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_321 = lean_ctor_get(x_191, 3);
lean_dec(x_321);
x_322 = lean_ctor_get(x_191, 0);
lean_dec(x_322);
x_323 = !lean_is_exclusive(x_193);
if (x_323 == 0)
{
uint8_t x_324; 
lean_ctor_set_uint8(x_193, sizeof(void*)*4, x_280);
x_324 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_324);
return x_1;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; 
x_325 = lean_ctor_get(x_193, 0);
x_326 = lean_ctor_get(x_193, 1);
x_327 = lean_ctor_get(x_193, 2);
x_328 = lean_ctor_get(x_193, 3);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_193);
x_329 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_329, 0, x_325);
lean_ctor_set(x_329, 1, x_326);
lean_ctor_set(x_329, 2, x_327);
lean_ctor_set(x_329, 3, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*4, x_280);
lean_ctor_set(x_191, 0, x_329);
x_330 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_330);
return x_1;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_331 = lean_ctor_get(x_191, 1);
x_332 = lean_ctor_get(x_191, 2);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_191);
x_333 = lean_ctor_get(x_193, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_193, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_193, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_193, 3);
lean_inc(x_336);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 x_337 = x_193;
} else {
 lean_dec_ref(x_193);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_334);
lean_ctor_set(x_338, 2, x_335);
lean_ctor_set(x_338, 3, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_280);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
lean_ctor_set(x_339, 2, x_332);
lean_ctor_set(x_339, 3, x_271);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_192);
x_340 = 1;
lean_ctor_set(x_1, 3, x_339);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_340);
return x_1;
}
}
}
}
}
}
else
{
uint8_t x_341; 
x_341 = 1;
lean_ctor_set(x_1, 3, x_191);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_341);
return x_1;
}
}
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_342 = lean_ctor_get(x_1, 0);
x_343 = lean_ctor_get(x_1, 1);
x_344 = lean_ctor_get(x_1, 2);
x_345 = lean_ctor_get(x_1, 3);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_1);
lean_inc(x_343);
lean_inc(x_2);
x_346 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(x_2, x_343);
switch (x_346) {
case 0:
{
lean_object* x_347; uint8_t x_348; 
x_347 = l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_342, x_2, x_3);
x_348 = lean_ctor_get_uint8(x_347, sizeof(void*)*4);
if (x_348 == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_347, 0);
lean_inc(x_349);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_347, 3);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; 
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_347, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_353 = x_347;
} else {
 lean_dec_ref(x_347);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 4, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_351);
lean_ctor_set(x_354, 2, x_352);
lean_ctor_set(x_354, 3, x_350);
lean_ctor_set_uint8(x_354, sizeof(void*)*4, x_348);
x_355 = 1;
x_356 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_343);
lean_ctor_set(x_356, 2, x_344);
lean_ctor_set(x_356, 3, x_345);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
return x_356;
}
else
{
uint8_t x_357; 
x_357 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_358 = lean_ctor_get(x_347, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_347, 2);
lean_inc(x_359);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_360 = x_347;
} else {
 lean_dec_ref(x_347);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_350, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_350, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_350, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_350, 3);
lean_inc(x_364);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_365 = x_350;
} else {
 lean_dec_ref(x_350);
 x_365 = lean_box(0);
}
x_366 = 1;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_349);
lean_ctor_set(x_367, 1, x_358);
lean_ctor_set(x_367, 2, x_359);
lean_ctor_set(x_367, 3, x_361);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
if (lean_is_scalar(x_360)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_360;
}
lean_ctor_set(x_368, 0, x_364);
lean_ctor_set(x_368, 1, x_343);
lean_ctor_set(x_368, 2, x_344);
lean_ctor_set(x_368, 3, x_345);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_366);
x_369 = 0;
x_370 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_370, 0, x_367);
lean_ctor_set(x_370, 1, x_362);
lean_ctor_set(x_370, 2, x_363);
lean_ctor_set(x_370, 3, x_368);
lean_ctor_set_uint8(x_370, sizeof(void*)*4, x_369);
return x_370;
}
else
{
lean_object* x_371; uint8_t x_372; lean_object* x_373; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_371 = x_350;
} else {
 lean_dec_ref(x_350);
 x_371 = lean_box(0);
}
x_372 = 1;
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(1, 4, 1);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_347);
lean_ctor_set(x_373, 1, x_343);
lean_ctor_set(x_373, 2, x_344);
lean_ctor_set(x_373, 3, x_345);
lean_ctor_set_uint8(x_373, sizeof(void*)*4, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
x_374 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; 
x_375 = lean_ctor_get(x_347, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_347, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_347, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_378 = x_347;
} else {
 lean_dec_ref(x_347);
 x_378 = lean_box(0);
}
x_379 = lean_ctor_get(x_349, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_349, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_349, 2);
lean_inc(x_381);
x_382 = lean_ctor_get(x_349, 3);
lean_inc(x_382);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_383 = x_349;
} else {
 lean_dec_ref(x_349);
 x_383 = lean_box(0);
}
x_384 = 1;
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(1, 4, 1);
} else {
 x_385 = x_383;
}
lean_ctor_set(x_385, 0, x_379);
lean_ctor_set(x_385, 1, x_380);
lean_ctor_set(x_385, 2, x_381);
lean_ctor_set(x_385, 3, x_382);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_384);
if (lean_is_scalar(x_378)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_378;
}
lean_ctor_set(x_386, 0, x_377);
lean_ctor_set(x_386, 1, x_343);
lean_ctor_set(x_386, 2, x_344);
lean_ctor_set(x_386, 3, x_345);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_384);
x_387 = 0;
x_388 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_375);
lean_ctor_set(x_388, 2, x_376);
lean_ctor_set(x_388, 3, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
return x_388;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_347, 3);
lean_inc(x_389);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; uint8_t x_391; lean_object* x_392; 
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_390 = x_349;
} else {
 lean_dec_ref(x_349);
 x_390 = lean_box(0);
}
x_391 = 1;
if (lean_is_scalar(x_390)) {
 x_392 = lean_alloc_ctor(1, 4, 1);
} else {
 x_392 = x_390;
}
lean_ctor_set(x_392, 0, x_347);
lean_ctor_set(x_392, 1, x_343);
lean_ctor_set(x_392, 2, x_344);
lean_ctor_set(x_392, 3, x_345);
lean_ctor_set_uint8(x_392, sizeof(void*)*4, x_391);
return x_392;
}
else
{
uint8_t x_393; 
x_393 = lean_ctor_get_uint8(x_389, sizeof(void*)*4);
if (x_393 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_394 = lean_ctor_get(x_347, 1);
lean_inc(x_394);
x_395 = lean_ctor_get(x_347, 2);
lean_inc(x_395);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_396 = x_347;
} else {
 lean_dec_ref(x_347);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_389, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_389, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_389, 2);
lean_inc(x_399);
x_400 = lean_ctor_get(x_389, 3);
lean_inc(x_400);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 lean_ctor_release(x_389, 2);
 lean_ctor_release(x_389, 3);
 x_401 = x_389;
} else {
 lean_dec_ref(x_389);
 x_401 = lean_box(0);
}
x_402 = 1;
lean_inc(x_349);
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_349);
lean_ctor_set(x_403, 1, x_394);
lean_ctor_set(x_403, 2, x_395);
lean_ctor_set(x_403, 3, x_397);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_404 = x_349;
} else {
 lean_dec_ref(x_349);
 x_404 = lean_box(0);
}
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
if (lean_is_scalar(x_404)) {
 x_405 = lean_alloc_ctor(1, 4, 1);
} else {
 x_405 = x_404;
}
lean_ctor_set(x_405, 0, x_400);
lean_ctor_set(x_405, 1, x_343);
lean_ctor_set(x_405, 2, x_344);
lean_ctor_set(x_405, 3, x_345);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_402);
x_406 = 0;
if (lean_is_scalar(x_396)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_396;
}
lean_ctor_set(x_407, 0, x_403);
lean_ctor_set(x_407, 1, x_398);
lean_ctor_set(x_407, 2, x_399);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_406);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_408 = lean_ctor_get(x_347, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_347, 2);
lean_inc(x_409);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 lean_ctor_release(x_347, 2);
 lean_ctor_release(x_347, 3);
 x_410 = x_347;
} else {
 lean_dec_ref(x_347);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_349, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_349, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_349, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_349, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_415 = x_349;
} else {
 lean_dec_ref(x_349);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 4, 1);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_412);
lean_ctor_set(x_416, 2, x_413);
lean_ctor_set(x_416, 3, x_414);
lean_ctor_set_uint8(x_416, sizeof(void*)*4, x_393);
if (lean_is_scalar(x_410)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_410;
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_408);
lean_ctor_set(x_417, 2, x_409);
lean_ctor_set(x_417, 3, x_389);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_348);
x_418 = 1;
x_419 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_343);
lean_ctor_set(x_419, 2, x_344);
lean_ctor_set(x_419, 3, x_345);
lean_ctor_set_uint8(x_419, sizeof(void*)*4, x_418);
return x_419;
}
}
}
}
}
else
{
uint8_t x_420; lean_object* x_421; 
x_420 = 1;
x_421 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_421, 0, x_347);
lean_ctor_set(x_421, 1, x_343);
lean_ctor_set(x_421, 2, x_344);
lean_ctor_set(x_421, 3, x_345);
lean_ctor_set_uint8(x_421, sizeof(void*)*4, x_420);
return x_421;
}
}
case 1:
{
uint8_t x_422; lean_object* x_423; 
lean_dec(x_344);
lean_dec(x_343);
x_422 = 1;
x_423 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_423, 0, x_342);
lean_ctor_set(x_423, 1, x_2);
lean_ctor_set(x_423, 2, x_3);
lean_ctor_set(x_423, 3, x_345);
lean_ctor_set_uint8(x_423, sizeof(void*)*4, x_422);
return x_423;
}
default: 
{
lean_object* x_424; uint8_t x_425; 
x_424 = l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_345, x_2, x_3);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; 
x_426 = lean_ctor_get(x_424, 0);
lean_inc(x_426);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_424, 3);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; 
x_428 = lean_ctor_get(x_424, 1);
lean_inc(x_428);
x_429 = lean_ctor_get(x_424, 2);
lean_inc(x_429);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_430 = x_424;
} else {
 lean_dec_ref(x_424);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 4, 1);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_427);
lean_ctor_set(x_431, 1, x_428);
lean_ctor_set(x_431, 2, x_429);
lean_ctor_set(x_431, 3, x_427);
lean_ctor_set_uint8(x_431, sizeof(void*)*4, x_425);
x_432 = 1;
x_433 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_433, 0, x_342);
lean_ctor_set(x_433, 1, x_343);
lean_ctor_set(x_433, 2, x_344);
lean_ctor_set(x_433, 3, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*4, x_432);
return x_433;
}
else
{
uint8_t x_434; 
x_434 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; 
x_435 = lean_ctor_get(x_424, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_424, 2);
lean_inc(x_436);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_437 = x_424;
} else {
 lean_dec_ref(x_424);
 x_437 = lean_box(0);
}
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_427, 1);
lean_inc(x_439);
x_440 = lean_ctor_get(x_427, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_427, 3);
lean_inc(x_441);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_442 = x_427;
} else {
 lean_dec_ref(x_427);
 x_442 = lean_box(0);
}
x_443 = 1;
if (lean_is_scalar(x_442)) {
 x_444 = lean_alloc_ctor(1, 4, 1);
} else {
 x_444 = x_442;
}
lean_ctor_set(x_444, 0, x_342);
lean_ctor_set(x_444, 1, x_343);
lean_ctor_set(x_444, 2, x_344);
lean_ctor_set(x_444, 3, x_426);
lean_ctor_set_uint8(x_444, sizeof(void*)*4, x_443);
if (lean_is_scalar(x_437)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_437;
}
lean_ctor_set(x_445, 0, x_438);
lean_ctor_set(x_445, 1, x_439);
lean_ctor_set(x_445, 2, x_440);
lean_ctor_set(x_445, 3, x_441);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_443);
x_446 = 0;
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_435);
lean_ctor_set(x_447, 2, x_436);
lean_ctor_set(x_447, 3, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_446);
return x_447;
}
else
{
lean_object* x_448; uint8_t x_449; lean_object* x_450; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_448 = x_427;
} else {
 lean_dec_ref(x_427);
 x_448 = lean_box(0);
}
x_449 = 1;
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 4, 1);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_342);
lean_ctor_set(x_450, 1, x_343);
lean_ctor_set(x_450, 2, x_344);
lean_ctor_set(x_450, 3, x_424);
lean_ctor_set_uint8(x_450, sizeof(void*)*4, x_449);
return x_450;
}
}
}
else
{
uint8_t x_451; 
x_451 = lean_ctor_get_uint8(x_426, sizeof(void*)*4);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_452 = lean_ctor_get(x_424, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_424, 2);
lean_inc(x_453);
x_454 = lean_ctor_get(x_424, 3);
lean_inc(x_454);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_455 = x_424;
} else {
 lean_dec_ref(x_424);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_426, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_426, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_426, 2);
lean_inc(x_458);
x_459 = lean_ctor_get(x_426, 3);
lean_inc(x_459);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_460 = x_426;
} else {
 lean_dec_ref(x_426);
 x_460 = lean_box(0);
}
x_461 = 1;
if (lean_is_scalar(x_460)) {
 x_462 = lean_alloc_ctor(1, 4, 1);
} else {
 x_462 = x_460;
}
lean_ctor_set(x_462, 0, x_342);
lean_ctor_set(x_462, 1, x_343);
lean_ctor_set(x_462, 2, x_344);
lean_ctor_set(x_462, 3, x_456);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
if (lean_is_scalar(x_455)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_455;
}
lean_ctor_set(x_463, 0, x_459);
lean_ctor_set(x_463, 1, x_452);
lean_ctor_set(x_463, 2, x_453);
lean_ctor_set(x_463, 3, x_454);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_461);
x_464 = 0;
x_465 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_457);
lean_ctor_set(x_465, 2, x_458);
lean_ctor_set(x_465, 3, x_463);
lean_ctor_set_uint8(x_465, sizeof(void*)*4, x_464);
return x_465;
}
else
{
lean_object* x_466; 
x_466 = lean_ctor_get(x_424, 3);
lean_inc(x_466);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; uint8_t x_468; lean_object* x_469; 
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_467 = x_426;
} else {
 lean_dec_ref(x_426);
 x_467 = lean_box(0);
}
x_468 = 1;
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(1, 4, 1);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_342);
lean_ctor_set(x_469, 1, x_343);
lean_ctor_set(x_469, 2, x_344);
lean_ctor_set(x_469, 3, x_424);
lean_ctor_set_uint8(x_469, sizeof(void*)*4, x_468);
return x_469;
}
else
{
uint8_t x_470; 
x_470 = lean_ctor_get_uint8(x_466, sizeof(void*)*4);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; 
x_471 = lean_ctor_get(x_424, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_424, 2);
lean_inc(x_472);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_473 = x_424;
} else {
 lean_dec_ref(x_424);
 x_473 = lean_box(0);
}
x_474 = lean_ctor_get(x_466, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 2);
lean_inc(x_476);
x_477 = lean_ctor_get(x_466, 3);
lean_inc(x_477);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 x_478 = x_466;
} else {
 lean_dec_ref(x_466);
 x_478 = lean_box(0);
}
x_479 = 1;
lean_inc(x_426);
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_342);
lean_ctor_set(x_480, 1, x_343);
lean_ctor_set(x_480, 2, x_344);
lean_ctor_set(x_480, 3, x_426);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_481 = x_426;
} else {
 lean_dec_ref(x_426);
 x_481 = lean_box(0);
}
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_479);
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 4, 1);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_474);
lean_ctor_set(x_482, 1, x_475);
lean_ctor_set(x_482, 2, x_476);
lean_ctor_set(x_482, 3, x_477);
lean_ctor_set_uint8(x_482, sizeof(void*)*4, x_479);
x_483 = 0;
if (lean_is_scalar(x_473)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_473;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_471);
lean_ctor_set(x_484, 2, x_472);
lean_ctor_set(x_484, 3, x_482);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_483);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; 
x_485 = lean_ctor_get(x_424, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_424, 2);
lean_inc(x_486);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 x_487 = x_424;
} else {
 lean_dec_ref(x_424);
 x_487 = lean_box(0);
}
x_488 = lean_ctor_get(x_426, 0);
lean_inc(x_488);
x_489 = lean_ctor_get(x_426, 1);
lean_inc(x_489);
x_490 = lean_ctor_get(x_426, 2);
lean_inc(x_490);
x_491 = lean_ctor_get(x_426, 3);
lean_inc(x_491);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 x_492 = x_426;
} else {
 lean_dec_ref(x_426);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 4, 1);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_489);
lean_ctor_set(x_493, 2, x_490);
lean_ctor_set(x_493, 3, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_470);
if (lean_is_scalar(x_487)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_487;
}
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_485);
lean_ctor_set(x_494, 2, x_486);
lean_ctor_set(x_494, 3, x_466);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_425);
x_495 = 1;
x_496 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_496, 0, x_342);
lean_ctor_set(x_496, 1, x_343);
lean_ctor_set(x_496, 2, x_344);
lean_ctor_set(x_496, 3, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*4, x_495);
return x_496;
}
}
}
}
}
else
{
uint8_t x_497; lean_object* x_498; 
x_497 = 1;
x_498 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_498, 0, x_342);
lean_ctor_set(x_498, 1, x_343);
lean_ctor_set(x_498, 2, x_344);
lean_ctor_set(x_498, 3, x_424);
lean_ctor_set_uint8(x_498, sizeof(void*)*4, x_497);
return x_498;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_RBNode_ins___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__2(x_1, x_2, x_3);
x_7 = l_Lean_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = 1;
x_16 = l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5(x_12, x_15, x_4, x_5, x_6, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_14, x_2, x_19);
x_2 = x_21;
x_3 = x_22;
x_9 = x_18;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
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
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
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
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Array_toSubarray___rarg(x_6, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_10);
x_18 = lean_nat_dec_le(x_12, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_11, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
goto _start;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8(x_1, x_10, x_23, x_24);
lean_dec(x_10);
if (x_25 == 0)
{
size_t x_26; size_t x_27; 
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
lean_dec(x_17);
x_30 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_31 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_32 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9(x_1, x_10, x_30, x_31);
lean_dec(x_10);
if (x_32 == 0)
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = 1;
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
x_37 = 0;
return x_37;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Array_toSubarray___rarg(x_6, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_10);
x_18 = lean_nat_dec_le(x_12, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_11, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
goto _start;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8(x_1, x_10, x_23, x_24);
lean_dec(x_10);
if (x_25 == 0)
{
size_t x_26; size_t x_27; 
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
lean_dec(x_17);
x_30 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_31 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_32 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9(x_1, x_10, x_30, x_31);
lean_dec(x_10);
if (x_32 == 0)
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = 1;
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
x_37 = 0;
return x_37;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
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
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
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
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Array_toSubarray___rarg(x_6, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_10);
x_18 = lean_nat_dec_le(x_12, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_11, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
goto _start;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12(x_1, x_10, x_23, x_24);
lean_dec(x_10);
if (x_25 == 0)
{
size_t x_26; size_t x_27; 
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
lean_dec(x_17);
x_30 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_31 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_32 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13(x_1, x_10, x_30, x_31);
lean_dec(x_10);
if (x_32 == 0)
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = 1;
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
x_37 = 0;
return x_37;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Array_toSubarray___rarg(x_6, x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 2);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
size_t x_14; size_t x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_10);
x_18 = lean_nat_dec_le(x_12, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = lean_nat_dec_lt(x_11, x_17);
if (x_19 == 0)
{
size_t x_20; size_t x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
goto _start;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12(x_1, x_10, x_23, x_24);
lean_dec(x_10);
if (x_25 == 0)
{
size_t x_26; size_t x_27; 
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = 1;
return x_29;
}
}
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
lean_dec(x_17);
x_30 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_31 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_32 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13(x_1, x_10, x_30, x_31);
lean_dec(x_10);
if (x_32 == 0)
{
size_t x_33; size_t x_34; 
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
goto _start;
}
else
{
uint8_t x_36; 
x_36 = 1;
return x_36;
}
}
}
}
else
{
uint8_t x_37; 
x_37 = 0;
return x_37;
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_11, x_8);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_10, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
lean_dec(x_13);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_10, x_24);
lean_dec(x_10);
x_26 = lean_nat_dec_lt(x_11, x_2);
lean_inc(x_11);
lean_inc(x_1);
x_27 = l_Array_toSubarray___rarg(x_1, x_22, x_11);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 2);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_26 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___closed__1;
x_86 = l_outOfBounds___rarg(x_85);
x_87 = lean_array_get_size(x_86);
x_88 = lean_nat_dec_lt(x_22, x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_86);
x_89 = l_Lean_instInhabitedName;
x_90 = l_outOfBounds___rarg(x_89);
x_32 = x_90;
goto block_84;
}
else
{
lean_object* x_91; 
x_91 = lean_array_fget(x_86, x_22);
lean_dec(x_86);
x_32 = x_91;
goto block_84;
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_array_fget(x_1, x_11);
x_93 = lean_array_get_size(x_92);
x_94 = lean_nat_dec_lt(x_22, x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_92);
x_95 = l_Lean_instInhabitedName;
x_96 = l_outOfBounds___rarg(x_95);
x_32 = x_96;
goto block_84;
}
else
{
lean_object* x_97; 
x_97 = lean_array_fget(x_92, x_22);
lean_dec(x_92);
x_32 = x_97;
goto block_84;
}
}
block_84:
{
lean_object* x_33; lean_object* x_42; 
if (x_31 == 0)
{
lean_object* x_67; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
x_67 = lean_box(0);
x_42 = x_67;
goto block_66;
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_array_get_size(x_28);
x_69 = lean_nat_dec_le(x_30, x_68);
if (x_69 == 0)
{
uint8_t x_70; 
lean_dec(x_30);
x_70 = lean_nat_dec_lt(x_29, x_68);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_29);
lean_dec(x_28);
x_71 = lean_box(0);
x_42 = x_71;
goto block_66;
}
else
{
size_t x_72; size_t x_73; uint8_t x_74; 
x_72 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_73 = lean_usize_of_nat(x_68);
lean_dec(x_68);
x_74 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14(x_32, x_28, x_72, x_73);
lean_dec(x_28);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_box(0);
x_42 = x_75;
goto block_66;
}
else
{
lean_object* x_76; 
lean_dec(x_32);
x_76 = lean_nat_add(x_11, x_9);
lean_dec(x_11);
lean_inc(x_3);
{
lean_object* _tmp_9 = x_25;
lean_object* _tmp_10 = x_76;
lean_object* _tmp_11 = lean_box(0);
lean_object* _tmp_12 = x_3;
x_10 = _tmp_9;
x_11 = _tmp_10;
x_12 = _tmp_11;
x_13 = _tmp_12;
}
goto _start;
}
}
}
else
{
size_t x_78; size_t x_79; uint8_t x_80; 
lean_dec(x_68);
x_78 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_79 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_80 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15(x_32, x_28, x_78, x_79);
lean_dec(x_28);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_box(0);
x_42 = x_81;
goto block_66;
}
else
{
lean_object* x_82; 
lean_dec(x_32);
x_82 = lean_nat_add(x_11, x_9);
lean_dec(x_11);
lean_inc(x_3);
{
lean_object* _tmp_9 = x_25;
lean_object* _tmp_10 = x_82;
lean_object* _tmp_11 = lean_box(0);
lean_object* _tmp_12 = x_3;
x_10 = _tmp_9;
x_11 = _tmp_10;
x_12 = _tmp_11;
x_13 = _tmp_12;
}
goto _start;
}
}
}
block_41:
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_33);
x_34 = lean_nat_dec_eq(x_4, x_22);
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_19);
return x_40;
}
block_66:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_42);
x_43 = lean_nat_add(x_11, x_24);
lean_inc(x_5);
lean_inc(x_1);
x_44 = l_Array_toSubarray___rarg(x_1, x_43, x_5);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 2);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_box(0);
x_33 = x_49;
goto block_41;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_47, x_50);
if (x_51 == 0)
{
uint8_t x_52; 
lean_dec(x_47);
x_52 = lean_nat_dec_lt(x_46, x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_53 = lean_box(0);
x_33 = x_53;
goto block_41;
}
else
{
size_t x_54; size_t x_55; uint8_t x_56; 
x_54 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_55 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_56 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10(x_32, x_45, x_54, x_55);
lean_dec(x_45);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_box(0);
x_33 = x_57;
goto block_41;
}
else
{
lean_object* x_58; 
lean_dec(x_32);
x_58 = lean_nat_add(x_11, x_9);
lean_dec(x_11);
lean_inc(x_3);
{
lean_object* _tmp_9 = x_25;
lean_object* _tmp_10 = x_58;
lean_object* _tmp_11 = lean_box(0);
lean_object* _tmp_12 = x_3;
x_10 = _tmp_9;
x_11 = _tmp_10;
x_12 = _tmp_11;
x_13 = _tmp_12;
}
goto _start;
}
}
}
else
{
size_t x_60; size_t x_61; uint8_t x_62; 
lean_dec(x_50);
x_60 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_61 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_62 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11(x_32, x_45, x_60, x_61);
lean_dec(x_45);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_63 = lean_box(0);
x_33 = x_63;
goto block_41;
}
else
{
lean_object* x_64; 
lean_dec(x_32);
x_64 = lean_nat_add(x_11, x_9);
lean_dec(x_11);
lean_inc(x_3);
{
lean_object* _tmp_9 = x_25;
lean_object* _tmp_10 = x_64;
lean_object* _tmp_11 = lean_box(0);
lean_object* _tmp_12 = x_3;
x_10 = _tmp_9;
x_11 = _tmp_10;
x_12 = _tmp_11;
x_13 = _tmp_12;
}
goto _start;
}
}
}
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_13);
lean_ctor_set(x_98, 1, x_19);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_9, x_6);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_8, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_8, x_22);
lean_dec(x_8);
x_24 = lean_nat_sub(x_2, x_9);
lean_inc(x_24);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_inc_n(x_24, 2);
lean_inc_n(x_4, 2);
lean_inc(x_1);
x_26 = l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16(x_1, x_2, x_4, x_9, x_24, x_25, x_20, x_24, x_22, x_24, x_20, lean_box(0), x_4, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_25);
lean_dec(x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_nat_add(x_9, x_7);
lean_dec(x_9);
lean_inc(x_4);
{
lean_object* _tmp_7 = x_23;
lean_object* _tmp_8 = x_30;
lean_object* _tmp_9 = lean_box(0);
lean_object* _tmp_10 = x_4;
lean_object* _tmp_16 = x_29;
x_8 = _tmp_7;
x_9 = _tmp_8;
x_10 = _tmp_9;
x_11 = _tmp_10;
x_17 = _tmp_16;
}
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_26, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_26, 0, x_40);
return x_26;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_43 = x_28;
} else {
 lean_dec_ref(x_28);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_11);
lean_ctor_set(x_48, 1, x_17);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___closed__1;
x_13 = l_outOfBounds___rarg(x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_10, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
x_16 = l_Lean_instInhabitedName;
x_17 = l_outOfBounds___rarg(x_16);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_array_fget(x_13, x_10);
lean_dec(x_13);
x_23 = 0;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_9);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_fget(x_2, x_10);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_10, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_27);
x_30 = l_Lean_instInhabitedName;
x_31 = l_outOfBounds___rarg(x_30);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_array_fget(x_27, x_10);
lean_dec(x_27);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_9);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(1u);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1;
lean_inc(x_8);
lean_inc(x_1);
x_13 = l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17(x_1, x_8, x_11, x_12, x_9, x_8, x_10, x_8, x_9, lean_box(0), x_12, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7___lambda__1(x_8, x_1, x_17, x_2, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_1);
lean_dec(x_8);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_name_eq(x_7, x_1);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (x_8 == 0)
{
lean_object* x_11; 
x_11 = lean_array_push(x_5, x_7);
x_3 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19(size_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; size_t x_14; size_t x_15; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_6, x_5, x_9);
x_11 = lean_array_get_size(x_8);
lean_inc(x_2);
x_12 = lean_array_mk(x_2);
x_13 = lean_nat_dec_lt(x_9, x_11);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
if (x_13 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_8);
x_16 = lean_array_uset(x_10, x_5, x_12);
x_5 = x_15;
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_11, x_11);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_8);
x_19 = lean_array_uset(x_10, x_5, x_12);
x_5 = x_15;
x_6 = x_19;
goto _start;
}
else
{
size_t x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_22 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18(x_3, x_8, x_1, x_21, x_12);
lean_dec(x_8);
x_23 = lean_array_uset(x_10, x_5, x_22);
x_5 = x_15;
x_6 = x_23;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
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
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_6);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
x_12 = 1;
x_13 = lean_usize_add(x_3, x_12);
x_14 = lean_array_uset(x_8, x_3, x_11);
x_3 = x_13;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; size_t x_15; size_t x_16; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(1u);
lean_inc(x_7);
x_10 = l_Array_toSubarray___rarg(x_7, x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_nat_dec_lt(x_12, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_get_size(x_11);
x_19 = lean_nat_dec_le(x_13, x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_13);
x_20 = lean_nat_dec_lt(x_12, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
x_3 = x_16;
goto _start;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_23 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_24 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20(x_1, x_11, x_22, x_23);
lean_dec(x_11);
if (x_24 == 0)
{
lean_dec(x_7);
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_26; 
x_26 = lean_array_push(x_5, x_7);
x_3 = x_16;
x_5 = x_26;
goto _start;
}
}
}
else
{
size_t x_28; size_t x_29; uint8_t x_30; 
lean_dec(x_18);
x_28 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_29 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_30 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_11, x_28, x_29);
lean_dec(x_11);
if (x_30 == 0)
{
lean_dec(x_7);
x_3 = x_16;
goto _start;
}
else
{
lean_object* x_32; 
x_32 = lean_array_push(x_5, x_7);
x_3 = x_16;
x_5 = x_32;
goto _start;
}
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_1);
x_15 = lean_array_push(x_6, x_1);
x_16 = lean_array_size(x_7);
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19(x_2, x_3, x_1, x_16, x_2, x_7);
lean_dec(x_1);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_18, x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_14);
return x_29;
}
else
{
size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_31 = l_Array_foldlMUnsafe_fold___at_Lean_computeStructureResolutionOrder___spec__5(x_17, x_2, x_30, x_4);
lean_dec(x_17);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_14);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Array_isEmpty___rarg(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_14);
lean_free_object(x_6);
lean_inc(x_18);
x_20 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_18, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
if (x_1 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_43; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_array_get_size(x_18);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
x_29 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_3, x_25);
if (x_28 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_26, x_26);
if (x_54 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
size_t x_55; lean_object* x_56; 
x_55 = lean_usize_of_nat(x_26);
lean_dec(x_26);
lean_inc(x_4);
x_56 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_25, x_18, x_2, x_55, x_4);
x_43 = x_56;
goto block_53;
}
}
block_42:
{
lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = l_Array_eraseReps___at_Lean_computeStructureResolutionOrder___spec__8(x_30);
lean_dec(x_30);
x_32 = lean_array_size(x_31);
x_33 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_3, x_32, x_2, x_31);
lean_inc(x_25);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_29);
x_35 = lean_array_push(x_16, x_34);
x_36 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_37 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_25, x_2, x_5, x_4, x_35, x_17, x_18, x_36, x_7, x_8, x_9, x_10, x_11, x_24);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_6 = x_40;
x_12 = x_39;
goto _start;
}
block_53:
{
size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_array_size(x_43);
x_45 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__11(x_44, x_2, x_43);
x_46 = lean_array_get_size(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_46, x_47);
x_49 = lean_nat_dec_eq(x_46, x_27);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_27, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_inc(x_48);
x_51 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_46, x_45, x_48, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_51;
goto block_42;
}
else
{
lean_object* x_52; 
x_52 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_46, x_45, x_27, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_52;
goto block_42;
}
}
else
{
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_45;
goto block_42;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_dec(x_20);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_dec(x_21);
x_59 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_60 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_58, x_2, x_5, x_4, x_16, x_17, x_18, x_59, x_7, x_8, x_9, x_10, x_11, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_6 = x_63;
x_12 = x_62;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_dec(x_20);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_dec(x_21);
x_67 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_68 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_66, x_2, x_5, x_4, x_16, x_17, x_18, x_67, x_7, x_8, x_9, x_10, x_11, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_6 = x_71;
x_12 = x_70;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_5);
lean_dec(x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_6, 0);
x_75 = lean_ctor_get(x_14, 0);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_14);
x_77 = l_Array_isEmpty___rarg(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_free_object(x_6);
lean_inc(x_76);
x_78 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_76, x_7, x_8, x_9, x_10, x_11, x_12);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
if (x_1 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_101; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_array_get_size(x_76);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
x_87 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_3, x_83);
if (x_86 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_84, x_84);
if (x_112 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
size_t x_113; lean_object* x_114; 
x_113 = lean_usize_of_nat(x_84);
lean_dec(x_84);
lean_inc(x_4);
x_114 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_83, x_76, x_2, x_113, x_4);
x_101 = x_114;
goto block_111;
}
}
block_100:
{
lean_object* x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = l_Array_eraseReps___at_Lean_computeStructureResolutionOrder___spec__8(x_88);
lean_dec(x_88);
x_90 = lean_array_size(x_89);
x_91 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_3, x_90, x_2, x_89);
lean_inc(x_83);
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_87);
x_93 = lean_array_push(x_74, x_92);
x_94 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_95 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_83, x_2, x_5, x_4, x_93, x_75, x_76, x_94, x_7, x_8, x_9, x_10, x_11, x_82);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_6 = x_98;
x_12 = x_97;
goto _start;
}
block_111:
{
size_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_array_size(x_101);
x_103 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__11(x_102, x_2, x_101);
x_104 = lean_array_get_size(x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_104, x_105);
x_107 = lean_nat_dec_eq(x_104, x_85);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_85, x_106);
if (x_108 == 0)
{
lean_object* x_109; 
lean_inc(x_106);
x_109 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_104, x_103, x_106, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_109;
goto block_100;
}
else
{
lean_object* x_110; 
x_110 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_104, x_103, x_85, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_110;
goto block_100;
}
}
else
{
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_103;
goto block_100;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_78, 1);
lean_inc(x_115);
lean_dec(x_78);
x_116 = lean_ctor_get(x_79, 1);
lean_inc(x_116);
lean_dec(x_79);
x_117 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_118 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_116, x_2, x_5, x_4, x_74, x_75, x_76, x_117, x_7, x_8, x_9, x_10, x_11, x_115);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_6 = x_121;
x_12 = x_120;
goto _start;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_78, 1);
lean_inc(x_123);
lean_dec(x_78);
x_124 = lean_ctor_get(x_79, 1);
lean_inc(x_124);
lean_dec(x_79);
x_125 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_126 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_124, x_2, x_5, x_4, x_74, x_75, x_76, x_125, x_7, x_8, x_9, x_10, x_11, x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_6 = x_129;
x_12 = x_128;
goto _start;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_5);
lean_dec(x_4);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_75);
lean_ctor_set(x_131, 1, x_76);
lean_ctor_set(x_6, 1, x_131);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_6);
lean_ctor_set(x_132, 1, x_12);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_6, 1);
x_134 = lean_ctor_get(x_6, 0);
lean_inc(x_133);
lean_inc(x_134);
lean_dec(x_6);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
x_138 = l_Array_isEmpty___rarg(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_137);
lean_inc(x_136);
x_139 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_136, x_7, x_8, x_9, x_10, x_11, x_12);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
if (x_1 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_162; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_array_get_size(x_136);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_lt(x_146, x_145);
x_148 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_3, x_144);
if (x_147 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_145, x_145);
if (x_173 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
size_t x_174; lean_object* x_175; 
x_174 = lean_usize_of_nat(x_145);
lean_dec(x_145);
lean_inc(x_4);
x_175 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_144, x_136, x_2, x_174, x_4);
x_162 = x_175;
goto block_172;
}
}
block_161:
{
lean_object* x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_150 = l_Array_eraseReps___at_Lean_computeStructureResolutionOrder___spec__8(x_149);
lean_dec(x_149);
x_151 = lean_array_size(x_150);
x_152 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_3, x_151, x_2, x_150);
lean_inc(x_144);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_148);
x_154 = lean_array_push(x_134, x_153);
x_155 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_156 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_144, x_2, x_5, x_4, x_154, x_135, x_136, x_155, x_7, x_8, x_9, x_10, x_11, x_143);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_6 = x_159;
x_12 = x_158;
goto _start;
}
block_172:
{
size_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_array_size(x_162);
x_164 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__11(x_163, x_2, x_162);
x_165 = lean_array_get_size(x_164);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_sub(x_165, x_166);
x_168 = lean_nat_dec_eq(x_165, x_146);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_146, x_167);
if (x_169 == 0)
{
lean_object* x_170; 
lean_inc(x_167);
x_170 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_165, x_164, x_167, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_170;
goto block_161;
}
else
{
lean_object* x_171; 
x_171 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_165, x_164, x_146, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_171;
goto block_161;
}
}
else
{
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_164;
goto block_161;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_139, 1);
lean_inc(x_176);
lean_dec(x_139);
x_177 = lean_ctor_get(x_140, 1);
lean_inc(x_177);
lean_dec(x_140);
x_178 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_179 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_177, x_2, x_5, x_4, x_134, x_135, x_136, x_178, x_7, x_8, x_9, x_10, x_11, x_176);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
x_6 = x_182;
x_12 = x_181;
goto _start;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_139, 1);
lean_inc(x_184);
lean_dec(x_139);
x_185 = lean_ctor_get(x_140, 1);
lean_inc(x_185);
lean_dec(x_140);
x_186 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_187 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_185, x_2, x_5, x_4, x_134, x_135, x_136, x_186, x_7, x_8, x_9, x_10, x_11, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec(x_188);
x_6 = x_190;
x_12 = x_189;
goto _start;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_137)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_137;
}
lean_ctor_set(x_192, 0, x_135);
lean_ctor_set(x_192, 1, x_136);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_134);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_12);
return x_194;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_insert___at___private_Lean_Structure_0__Lean_setStructureResolutionOrder___spec__1(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_structureResolutionExt;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__3;
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
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 4);
lean_dec(x_14);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___lambda__1), 3, 2);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
x_16 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__1;
x_17 = l_Lean_EnvExtension_modifyState___rarg(x_16, x_13, x_15);
x_18 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__4;
lean_ctor_set(x_10, 4, x_18);
lean_ctor_set(x_10, 0, x_17);
x_19 = lean_st_ref_set(x_7, x_10, x_11);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_take(x_5, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_22, 1);
lean_dec(x_25);
x_26 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__5;
lean_ctor_set(x_22, 1, x_26);
x_27 = lean_st_ref_set(x_5, x_22, x_23);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 2);
x_36 = lean_ctor_get(x_22, 3);
x_37 = lean_ctor_get(x_22, 4);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_38 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__5;
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_35);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_37);
x_40 = lean_st_ref_set(x_5, x_39, x_23);
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
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
x_47 = lean_ctor_get(x_10, 2);
x_48 = lean_ctor_get(x_10, 3);
x_49 = lean_ctor_get(x_10, 5);
x_50 = lean_ctor_get(x_10, 6);
x_51 = lean_ctor_get(x_10, 7);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
x_52 = lean_alloc_closure((void*)(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___lambda__1), 3, 2);
lean_closure_set(x_52, 0, x_1);
lean_closure_set(x_52, 1, x_2);
x_53 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__1;
x_54 = l_Lean_EnvExtension_modifyState___rarg(x_53, x_45, x_52);
x_55 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__4;
x_56 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_47);
lean_ctor_set(x_56, 3, x_48);
lean_ctor_set(x_56, 4, x_55);
lean_ctor_set(x_56, 5, x_49);
lean_ctor_set(x_56, 6, x_50);
lean_ctor_set(x_56, 7, x_51);
x_57 = lean_st_ref_set(x_7, x_56, x_11);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_take(x_5, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 4);
lean_inc(x_65);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 lean_ctor_release(x_60, 4);
 x_66 = x_60;
} else {
 lean_dec_ref(x_60);
 x_66 = lean_box(0);
}
x_67 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__5;
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 5, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_63);
lean_ctor_set(x_68, 3, x_64);
lean_ctor_set(x_68, 4, x_65);
x_69 = lean_st_ref_set(x_5, x_68, x_61);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Array_isEmpty___rarg(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_14);
lean_free_object(x_6);
lean_inc(x_18);
x_20 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_18, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
if (x_1 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_43; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_array_get_size(x_18);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
x_29 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_3, x_25);
if (x_28 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_26, x_26);
if (x_54 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
size_t x_55; lean_object* x_56; 
x_55 = lean_usize_of_nat(x_26);
lean_dec(x_26);
lean_inc(x_4);
x_56 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_25, x_18, x_2, x_55, x_4);
x_43 = x_56;
goto block_53;
}
}
block_42:
{
lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = l_Array_eraseReps___at_Lean_computeStructureResolutionOrder___spec__8(x_30);
lean_dec(x_30);
x_32 = lean_array_size(x_31);
x_33 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_3, x_32, x_2, x_31);
lean_inc(x_25);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_29);
x_35 = lean_array_push(x_16, x_34);
x_36 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_37 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_25, x_2, x_5, x_4, x_35, x_17, x_18, x_36, x_7, x_8, x_9, x_10, x_11, x_24);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_6 = x_40;
x_12 = x_39;
goto _start;
}
block_53:
{
size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_array_size(x_43);
x_45 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__11(x_44, x_2, x_43);
x_46 = lean_array_get_size(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_46, x_47);
x_49 = lean_nat_dec_eq(x_46, x_27);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_27, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_inc(x_48);
x_51 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_46, x_45, x_48, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_51;
goto block_42;
}
else
{
lean_object* x_52; 
x_52 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_46, x_45, x_27, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_52;
goto block_42;
}
}
else
{
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_45;
goto block_42;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_dec(x_20);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_dec(x_21);
x_59 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_60 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_58, x_2, x_5, x_4, x_16, x_17, x_18, x_59, x_7, x_8, x_9, x_10, x_11, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_6 = x_63;
x_12 = x_62;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_dec(x_20);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_dec(x_21);
x_67 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_68 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_66, x_2, x_5, x_4, x_16, x_17, x_18, x_67, x_7, x_8, x_9, x_10, x_11, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_6 = x_71;
x_12 = x_70;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_5);
lean_dec(x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_6, 0);
x_75 = lean_ctor_get(x_14, 0);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_14);
x_77 = l_Array_isEmpty___rarg(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_free_object(x_6);
lean_inc(x_76);
x_78 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_76, x_7, x_8, x_9, x_10, x_11, x_12);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
if (x_1 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_101; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_array_get_size(x_76);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
x_87 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_3, x_83);
if (x_86 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_84, x_84);
if (x_112 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
size_t x_113; lean_object* x_114; 
x_113 = lean_usize_of_nat(x_84);
lean_dec(x_84);
lean_inc(x_4);
x_114 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_83, x_76, x_2, x_113, x_4);
x_101 = x_114;
goto block_111;
}
}
block_100:
{
lean_object* x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = l_Array_eraseReps___at_Lean_computeStructureResolutionOrder___spec__8(x_88);
lean_dec(x_88);
x_90 = lean_array_size(x_89);
x_91 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_3, x_90, x_2, x_89);
lean_inc(x_83);
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_87);
x_93 = lean_array_push(x_74, x_92);
x_94 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_95 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_83, x_2, x_5, x_4, x_93, x_75, x_76, x_94, x_7, x_8, x_9, x_10, x_11, x_82);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_6 = x_98;
x_12 = x_97;
goto _start;
}
block_111:
{
size_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_array_size(x_101);
x_103 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__11(x_102, x_2, x_101);
x_104 = lean_array_get_size(x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_104, x_105);
x_107 = lean_nat_dec_eq(x_104, x_85);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_85, x_106);
if (x_108 == 0)
{
lean_object* x_109; 
lean_inc(x_106);
x_109 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_104, x_103, x_106, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_109;
goto block_100;
}
else
{
lean_object* x_110; 
x_110 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_104, x_103, x_85, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_110;
goto block_100;
}
}
else
{
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_103;
goto block_100;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_78, 1);
lean_inc(x_115);
lean_dec(x_78);
x_116 = lean_ctor_get(x_79, 1);
lean_inc(x_116);
lean_dec(x_79);
x_117 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_118 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_116, x_2, x_5, x_4, x_74, x_75, x_76, x_117, x_7, x_8, x_9, x_10, x_11, x_115);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_6 = x_121;
x_12 = x_120;
goto _start;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_78, 1);
lean_inc(x_123);
lean_dec(x_78);
x_124 = lean_ctor_get(x_79, 1);
lean_inc(x_124);
lean_dec(x_79);
x_125 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_126 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_124, x_2, x_5, x_4, x_74, x_75, x_76, x_125, x_7, x_8, x_9, x_10, x_11, x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_6 = x_129;
x_12 = x_128;
goto _start;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_5);
lean_dec(x_4);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_75);
lean_ctor_set(x_131, 1, x_76);
lean_ctor_set(x_6, 1, x_131);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_6);
lean_ctor_set(x_132, 1, x_12);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_6, 1);
x_134 = lean_ctor_get(x_6, 0);
lean_inc(x_133);
lean_inc(x_134);
lean_dec(x_6);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
x_138 = l_Array_isEmpty___rarg(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_137);
lean_inc(x_136);
x_139 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_136, x_7, x_8, x_9, x_10, x_11, x_12);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
if (x_1 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_162; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_array_get_size(x_136);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_lt(x_146, x_145);
x_148 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_3, x_144);
if (x_147 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_145, x_145);
if (x_173 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
size_t x_174; lean_object* x_175; 
x_174 = lean_usize_of_nat(x_145);
lean_dec(x_145);
lean_inc(x_4);
x_175 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_144, x_136, x_2, x_174, x_4);
x_162 = x_175;
goto block_172;
}
}
block_161:
{
lean_object* x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_150 = l_Array_eraseReps___at_Lean_computeStructureResolutionOrder___spec__8(x_149);
lean_dec(x_149);
x_151 = lean_array_size(x_150);
x_152 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_3, x_151, x_2, x_150);
lean_inc(x_144);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_148);
x_154 = lean_array_push(x_134, x_153);
x_155 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_156 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_144, x_2, x_5, x_4, x_154, x_135, x_136, x_155, x_7, x_8, x_9, x_10, x_11, x_143);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_6 = x_159;
x_12 = x_158;
goto _start;
}
block_172:
{
size_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_array_size(x_162);
x_164 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__11(x_163, x_2, x_162);
x_165 = lean_array_get_size(x_164);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_sub(x_165, x_166);
x_168 = lean_nat_dec_eq(x_165, x_146);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_146, x_167);
if (x_169 == 0)
{
lean_object* x_170; 
lean_inc(x_167);
x_170 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_165, x_164, x_167, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_170;
goto block_161;
}
else
{
lean_object* x_171; 
x_171 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_165, x_164, x_146, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_171;
goto block_161;
}
}
else
{
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_164;
goto block_161;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_139, 1);
lean_inc(x_176);
lean_dec(x_139);
x_177 = lean_ctor_get(x_140, 1);
lean_inc(x_177);
lean_dec(x_140);
x_178 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_179 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_177, x_2, x_5, x_4, x_134, x_135, x_136, x_178, x_7, x_8, x_9, x_10, x_11, x_176);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
x_6 = x_182;
x_12 = x_181;
goto _start;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_139, 1);
lean_inc(x_184);
lean_dec(x_139);
x_185 = lean_ctor_get(x_140, 1);
lean_inc(x_185);
lean_dec(x_140);
x_186 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_187 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_185, x_2, x_5, x_4, x_134, x_135, x_136, x_186, x_7, x_8, x_9, x_10, x_11, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec(x_188);
x_6 = x_190;
x_12 = x_189;
goto _start;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_137)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_137;
}
lean_ctor_set(x_192, 0, x_135);
lean_ctor_set(x_192, 1, x_136);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_134);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_12);
return x_194;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_14, 1);
x_19 = l_Array_isEmpty___rarg(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_free_object(x_14);
lean_free_object(x_6);
lean_inc(x_18);
x_20 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_18, x_7, x_8, x_9, x_10, x_11, x_12);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
if (x_1 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_43; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_array_get_size(x_18);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
x_29 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_3, x_25);
if (x_28 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_26, x_26);
if (x_54 == 0)
{
lean_dec(x_26);
lean_inc(x_4);
x_43 = x_4;
goto block_53;
}
else
{
size_t x_55; lean_object* x_56; 
x_55 = lean_usize_of_nat(x_26);
lean_dec(x_26);
lean_inc(x_4);
x_56 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_25, x_18, x_2, x_55, x_4);
x_43 = x_56;
goto block_53;
}
}
block_42:
{
lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = l_Array_eraseReps___at_Lean_computeStructureResolutionOrder___spec__8(x_30);
lean_dec(x_30);
x_32 = lean_array_size(x_31);
x_33 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_3, x_32, x_2, x_31);
lean_inc(x_25);
x_34 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_29);
x_35 = lean_array_push(x_16, x_34);
x_36 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_37 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_25, x_2, x_5, x_4, x_35, x_17, x_18, x_36, x_7, x_8, x_9, x_10, x_11, x_24);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_6 = x_40;
x_12 = x_39;
goto _start;
}
block_53:
{
size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_array_size(x_43);
x_45 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__11(x_44, x_2, x_43);
x_46 = lean_array_get_size(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_46, x_47);
x_49 = lean_nat_dec_eq(x_46, x_27);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_27, x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_inc(x_48);
x_51 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_46, x_45, x_48, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_51;
goto block_42;
}
else
{
lean_object* x_52; 
x_52 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_46, x_45, x_27, x_48, lean_box(0), lean_box(0));
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_52;
goto block_42;
}
}
else
{
lean_dec(x_48);
lean_dec(x_46);
x_30 = x_45;
goto block_42;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_dec(x_20);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_dec(x_21);
x_59 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_60 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_58, x_2, x_5, x_4, x_16, x_17, x_18, x_59, x_7, x_8, x_9, x_10, x_11, x_57);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_6 = x_63;
x_12 = x_62;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_dec(x_20);
x_66 = lean_ctor_get(x_21, 1);
lean_inc(x_66);
lean_dec(x_21);
x_67 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_68 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_66, x_2, x_5, x_4, x_16, x_17, x_18, x_67, x_7, x_8, x_9, x_10, x_11, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_6 = x_71;
x_12 = x_70;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_5);
lean_dec(x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_12);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_6, 0);
x_75 = lean_ctor_get(x_14, 0);
x_76 = lean_ctor_get(x_14, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_14);
x_77 = l_Array_isEmpty___rarg(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_free_object(x_6);
lean_inc(x_76);
x_78 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_76, x_7, x_8, x_9, x_10, x_11, x_12);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
if (x_1 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; lean_object* x_101; 
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
lean_dec(x_79);
x_84 = lean_array_get_size(x_76);
x_85 = lean_unsigned_to_nat(0u);
x_86 = lean_nat_dec_lt(x_85, x_84);
x_87 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_3, x_83);
if (x_86 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
uint8_t x_112; 
x_112 = lean_nat_dec_le(x_84, x_84);
if (x_112 == 0)
{
lean_dec(x_84);
lean_inc(x_4);
x_101 = x_4;
goto block_111;
}
else
{
size_t x_113; lean_object* x_114; 
x_113 = lean_usize_of_nat(x_84);
lean_dec(x_84);
lean_inc(x_4);
x_114 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_83, x_76, x_2, x_113, x_4);
x_101 = x_114;
goto block_111;
}
}
block_100:
{
lean_object* x_89; size_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_89 = l_Array_eraseReps___at_Lean_computeStructureResolutionOrder___spec__8(x_88);
lean_dec(x_88);
x_90 = lean_array_size(x_89);
x_91 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_3, x_90, x_2, x_89);
lean_inc(x_83);
x_92 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_uint8(x_92, sizeof(void*)*2, x_87);
x_93 = lean_array_push(x_74, x_92);
x_94 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_95 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_83, x_2, x_5, x_4, x_93, x_75, x_76, x_94, x_7, x_8, x_9, x_10, x_11, x_82);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_6 = x_98;
x_12 = x_97;
goto _start;
}
block_111:
{
size_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_102 = lean_array_size(x_101);
x_103 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__11(x_102, x_2, x_101);
x_104 = lean_array_get_size(x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_104, x_105);
x_107 = lean_nat_dec_eq(x_104, x_85);
if (x_107 == 0)
{
uint8_t x_108; 
x_108 = lean_nat_dec_le(x_85, x_106);
if (x_108 == 0)
{
lean_object* x_109; 
lean_inc(x_106);
x_109 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_104, x_103, x_106, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_109;
goto block_100;
}
else
{
lean_object* x_110; 
x_110 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_104, x_103, x_85, x_106, lean_box(0), lean_box(0));
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_110;
goto block_100;
}
}
else
{
lean_dec(x_106);
lean_dec(x_104);
x_88 = x_103;
goto block_100;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_78, 1);
lean_inc(x_115);
lean_dec(x_78);
x_116 = lean_ctor_get(x_79, 1);
lean_inc(x_116);
lean_dec(x_79);
x_117 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_118 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_116, x_2, x_5, x_4, x_74, x_75, x_76, x_117, x_7, x_8, x_9, x_10, x_11, x_115);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
lean_dec(x_119);
x_6 = x_121;
x_12 = x_120;
goto _start;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_78, 1);
lean_inc(x_123);
lean_dec(x_78);
x_124 = lean_ctor_get(x_79, 1);
lean_inc(x_124);
lean_dec(x_79);
x_125 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_126 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_124, x_2, x_5, x_4, x_74, x_75, x_76, x_125, x_7, x_8, x_9, x_10, x_11, x_123);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_6 = x_129;
x_12 = x_128;
goto _start;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_5);
lean_dec(x_4);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_75);
lean_ctor_set(x_131, 1, x_76);
lean_ctor_set(x_6, 1, x_131);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_6);
lean_ctor_set(x_132, 1, x_12);
return x_132;
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_6, 1);
x_134 = lean_ctor_get(x_6, 0);
lean_inc(x_133);
lean_inc(x_134);
lean_dec(x_6);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
x_138 = l_Array_isEmpty___rarg(x_136);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_137);
lean_inc(x_136);
x_139 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_136, x_7, x_8, x_9, x_10, x_11, x_12);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
if (x_1 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; lean_object* x_149; lean_object* x_162; 
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
lean_dec(x_139);
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
x_145 = lean_array_get_size(x_136);
x_146 = lean_unsigned_to_nat(0u);
x_147 = lean_nat_dec_lt(x_146, x_145);
x_148 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_3, x_144);
if (x_147 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_145, x_145);
if (x_173 == 0)
{
lean_dec(x_145);
lean_inc(x_4);
x_162 = x_4;
goto block_172;
}
else
{
size_t x_174; lean_object* x_175; 
x_174 = lean_usize_of_nat(x_145);
lean_dec(x_145);
lean_inc(x_4);
x_175 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_144, x_136, x_2, x_174, x_4);
x_162 = x_175;
goto block_172;
}
}
block_161:
{
lean_object* x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_150 = l_Array_eraseReps___at_Lean_computeStructureResolutionOrder___spec__8(x_149);
lean_dec(x_149);
x_151 = lean_array_size(x_150);
x_152 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_3, x_151, x_2, x_150);
lean_inc(x_144);
x_153 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*2, x_148);
x_154 = lean_array_push(x_134, x_153);
x_155 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_156 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_144, x_2, x_5, x_4, x_154, x_135, x_136, x_155, x_7, x_8, x_9, x_10, x_11, x_143);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_6 = x_159;
x_12 = x_158;
goto _start;
}
block_172:
{
size_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_163 = lean_array_size(x_162);
x_164 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__11(x_163, x_2, x_162);
x_165 = lean_array_get_size(x_164);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_sub(x_165, x_166);
x_168 = lean_nat_dec_eq(x_165, x_146);
if (x_168 == 0)
{
uint8_t x_169; 
x_169 = lean_nat_dec_le(x_146, x_167);
if (x_169 == 0)
{
lean_object* x_170; 
lean_inc(x_167);
x_170 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_165, x_164, x_167, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_170;
goto block_161;
}
else
{
lean_object* x_171; 
x_171 = l_Array_qsort_sort___at_Lean_computeStructureResolutionOrder___spec__12(x_165, x_164, x_146, x_167, lean_box(0), lean_box(0));
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_171;
goto block_161;
}
}
else
{
lean_dec(x_167);
lean_dec(x_165);
x_149 = x_164;
goto block_161;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_139, 1);
lean_inc(x_176);
lean_dec(x_139);
x_177 = lean_ctor_get(x_140, 1);
lean_inc(x_177);
lean_dec(x_140);
x_178 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_179 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_177, x_2, x_5, x_4, x_134, x_135, x_136, x_178, x_7, x_8, x_9, x_10, x_11, x_176);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
lean_dec(x_180);
x_6 = x_182;
x_12 = x_181;
goto _start;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_139, 1);
lean_inc(x_184);
lean_dec(x_139);
x_185 = lean_ctor_get(x_140, 1);
lean_inc(x_185);
lean_dec(x_140);
x_186 = lean_box(0);
lean_inc(x_4);
lean_inc(x_5);
x_187 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_185, x_2, x_5, x_4, x_134, x_135, x_136, x_186, x_7, x_8, x_9, x_10, x_11, x_184);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
lean_dec(x_188);
x_6 = x_190;
x_12 = x_189;
goto _start;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_5);
lean_dec(x_4);
if (lean_is_scalar(x_137)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_137;
}
lean_ctor_set(x_192, 0, x_135);
lean_ctor_set(x_192, 1, x_136);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_134);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_12);
return x_194;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; size_t x_15; lean_object* x_16; uint8_t x_17; 
lean_inc(x_2);
x_11 = l_Lean_getStructureParentInfo(x_1, x_2);
x_12 = lean_array_size(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_computeStructureResolutionOrder___spec__1(x_12, x_13, x_11);
x_15 = lean_array_size(x_14);
lean_inc(x_14);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_15, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_array_get_size(x_18);
lean_inc(x_14);
x_21 = lean_array_push(x_18, x_14);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_insertIdx_loop___rarg(x_22, x_21, x_20);
x_24 = lean_array_get_size(x_23);
x_25 = lean_box(0);
x_26 = lean_nat_dec_lt(x_22, x_24);
lean_inc(x_2);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_25);
lean_ctor_set(x_16, 0, x_2);
x_27 = lean_array_mk(x_16);
if (x_26 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_23);
x_28 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24(x_3, x_13, x_14, x_28, x_25, x_30, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_14);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_dec(x_38);
lean_inc(x_37);
x_39 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_37, x_5, x_6, x_7, x_8, x_9, x_34);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_33, 1, x_35);
lean_ctor_set(x_39, 0, x_33);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
lean_ctor_set(x_33, 1, x_35);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
lean_dec(x_33);
lean_inc(x_44);
x_45 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_44, x_5, x_6, x_7, x_8, x_9, x_34);
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
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_35);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_24, x_24);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_24);
lean_dec(x_23);
x_51 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26(x_3, x_13, x_14, x_51, x_25, x_53, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_14);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_56, 0);
x_61 = lean_ctor_get(x_56, 1);
lean_dec(x_61);
lean_inc(x_60);
x_62 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_60, x_5, x_6, x_7, x_8, x_9, x_57);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set(x_56, 1, x_58);
lean_ctor_set(x_62, 0, x_56);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
lean_ctor_set(x_56, 1, x_58);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_56);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_56, 0);
lean_inc(x_67);
lean_dec(x_56);
lean_inc(x_67);
x_68 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_67, x_5, x_6, x_7, x_8, x_9, x_57);
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
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_58);
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
else
{
size_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_73 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_74 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
x_75 = l_Array_foldlMUnsafe_fold___at_Lean_computeStructureResolutionOrder___spec__5(x_23, x_13, x_73, x_74);
lean_dec(x_23);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_27);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27(x_3, x_13, x_14, x_74, x_25, x_77, x_5, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_14);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec(x_79);
x_83 = !lean_is_exclusive(x_80);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_80, 0);
x_85 = lean_ctor_get(x_80, 1);
lean_dec(x_85);
lean_inc(x_84);
x_86 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_84, x_5, x_6, x_7, x_8, x_9, x_81);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set(x_80, 1, x_82);
lean_ctor_set(x_86, 0, x_80);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
lean_ctor_set(x_80, 1, x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_80, 0);
lean_inc(x_91);
lean_dec(x_80);
lean_inc(x_91);
x_92 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_91, x_5, x_6, x_7, x_8, x_9, x_81);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_94 = x_92;
} else {
 lean_dec_ref(x_92);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_82);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_97 = lean_ctor_get(x_16, 0);
x_98 = lean_ctor_get(x_16, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_16);
x_99 = lean_array_get_size(x_97);
lean_inc(x_14);
x_100 = lean_array_push(x_97, x_14);
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Array_insertIdx_loop___rarg(x_101, x_100, x_99);
x_103 = lean_array_get_size(x_102);
x_104 = lean_box(0);
x_105 = lean_nat_dec_lt(x_101, x_103);
lean_inc(x_2);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_2);
lean_ctor_set(x_106, 1, x_104);
x_107 = lean_array_mk(x_106);
if (x_105 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_103);
lean_dec(x_102);
x_108 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24(x_3, x_13, x_14, x_108, x_104, x_110, x_5, x_6, x_7, x_8, x_9, x_98);
lean_dec(x_14);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
lean_dec(x_112);
x_116 = lean_ctor_get(x_113, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_117 = x_113;
} else {
 lean_dec_ref(x_113);
 x_117 = lean_box(0);
}
lean_inc(x_116);
x_118 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_116, x_5, x_6, x_7, x_8, x_9, x_114);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_117;
}
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_115);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
else
{
uint8_t x_123; 
x_123 = lean_nat_dec_le(x_103, x_103);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_103);
lean_dec(x_102);
x_124 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_107);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26(x_3, x_13, x_14, x_124, x_104, x_126, x_5, x_6, x_7, x_8, x_9, x_98);
lean_dec(x_14);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
lean_dec(x_128);
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_133 = x_129;
} else {
 lean_dec_ref(x_129);
 x_133 = lean_box(0);
}
lean_inc(x_132);
x_134 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_132, x_5, x_6, x_7, x_8, x_9, x_130);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_133;
}
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_131);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
else
{
size_t x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_139 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_140 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
x_141 = l_Array_foldlMUnsafe_fold___at_Lean_computeStructureResolutionOrder___spec__5(x_102, x_13, x_139, x_140);
lean_dec(x_102);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_107);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27(x_3, x_13, x_14, x_140, x_104, x_143, x_5, x_6, x_7, x_8, x_9, x_98);
lean_dec(x_14);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_ctor_get(x_145, 0);
lean_inc(x_148);
lean_dec(x_145);
x_149 = lean_ctor_get(x_146, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_150 = x_146;
} else {
 lean_dec_ref(x_146);
 x_150 = lean_box(0);
}
lean_inc(x_149);
x_151 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_2, x_149, x_5, x_6, x_7, x_8, x_9, x_147);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_150;
}
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_148);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_153;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_152);
return x_155;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_9);
x_15 = lean_box(0);
x_16 = l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___lambda__1(x_13, x_1, x_2, x_15, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Structure_0__Lean_getStructureResolutionOrder_x3f(x_22, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___lambda__1(x_22, x_1, x_2, x_24, x_3, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_1);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_8 = 1;
x_9 = l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_8 = l_Lean_getStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Array_erase___at_Lean_getAllParentStructures___spec__1(x_10, x_1);
lean_dec(x_1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Array_erase___at_Lean_getAllParentStructures___spec__1(x_12, x_1);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
lean_dec(x_6);
x_15 = lean_array_uget(x_3, x_5);
x_16 = lean_st_ref_take(x_7, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_Lean_RBNode_insert___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(x_17, x_15, x_19);
x_21 = lean_st_ref_set(x_7, x_20, x_18);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_5, x_23);
x_5 = x_24;
x_6 = x_19;
x_12 = x_22;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_unfoldeDefinitionGuarded_x3f(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(x_18, x_3, x_4, x_5, x_6, x_7, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_take(x_2, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
lean_inc(x_9);
x_14 = l_Lean_RBNode_insert___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__1(x_11, x_9, x_13);
x_15 = lean_st_ref_set(x_2, x_14, x_12);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_9);
x_21 = l_Lean_isStructure(x_20, x_9);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_9);
x_22 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = l_Lean_getAllParentStructures___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3(x_9, x_2, x_3, x_4, x_5, x_6, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = lean_array_size(x_24);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__28(x_24, x_26, x_24, x_27, x_28, x_13, x_2, x_3, x_4, x_5, x_6, x_25);
lean_dec(x_24);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_7);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__6(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__8(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__9(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__10(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__11(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__12(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__13(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__14(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__15(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
lean_object* x_20; 
x_20 = l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
lean_object* x_18; 
x_18 = l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_computeStructureResolutionOrder_selectParent___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__18(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__19(x_7, x_2, x_3, x_8, x_9, x_6);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__20(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__21(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__22(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__23(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___lambda__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__24(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__26(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__27(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___lambda__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_computeStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__5(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getAllParentStructures___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getAllParentStructures___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__28(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_box(0);
x_8 = lean_st_mk_ref(x_7, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit(x_1, x_9, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_9, x_12);
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_5);
x_13 = lean_apply_2(x_1, x_5, x_3);
if (lean_obj_tag(x_13) == 0)
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_1);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_apply_10(x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_visitNamespaces(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_2 = x_11;
x_3 = x_15;
x_10 = x_14;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_14, 0);
lean_dec(x_27);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_15);
lean_ctor_set(x_14, 0, x_30);
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_15, 0, x_33);
x_34 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_15);
lean_ctor_set(x_14, 0, x_35);
return x_14;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_40 = x_36;
} else {
 lean_dec_ref(x_36);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_15, 0, x_41);
x_42 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_15);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_15, 0);
lean_free_object(x_15);
x_46 = !lean_is_exclusive(x_6);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_14);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_14, 0);
lean_dec(x_49);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_45, 1);
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_ctor_get(x_48, 1);
x_56 = l_Lean_Name_isSuffixOf(x_52, x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
x_57 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
lean_ctor_set(x_45, 1, x_6);
lean_ctor_set(x_45, 0, x_57);
lean_ctor_set(x_14, 0, x_45);
return x_14;
}
else
{
lean_object* x_58; 
lean_dec(x_55);
lean_dec(x_54);
lean_ctor_set(x_48, 1, x_53);
lean_ctor_set(x_48, 0, x_52);
x_58 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
lean_ctor_set(x_45, 1, x_6);
lean_ctor_set(x_45, 0, x_58);
lean_ctor_set(x_14, 0, x_45);
return x_14;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_63 = l_Lean_Name_isSuffixOf(x_59, x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_60);
lean_dec(x_59);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_6, 0, x_64);
x_65 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
lean_ctor_set(x_45, 1, x_6);
lean_ctor_set(x_45, 0, x_65);
lean_ctor_set(x_14, 0, x_45);
return x_14;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
lean_dec(x_61);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set(x_6, 0, x_66);
x_67 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
lean_ctor_set(x_45, 1, x_6);
lean_ctor_set(x_45, 0, x_67);
lean_ctor_set(x_14, 0, x_45);
return x_14;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_ctor_get(x_45, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_45);
x_70 = lean_ctor_get(x_48, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_48, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_72 = x_48;
} else {
 lean_dec_ref(x_48);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Name_isSuffixOf(x_68, x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_69);
lean_dec(x_68);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_6, 0, x_74);
x_75 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_6);
lean_ctor_set(x_14, 0, x_76);
return x_14;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_71);
lean_dec(x_70);
if (lean_is_scalar(x_72)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_72;
}
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_69);
lean_ctor_set(x_6, 0, x_77);
x_78 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_6);
lean_ctor_set(x_14, 0, x_79);
return x_14;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_80 = lean_ctor_get(x_6, 0);
x_81 = lean_ctor_get(x_14, 1);
lean_inc(x_81);
lean_dec(x_14);
x_82 = lean_ctor_get(x_45, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_45, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_84 = x_45;
} else {
 lean_dec_ref(x_45);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_80, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_87 = x_80;
} else {
 lean_dec_ref(x_80);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Name_isSuffixOf(x_82, x_85);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_83);
lean_dec(x_82);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_85);
lean_ctor_set(x_89, 1, x_86);
lean_ctor_set(x_6, 0, x_89);
x_90 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
if (lean_is_scalar(x_84)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_84;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_6);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_81);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_86);
lean_dec(x_85);
if (lean_is_scalar(x_87)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_87;
}
lean_ctor_set(x_93, 0, x_82);
lean_ctor_set(x_93, 1, x_83);
lean_ctor_set(x_6, 0, x_93);
x_94 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
if (lean_is_scalar(x_84)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_84;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_81);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_97 = lean_ctor_get(x_6, 0);
lean_inc(x_97);
lean_dec(x_6);
x_98 = lean_ctor_get(x_14, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_99 = x_14;
} else {
 lean_dec_ref(x_14);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_45, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_45, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_102 = x_45;
} else {
 lean_dec_ref(x_45);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_97, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_105 = x_97;
} else {
 lean_dec_ref(x_97);
 x_105 = lean_box(0);
}
x_106 = l_Lean_Name_isSuffixOf(x_100, x_103);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_101);
lean_dec(x_100);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_105;
}
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_104);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
if (lean_is_scalar(x_102)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_102;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
if (lean_is_scalar(x_99)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_99;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_98);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_104);
lean_dec(x_103);
if (lean_is_scalar(x_105)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_105;
}
lean_ctor_set(x_112, 0, x_100);
lean_ctor_set(x_112, 1, x_101);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
if (lean_is_scalar(x_102)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_102;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
if (lean_is_scalar(x_99)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_99;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_98);
return x_116;
}
}
}
}
else
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_15, 0);
lean_inc(x_117);
lean_dec(x_15);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_118 = lean_ctor_get(x_14, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_119 = x_14;
} else {
 lean_dec_ref(x_14);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_122 = x_117;
} else {
 lean_dec_ref(x_117);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
if (lean_is_scalar(x_119)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_119;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_118);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_128 = lean_ctor_get(x_6, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 x_129 = x_6;
} else {
 lean_dec_ref(x_6);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_14, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_131 = x_14;
} else {
 lean_dec_ref(x_14);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_117, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_117, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_134 = x_117;
} else {
 lean_dec_ref(x_117);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_128, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_128, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_137 = x_128;
} else {
 lean_dec_ref(x_128);
 x_137 = lean_box(0);
}
x_138 = l_Lean_Name_isSuffixOf(x_132, x_135);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_133);
lean_dec(x_132);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_135);
lean_ctor_set(x_139, 1, x_136);
if (lean_is_scalar(x_129)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_129;
}
lean_ctor_set(x_140, 0, x_139);
x_141 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
if (lean_is_scalar(x_134)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_134;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
if (lean_is_scalar(x_131)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_131;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_130);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_136);
lean_dec(x_135);
if (lean_is_scalar(x_137)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_137;
}
lean_ctor_set(x_144, 0, x_132);
lean_ctor_set(x_144, 1, x_133);
if (lean_is_scalar(x_129)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_129;
}
lean_ctor_set(x_145, 0, x_144);
x_146 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
if (lean_is_scalar(x_134)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_134;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
if (lean_is_scalar(x_131)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_131;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_130);
return x_148;
}
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_6);
x_149 = !lean_is_exclusive(x_14);
if (x_149 == 0)
{
return x_14;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_14, 0);
x_151 = lean_ctor_get(x_14, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_14);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_8);
x_20 = lean_ctor_get(x_7, 0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_3, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1(x_22, x_2, x_1, x_3, x_25, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_27, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_33);
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_26, 1);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_39 = x_27;
} else {
 lean_dec_ref(x_27);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
lean_dec(x_28);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_dec(x_27);
x_45 = lean_ctor_get(x_28, 0);
lean_inc(x_45);
lean_dec(x_28);
x_7 = x_21;
x_8 = x_45;
x_9 = lean_box(0);
x_10 = x_44;
x_17 = x_43;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; 
x_51 = lean_box(0);
x_7 = x_21;
x_8 = x_51;
x_9 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_7, 1);
x_54 = lean_box(0);
x_7 = x_53;
x_8 = x_54;
x_9 = lean_box(0);
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = lean_apply_9(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_2 = x_16;
x_3 = x_14;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed), 11, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_box(0);
x_12 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_10, x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
x_15 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__3(x_1, x_15, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
lean_inc(x_3);
x_12 = l_Lean_Meta_allowCompletion(x_1, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_apply_9(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_forEligibleDeclsM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_12);
x_13 = l_Lean_Server_Completion_getEligibleHeaderDecls(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_dec(x_16);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Server_Completion_forEligibleDeclsM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__2___lambda__1), 11, 2);
lean_closure_set(x_22, 0, x_12);
lean_closure_set(x_22, 1, x_1);
x_23 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__4(x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_21);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_17, x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_16);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Server_Completion_forEligibleDeclsM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__2___lambda__1), 11, 2);
lean_closure_set(x_27, 0, x_12);
lean_closure_set(x_27, 1, x_1);
x_28 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__4(x_26, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_26);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_31 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__6(x_1, x_16, x_29, x_30, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_alloc_closure((void*)(l_Lean_Server_Completion_forEligibleDeclsM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__2___lambda__1), 11, 2);
lean_closure_set(x_36, 0, x_12);
lean_closure_set(x_36, 1, x_1);
x_37 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__4(x_35, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_33);
lean_dec(x_35);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, double x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_15);
lean_inc(x_1);
x_17 = l_Lean_Server_Completion_allowCompletion(x_2, x_1, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Name_getString_x21(x_3);
x_20 = lean_box(0);
x_21 = l_Lean_Name_str___override(x_20, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(x_21, x_15, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_5 = x_16;
x_12 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, double x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_15);
lean_inc(x_1);
x_17 = l_Lean_Server_Completion_allowCompletion(x_2, x_1, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_Name_getString_x21(x_3);
x_20 = lean_box(0);
x_21 = l_Lean_Name_str___override(x_20, x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_22 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(x_21, x_15, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_5 = x_16;
x_12 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = lean_apply_9(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_2 = x_16;
x_3 = x_14;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = lean_apply_10(x_1, x_5, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_18;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
case 1:
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_28 = l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg(x_1, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; size_t x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_5 = x_29;
x_12 = x_30;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
default: 
{
size_t x_38; size_t x_39; 
x_38 = 1;
x_39 = lean_usize_add(x_3, x_38);
x_3 = x_39;
goto _start;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_12);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg___boxed), 12, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_2);
x_15 = lean_nat_dec_lt(x_5, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_fget(x_2, x_5);
x_18 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = lean_apply_10(x_1, x_6, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_23;
x_6 = x_20;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg___boxed), 13, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_12, x_12);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_20 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg(x_1, x_11, x_18, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg(x_1, x_21, x_22, lean_box(0), x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg___boxed), 10, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed), 11, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_box(0);
x_12 = l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg(x_10, x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__16(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
x_15 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__10(x_1, x_15, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_10, 1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 1);
x_16 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__11(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_18 = lean_ctor_get(x_1, 1);
x_19 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__11(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__16(x_2, x_11, x_20, x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_1, 1);
x_26 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__11(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = l_Lean_Name_isPrefixOf(x_1, x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_box(0);
lean_inc(x_6);
x_19 = l_Lean_Name_replacePrefix(x_6, x_1, x_18);
x_20 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(x_2, x_19, x_3);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
else
{
lean_object* x_23; double x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_unbox_float(x_23);
lean_dec(x_23);
x_25 = l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__8(x_4, x_5, x_6, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_18; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_9);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_getAliasState(x_3);
x_23 = lean_box(x_1);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17___lambda__1___boxed), 14, 5);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_4);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_25 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__9(x_22, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_8 = x_20;
x_9 = x_27;
x_10 = lean_box(0);
x_17 = x_26;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_dec(x_8);
x_34 = lean_ctor_get(x_19, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_dec(x_19);
lean_inc(x_35);
lean_inc(x_3);
x_36 = l_Lean_Server_Completion_allowCompletion(x_4, x_3, x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_35);
lean_dec(x_34);
x_37 = lean_box(0);
x_8 = x_33;
x_9 = x_37;
x_10 = lean_box(0);
goto _start;
}
else
{
lean_object* x_39; 
lean_inc(x_2);
x_39 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(x_2, x_34, x_1);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_34);
x_40 = lean_box(0);
x_8 = x_33;
x_9 = x_40;
x_10 = lean_box(0);
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; double x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l_Lean_Name_getString_x21(x_34);
lean_dec(x_34);
x_44 = lean_box(0);
x_45 = l_Lean_Name_str___override(x_44, x_43);
x_46 = lean_unbox_float(x_42);
lean_dec(x_42);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_47 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItemForDecl(x_45, x_35, x_46, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_8 = x_33;
x_9 = x_49;
x_10 = lean_box(0);
x_17 = x_48;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_33);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_47, 0);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
lean_dec(x_3);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = lean_apply_9(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_2 = x_16;
x_3 = x_14;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forM___at_Lean_Server_Completion_completeNamespaces___spec__4___lambda__1___boxed), 11, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_box(0);
x_12 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_Server_Completion_completeNamespaces___spec__6___rarg(x_10, x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__22(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
x_15 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Std_DHashMap_Internal_AssocList_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__19(x_1, x_15, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_17;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_12);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_10, 1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_1, 1);
x_16 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__20(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_12, x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_18 = lean_ctor_get(x_1, 1);
x_19 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__20(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_22 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__22(x_2, x_11, x_20, x_21, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_1, 1);
x_26 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__20(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; double x_18; lean_object* x_19; 
lean_dec(x_7);
x_17 = lean_array_uget(x_4, x_6);
x_18 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2;
lean_inc(x_1);
x_19 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_1, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
size_t x_20; size_t x_21; lean_object* x_22; 
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_6, x_20);
x_22 = lean_box(0);
x_6 = x_21;
x_7 = x_22;
goto _start;
}
else
{
lean_object* x_24; double x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_unbox_float(x_24);
lean_dec(x_24);
x_26 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem(x_17, x_25, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = 1;
x_29 = lean_usize_add(x_6, x_28);
x_30 = lean_box(0);
x_6 = x_29;
x_7 = x_30;
x_14 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__26(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_9, x_8);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_uget(x_7, x_9);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_10, 1);
x_23 = lean_ctor_get(x_10, 0);
lean_dec(x_23);
lean_inc(x_22);
lean_inc(x_2);
x_24 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25(x_1, x_2, x_3, x_20, x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_10, 0, x_28);
lean_ctor_set(x_24, 0, x_10);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_10, 0, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_22);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
lean_inc(x_6);
lean_ctor_set(x_10, 1, x_33);
lean_ctor_set(x_10, 0, x_6);
x_34 = 1;
x_35 = lean_usize_add(x_9, x_34);
x_9 = x_35;
x_17 = x_32;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_dec(x_10);
lean_inc(x_37);
lean_inc(x_2);
x_38 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25(x_1, x_2, x_3, x_20, x_37, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_20);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_6);
lean_dec(x_2);
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
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; 
lean_dec(x_37);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
lean_dec(x_39);
lean_inc(x_6);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = lean_usize_add(x_9, x_48);
x_9 = x_49;
x_10 = x_47;
x_17 = x_45;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__27(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_8, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_uget(x_6, x_8);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_21 = x_9;
} else {
 lean_dec_ref(x_9);
 x_21 = lean_box(0);
}
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_20);
x_22 = x_30;
x_23 = x_16;
goto block_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
x_32 = l_Lean_LocalDecl_userName(x_31);
lean_inc(x_2);
x_33 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(x_2, x_32, x_1);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_31);
x_34 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_22 = x_34;
x_23 = x_16;
goto block_29;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
lean_ctor_set(x_33, 0, x_37);
x_38 = 5;
x_39 = lean_unbox_float(x_36);
lean_dec(x_36);
x_40 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_32, x_33, x_38, x_39, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_22 = x_42;
x_23 = x_41;
goto block_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; double x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
lean_dec(x_33);
x_44 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = 5;
x_47 = lean_unbox_float(x_43);
lean_dec(x_43);
x_48 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_32, x_45, x_46, x_47, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_22 = x_50;
x_23 = x_49;
goto block_29;
}
}
}
block_29:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_5);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_8, x_26);
x_8 = x_27;
x_9 = x_25;
x_16 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_array_size(x_13);
x_18 = 0;
x_19 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__26(x_1, x_2, x_3, x_13, x_14, x_15, x_13, x_17, x_18, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
x_25 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1(x_23, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
x_36 = lean_array_size(x_32);
x_37 = 0;
x_38 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__27(x_1, x_2, x_32, x_33, x_34, x_32, x_36, x_37, x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_box(0);
x_44 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1(x_42, x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_39);
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_47);
return x_38;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_dec(x_38);
x_49 = lean_ctor_get(x_40, 0);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__28(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = lean_usize_dec_lt(x_8, x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_uget(x_6, x_8);
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_21 = x_9;
} else {
 lean_dec_ref(x_9);
 x_21 = lean_box(0);
}
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_20);
x_22 = x_30;
x_23 = x_16;
goto block_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
x_32 = l_Lean_LocalDecl_userName(x_31);
lean_inc(x_2);
x_33 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(x_2, x_32, x_1);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_32);
lean_dec(x_31);
x_34 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_22 = x_34;
x_23 = x_16;
goto block_29;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
lean_ctor_set(x_33, 0, x_37);
x_38 = 5;
x_39 = lean_unbox_float(x_36);
lean_dec(x_36);
x_40 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_32, x_33, x_38, x_39, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_22 = x_42;
x_23 = x_41;
goto block_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; double x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
lean_dec(x_33);
x_44 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = 5;
x_47 = lean_unbox_float(x_43);
lean_dec(x_43);
x_48 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_32, x_45, x_46, x_47, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1;
x_22 = x_50;
x_23 = x_49;
goto block_29;
}
}
}
block_29:
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_5);
if (lean_is_scalar(x_21)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_21;
}
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_8, x_26);
x_8 = x_27;
x_9 = x_25;
x_16 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
x_13 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25(x_1, x_2, x_4, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_box(0);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_array_size(x_23);
x_28 = 0;
x_29 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__28(x_1, x_2, x_23, x_24, x_25, x_23, x_27, x_28, x_26, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
lean_ctor_set(x_29, 0, x_34);
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_30);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_29, 0);
lean_dec(x_39);
x_40 = lean_ctor_get(x_31, 0);
lean_inc(x_40);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_40);
return x_29;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_29, 1);
lean_inc(x_41);
lean_dec(x_29);
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(x_4, x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_13, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_14);
lean_ctor_set(x_13, 0, x_29);
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_14, 0, x_32);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_14);
lean_ctor_set(x_13, 0, x_34);
return x_13;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_dec(x_13);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_39 = x_35;
} else {
 lean_dec_ref(x_35);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_14, 0, x_40);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_14);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_14, 0);
lean_free_object(x_14);
x_45 = !lean_is_exclusive(x_5);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_5, 0);
x_48 = lean_ctor_get(x_13, 0);
lean_dec(x_48);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_44, 0);
x_52 = lean_ctor_get(x_44, 1);
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_ctor_get(x_47, 1);
x_55 = l_Lean_Name_isSuffixOf(x_51, x_53);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_51);
x_56 = lean_box(0);
lean_ctor_set(x_44, 1, x_5);
lean_ctor_set(x_44, 0, x_56);
lean_ctor_set(x_13, 0, x_44);
return x_13;
}
else
{
lean_object* x_57; 
lean_dec(x_54);
lean_dec(x_53);
lean_ctor_set(x_47, 1, x_52);
lean_ctor_set(x_47, 0, x_51);
x_57 = lean_box(0);
lean_ctor_set(x_44, 1, x_5);
lean_ctor_set(x_44, 0, x_57);
lean_ctor_set(x_13, 0, x_44);
return x_13;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_ctor_get(x_44, 1);
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_47, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_47);
x_62 = l_Lean_Name_isSuffixOf(x_58, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_58);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_5, 0, x_63);
x_64 = lean_box(0);
lean_ctor_set(x_44, 1, x_5);
lean_ctor_set(x_44, 0, x_64);
lean_ctor_set(x_13, 0, x_44);
return x_13;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_60);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_59);
lean_ctor_set(x_5, 0, x_65);
x_66 = lean_box(0);
lean_ctor_set(x_44, 1, x_5);
lean_ctor_set(x_44, 0, x_66);
lean_ctor_set(x_13, 0, x_44);
return x_13;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_44, 0);
x_68 = lean_ctor_get(x_44, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_44);
x_69 = lean_ctor_get(x_47, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_47, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_71 = x_47;
} else {
 lean_dec_ref(x_47);
 x_71 = lean_box(0);
}
x_72 = l_Lean_Name_isSuffixOf(x_67, x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_68);
lean_dec(x_67);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_5, 0, x_73);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_5);
lean_ctor_set(x_13, 0, x_75);
return x_13;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_70);
lean_dec(x_69);
if (lean_is_scalar(x_71)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_71;
}
lean_ctor_set(x_76, 0, x_67);
lean_ctor_set(x_76, 1, x_68);
lean_ctor_set(x_5, 0, x_76);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_5);
lean_ctor_set(x_13, 0, x_78);
return x_13;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_79 = lean_ctor_get(x_5, 0);
x_80 = lean_ctor_get(x_13, 1);
lean_inc(x_80);
lean_dec(x_13);
x_81 = lean_ctor_get(x_44, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_44, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_83 = x_44;
} else {
 lean_dec_ref(x_44);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_86 = x_79;
} else {
 lean_dec_ref(x_79);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Name_isSuffixOf(x_81, x_84);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_82);
lean_dec(x_81);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_85);
lean_ctor_set(x_5, 0, x_88);
x_89 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_83;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_5);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_80);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_85);
lean_dec(x_84);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_86;
}
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set(x_92, 1, x_82);
lean_ctor_set(x_5, 0, x_92);
x_93 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_83;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_5);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_80);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_96 = lean_ctor_get(x_5, 0);
lean_inc(x_96);
lean_dec(x_5);
x_97 = lean_ctor_get(x_13, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_98 = x_13;
} else {
 lean_dec_ref(x_13);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_44, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_44, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_101 = x_44;
} else {
 lean_dec_ref(x_44);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get(x_96, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_104 = x_96;
} else {
 lean_dec_ref(x_96);
 x_104 = lean_box(0);
}
x_105 = l_Lean_Name_isSuffixOf(x_99, x_102);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_100);
lean_dec(x_99);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_103);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_101;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
if (lean_is_scalar(x_98)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_98;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_97);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_103);
lean_dec(x_102);
if (lean_is_scalar(x_104)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_104;
}
lean_ctor_set(x_111, 0, x_99);
lean_ctor_set(x_111, 1, x_100);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_101;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
if (lean_is_scalar(x_98)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_98;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_97);
return x_115;
}
}
}
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_14, 0);
lean_inc(x_116);
lean_dec(x_14);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_117 = lean_ctor_get(x_13, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_118 = x_13;
} else {
 lean_dec_ref(x_13);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_121 = x_116;
} else {
 lean_dec_ref(x_116);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
if (lean_is_scalar(x_118)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_118;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_117);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_127 = lean_ctor_get(x_5, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_128 = x_5;
} else {
 lean_dec_ref(x_5);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_13, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_130 = x_13;
} else {
 lean_dec_ref(x_13);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_116, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_116, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_133 = x_116;
} else {
 lean_dec_ref(x_116);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_127, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_127, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_136 = x_127;
} else {
 lean_dec_ref(x_127);
 x_136 = lean_box(0);
}
x_137 = l_Lean_Name_isSuffixOf(x_131, x_134);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_132);
lean_dec(x_131);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_135);
if (lean_is_scalar(x_128)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_128;
}
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_box(0);
if (lean_is_scalar(x_133)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_133;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
if (lean_is_scalar(x_130)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_130;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_129);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_135);
lean_dec(x_134);
if (lean_is_scalar(x_136)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_136;
}
lean_ctor_set(x_143, 0, x_131);
lean_ctor_set(x_143, 1, x_132);
if (lean_is_scalar(x_128)) {
 x_144 = lean_alloc_ctor(1, 1, 0);
} else {
 x_144 = x_128;
}
lean_ctor_set(x_144, 0, x_143);
x_145 = lean_box(0);
if (lean_is_scalar(x_133)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_133;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
if (lean_is_scalar(x_130)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_130;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_129);
return x_147;
}
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_5);
x_148 = !lean_is_exclusive(x_13);
if (x_148 == 0)
{
return x_13;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_13, 0);
x_150 = lean_ctor_get(x_13, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_13);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_51; 
x_13 = lean_box(x_2);
lean_inc(x_4);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__1___boxed), 12, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_4);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
x_17 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_51 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_visitNamespaces(x_14, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_15, 5);
lean_inc(x_55);
lean_dec(x_15);
x_56 = lean_box(0);
x_57 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_1);
x_58 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1(x_2, x_1, x_4, x_55, x_56, x_55, x_55, x_57, lean_box(0), x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
lean_dec(x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
x_63 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(x_62, x_1, x_2, x_4, x_8, x_9, x_10, x_11, x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_18 = x_61;
x_19 = x_65;
goto block_50;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_64, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_dec(x_63);
x_69 = !lean_is_exclusive(x_67);
if (x_69 == 0)
{
x_18 = x_64;
x_19 = x_68;
goto block_50;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 0);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_67);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_64, 0, x_72);
x_18 = x_64;
x_19 = x_68;
goto block_50;
}
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_64, 0);
lean_free_object(x_64);
x_74 = !lean_is_exclusive(x_61);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_75 = lean_ctor_get(x_61, 0);
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
lean_dec(x_63);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_dec(x_73);
x_79 = !lean_is_exclusive(x_75);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_80 = lean_ctor_get(x_75, 0);
x_81 = lean_ctor_get(x_75, 1);
x_82 = l_Lean_Name_isSuffixOf(x_77, x_80);
if (x_82 == 0)
{
lean_dec(x_78);
lean_dec(x_77);
x_18 = x_61;
x_19 = x_76;
goto block_50;
}
else
{
lean_dec(x_81);
lean_dec(x_80);
lean_ctor_set(x_75, 1, x_78);
lean_ctor_set(x_75, 0, x_77);
x_18 = x_61;
x_19 = x_76;
goto block_50;
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_75, 0);
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_75);
x_85 = l_Lean_Name_isSuffixOf(x_77, x_83);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_78);
lean_dec(x_77);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_61, 0, x_86);
x_18 = x_61;
x_19 = x_76;
goto block_50;
}
else
{
lean_object* x_87; 
lean_dec(x_84);
lean_dec(x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_78);
lean_ctor_set(x_61, 0, x_87);
x_18 = x_61;
x_19 = x_76;
goto block_50;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_88 = lean_ctor_get(x_61, 0);
lean_inc(x_88);
lean_dec(x_61);
x_89 = lean_ctor_get(x_63, 1);
lean_inc(x_89);
lean_dec(x_63);
x_90 = lean_ctor_get(x_73, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
lean_dec(x_73);
x_92 = lean_ctor_get(x_88, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_94 = x_88;
} else {
 lean_dec_ref(x_88);
 x_94 = lean_box(0);
}
x_95 = l_Lean_Name_isSuffixOf(x_90, x_92);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_91);
lean_dec(x_90);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_92);
lean_ctor_set(x_96, 1, x_93);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_18 = x_97;
x_19 = x_89;
goto block_50;
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_93);
lean_dec(x_92);
if (lean_is_scalar(x_94)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_94;
}
lean_ctor_set(x_98, 0, x_90);
lean_ctor_set(x_98, 1, x_91);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_18 = x_99;
x_19 = x_89;
goto block_50;
}
}
}
}
else
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_64, 0);
lean_inc(x_100);
lean_dec(x_64);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_63, 1);
lean_inc(x_101);
lean_dec(x_63);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_18 = x_106;
x_19 = x_101;
goto block_50;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_107 = lean_ctor_get(x_61, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_108 = x_61;
} else {
 lean_dec_ref(x_61);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_63, 1);
lean_inc(x_109);
lean_dec(x_63);
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_dec(x_100);
x_112 = lean_ctor_get(x_107, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
x_115 = l_Lean_Name_isSuffixOf(x_110, x_112);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_111);
lean_dec(x_110);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_113);
if (lean_is_scalar(x_108)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_108;
}
lean_ctor_set(x_117, 0, x_116);
x_18 = x_117;
x_19 = x_109;
goto block_50;
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_113);
lean_dec(x_112);
if (lean_is_scalar(x_114)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_114;
}
lean_ctor_set(x_118, 0, x_110);
lean_ctor_set(x_118, 1, x_111);
if (lean_is_scalar(x_108)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_108;
}
lean_ctor_set(x_119, 0, x_118);
x_18 = x_119;
x_19 = x_109;
goto block_50;
}
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_61);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_120 = !lean_is_exclusive(x_63);
if (x_120 == 0)
{
return x_63;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_63, 0);
x_122 = lean_ctor_get(x_63, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_63);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_58);
if (x_124 == 0)
{
return x_58;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_58, 0);
x_126 = lean_ctor_get(x_58, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_58);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_51);
if (x_128 == 0)
{
return x_51;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_51, 0);
x_130 = lean_ctor_get(x_51, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_51);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
block_50:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; double x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_4);
x_29 = lean_unbox(x_27);
lean_dec(x_27);
x_30 = lean_unbox_float(x_25);
lean_dec(x_25);
x_31 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_24, x_18, x_29, x_30, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_18, 0);
lean_inc(x_36);
lean_dec(x_18);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_39 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; double x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_4);
x_43 = lean_unbox(x_40);
lean_dec(x_40);
x_44 = lean_unbox_float(x_38);
lean_dec(x_38);
x_45 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_37, x_42, x_43, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_48 = x_39;
} else {
 lean_dec_ref(x_39);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Name_isPrefixOf(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = l_Lean_Name_replacePrefix(x_4, x_3, x_7);
x_9 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchAtomic(x_1, x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, double x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__7(x_1, x_2, x_3, x_5, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore_searchAlias(x_2, x_3, x_4, x_5, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Server_Completion_completeNamespaces(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_st_ref_get(x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__2___boxed), 12, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_Lean_Server_Completion_forEligibleDeclsM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__2(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(x_2);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__3___boxed), 4, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_20);
lean_inc(x_15);
x_22 = l_Lean_Server_Completion_getEligibleHeaderDecls(x_15, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_23);
lean_inc(x_15);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__4___boxed), 12, 2);
lean_closure_set(x_25, 0, x_15);
lean_closure_set(x_25, 1, x_23);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 5);
lean_inc(x_27);
x_28 = lean_box(0);
x_29 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_27);
lean_inc(x_15);
lean_inc(x_1);
x_30 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17(x_2, x_1, x_15, x_23, x_27, x_28, x_27, x_27, x_29, lean_box(0), x_5, x_6, x_7, x_8, x_9, x_10, x_24);
lean_dec(x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_getAliasState(x_15);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__5), 12, 3);
lean_closure_set(x_33, 0, x_26);
lean_closure_set(x_33, 1, x_21);
lean_closure_set(x_33, 2, x_25);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__18(x_32, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
if (x_2 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = l_Lean_Parser_getTokenTable(x_15);
lean_dec(x_15);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Data_Trie_findPrefix_go___rarg(x_37, x_38, x_39);
x_41 = lean_array_size(x_40);
x_42 = 0;
x_43 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__23(x_37, x_40, x_28, x_40, x_41, x_42, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_36);
lean_dec(x_40);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Server_Completion_completeNamespaces(x_3, x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_35);
lean_dec(x_15);
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_dec(x_34);
x_47 = l_Lean_Server_Completion_completeNamespaces(x_3, x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_15);
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
lean_dec(x_34);
x_49 = l_Lean_Server_Completion_completeNamespaces(x_3, x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_15);
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_dec(x_34);
x_51 = l_Lean_Server_Completion_completeNamespaces(x_3, x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_34);
if (x_52 == 0)
{
return x_34;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_34, 0);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_34);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_30);
if (x_56 == 0)
{
return x_30;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_30, 0);
x_58 = lean_ctor_get(x_30, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_30);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_18);
if (x_60 == 0)
{
return x_18;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_18, 0);
x_62 = lean_ctor_get(x_18, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_18);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Name_isAtomic(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__7(x_3, x_2, x_1, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
lean_inc(x_3);
x_18 = l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24(x_2, x_3, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__7(x_3, x_2, x_1, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__9(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__8(x_1, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate(x_4, x_15);
x_17 = 0;
x_18 = lean_box(0);
x_19 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__8(x_1, x_17, x_16, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = l_Lean_Name_hasMacroScopes(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__9(x_1, x_4, x_5, x_3, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Syntax_getHeadInfo(x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_17 = lean_erase_macro_scopes(x_3);
x_18 = lean_box(0);
x_19 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__9(x_1, x_4, x_5, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_1);
lean_dec(x_1);
x_19 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__6(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
double x_13; lean_object* x_14; 
x_13 = lean_unbox_float(x_4);
lean_dec(x_4);
x_14 = l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__7(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
double x_13; lean_object* x_14; 
x_13 = lean_unbox_float(x_4);
lean_dec(x_4);
x_14 = l_List_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__8(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__14___rarg(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_PersistentHashMap_foldlMAux_traverse___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__15___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_foldlMAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__13___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__16(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17___lambda__1(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_1);
lean_dec(x_1);
x_19 = l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__17(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentHashMap_foldlM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__21(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentHashMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__20(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__22(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_SMap_forM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__23(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__26___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_1);
lean_dec(x_1);
x_19 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_20 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_21 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__26(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_20 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__27(x_17, x_2, x_3, x_4, x_5, x_6, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_PersistentArray_forInAux___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__25(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_20 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__28(x_17, x_2, x_3, x_4, x_5, x_6, x_18, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_PersistentArray_forIn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__24(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__3(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
double x_13; lean_object* x_14; 
x_13 = lean_unbox_float(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__4(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__6(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__7(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__8(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___lambda__9(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(x_8);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___boxed), 12, 5);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_7);
lean_closure_set(x_11, 4, x_10);
x_12 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(x_1, x_2, x_3, x_4, x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_idCompletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = l_Lean_Server_Completion_idCompletion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_findCore___at_Lean_Server_Completion_dotCompletion___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_2);
x_8 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_cmpModPrivate(x_2, x_5);
switch (x_8) {
case 0:
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
default: 
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Server_Completion_dotCompletion___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Expr_hasMVar(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_st_ref_get(x_5, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_instantiateMVarsCore(x_14, x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_5, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_17);
x_23 = lean_st_ref_set(x_5, x_19, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_16);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_19, 1);
x_29 = lean_ctor_get(x_19, 2);
x_30 = lean_ctor_get(x_19, 3);
x_31 = lean_ctor_get(x_19, 4);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_17);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set(x_32, 4, x_31);
x_33 = lean_st_ref_set(x_5, x_32, x_20);
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
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Server_Completion_dotCompletion___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_8(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Server_Completion_dotCompletion___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Server_Completion_dotCompletion___spec__3___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; double x_18; uint8_t x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_ConstantInfo_name(x_1);
x_14 = l_Lean_Name_getString_x21(x_13);
x_15 = lean_box(0);
x_16 = l_Lean_Name_str___override(x_15, x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_13);
x_18 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3;
x_19 = lean_unbox(x_11);
lean_dec(x_11);
x_20 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_16, x_17, x_19, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_Lean_Name_getPrefix(x_20);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod(x_21, x_2, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_box(0);
x_33 = l_Lean_Server_Completion_dotCompletion___lambda__1(x_2, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Name_getPrefix(x_2);
x_12 = l_Lean_RBNode_findCore___at_Lean_Server_Completion_dotCompletion___spec__1(x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Lean_Server_Completion_dotCompletion___lambda__2(x_2, x_3, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lambda__3___boxed), 10, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = l_Lean_Server_Completion_forEligibleDeclsM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__2(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Server_Completion_dotCompletion___lambda__4(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_instantiateMVars___at_Lean_Server_Completion_dotCompletion___spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames(x_13, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Exception_isInterrupt(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Exception_isRuntime(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
x_20 = lean_box(0);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
return x_15;
}
}
else
{
return x_15;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = l_Lean_Exception_isInterrupt(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_9);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_9, 0);
x_31 = l_Lean_Exception_isInterrupt(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_Exception_isRuntime(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
x_33 = lean_box(0);
lean_ctor_set_tag(x_9, 0);
lean_ctor_set(x_9, 0, x_33);
return x_9;
}
else
{
return x_9;
}
}
else
{
return x_9;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
x_36 = l_Lean_Exception_isInterrupt(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Exception_isRuntime(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
return x_41;
}
}
}
}
}
static lean_object* _init_l_Lean_Server_Completion_dotCompletion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lambda__5), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = l_Lean_Server_Completion_dotCompletion___closed__1;
x_8 = lean_ctor_get(x_4, 3);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotCompletion___lambda__6___boxed), 8, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Server_Completion_dotCompletion___spec__3___rarg), 9, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_7);
x_11 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(x_1, x_2, x_3, x_6, x_10, x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at_Lean_Server_Completion_dotCompletion___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at_Lean_Server_Completion_dotCompletion___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_Completion_dotCompletion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Server_Completion_dotCompletion___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Server_Completion_dotCompletion___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Server_Completion_dotCompletion___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotCompletion___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Server_Completion_dotCompletion___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Server_Completion_dotIdCompletion___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Server_Completion_dotIdCompletion___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Server_Completion_dotIdCompletion___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_15 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f(x_1, x_2, x_14, x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; double x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_ConstantInfo_name(x_4);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_28);
x_29 = lean_unbox_float(x_27);
lean_dec(x_27);
x_30 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_26, x_16, x_5, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; double x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_ConstantInfo_name(x_4);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_unbox_float(x_34);
lean_dec(x_34);
x_38 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_33, x_36, x_5, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_39 = !lean_is_exclusive(x_15);
if (x_39 == 0)
{
return x_15;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Name_isAnonymous(x_3);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_14);
lean_dec(x_14);
x_19 = l_Lean_Server_Completion_dotIdCompletion___lambda__1(x_2, x_3, x_4, x_1, x_18, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; double x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_3);
x_20 = l_Lean_ConstantInfo_name(x_1);
x_21 = l_Lean_Name_getString_x21(x_20);
x_22 = lean_box(0);
x_23 = l_Lean_Name_str___override(x_22, x_21);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_20);
x_25 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3;
x_26 = lean_unbox(x_14);
lean_dec(x_14);
x_27 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem(x_23, x_24, x_26, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_normPrivateName_x3f(x_1, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_Name_getPrefix(x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_22);
x_23 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotIdCompletionMethod(x_22, x_2, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = lean_box(0);
x_34 = l_Lean_Server_Completion_dotIdCompletion___lambda__2(x_2, x_22, x_3, x_21, x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_22);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
return x_23;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 0);
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Name_getPrefix(x_3);
x_13 = l_Lean_RBNode_findCore___at_Lean_Server_Completion_dotCompletion___spec__1(x_2, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_Lean_Server_Completion_dotIdCompletion___lambda__3(x_3, x_4, x_1, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lambda__4___boxed), 11, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_Server_Completion_forEligibleDeclsM___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__2(x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Expr_cleanupAnnotations(x_2);
x_11 = l_Lean_Expr_getAppFn(x_10);
lean_dec(x_10);
x_12 = l_Lean_Expr_cleanupAnnotations(x_11);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames(x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Server_Completion_dotIdCompletion___lambda__5(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
x_20 = l_Lean_Exception_isInterrupt(x_18);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_13);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_Server_Completion_dotIdCompletion___lambda__5(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_23;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
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
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = l_Lean_Exception_isInterrupt(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_24);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Server_Completion_dotIdCompletion___lambda__5(x_1, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Server_Completion_dotIdCompletion___spec__1___rarg___boxed), 8, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(x_1, x_2, x_3, x_4, x_9, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_instantiateMVars___at_Lean_Server_Completion_dotCompletion___spec__2___boxed), 8, 1);
lean_closure_set(x_12, 0, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Server_Completion_dotIdCompletion___lambda__6), 9, 1);
lean_closure_set(x_13, 0, x_5);
x_14 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Server_Completion_dotCompletion___spec__3___rarg), 9, 2);
lean_closure_set(x_14, 0, x_12);
lean_closure_set(x_14, 1, x_13);
x_15 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(x_1, x_2, x_3, x_4, x_14, x_7);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_Server_Completion_dotIdCompletion___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_ReaderT_pure___at_Lean_Server_Completion_dotIdCompletion___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Server_Completion_dotIdCompletion___lambda__1(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Server_Completion_dotIdCompletion___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Server_Completion_dotIdCompletion___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_dotIdCompletion___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Server_Completion_dotIdCompletion___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("field", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 4;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_6, x_5);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_7);
x_17 = lean_array_uget(x_4, x_6);
if (lean_obj_tag(x_17) == 1)
{
lean_object* x_18; double x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2;
lean_inc(x_1);
x_20 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_1, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
size_t x_21; size_t x_22; lean_object* x_23; 
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_6, x_21);
x_23 = lean_box(0);
x_6 = x_22;
x_7 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; double x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2;
x_28 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__3;
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_26);
lean_ctor_set(x_29, 5, x_26);
lean_ctor_set(x_29, 6, x_26);
lean_ctor_set(x_29, 7, x_26);
x_30 = lean_unbox_float(x_25);
lean_dec(x_25);
x_31 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addItem(x_29, x_30, x_26, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = 1;
x_34 = lean_usize_add(x_6, x_33);
x_35 = lean_box(0);
x_6 = x_34;
x_7 = x_35;
x_14 = x_32;
goto _start;
}
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
lean_dec(x_17);
x_37 = 1;
x_38 = lean_usize_add(x_6, x_37);
x_39 = lean_box(0);
x_6 = x_38;
x_7 = x_39;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = 0;
x_12 = l_Lean_getStructureFieldsFlattened(x_3, x_1, x_11);
x_13 = lean_box(0);
x_14 = lean_array_size(x_12);
x_15 = 0;
x_16 = lean_box(0);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1(x_2, x_12, x_13, x_12, x_14, x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Server_Completion_fieldIdCompletion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_Completion_fieldIdCompletion___lambda__1___boxed), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_8 = x_14;
goto block_13;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = 1;
x_17 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2;
x_18 = l_Lean_Name_toString(x_15, x_16, x_17);
x_8 = x_18;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Server_Completion_fieldIdCompletion___lambda__2___boxed), 10, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_Server_Completion_fieldIdCompletion___closed__1;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Server_Completion_dotCompletion___spec__3___rarg), 9, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM(x_1, x_2, x_3, x_4, x_11, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_Completion_fieldIdCompletion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_fieldIdCompletion___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Server_Completion_fieldIdCompletion___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 9;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("), ", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 32;
x_2 = l_Char_utf8Size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_34; lean_object* x_35; lean_object* x_36; double x_37; lean_object* x_38; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 3);
lean_inc(x_21);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_10, x_11, x_12, x_13, x_14, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
x_34 = 1;
x_35 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2;
lean_inc(x_19);
x_36 = l_Lean_Name_toString(x_19, x_34, x_35);
x_37 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2;
lean_inc(x_6);
x_38 = l_Lean_FuzzyMatching_fuzzyMatchScoreWithThreshold_x3f(x_6, x_36, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_20);
lean_dec(x_19);
if (lean_is_scalar(x_27)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_27;
}
lean_ctor_set(x_39, 0, x_26);
if (lean_is_scalar(x_25)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_25;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_24);
x_28 = x_40;
goto block_33;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_102; lean_object* x_120; lean_object* x_121; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_4, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
x_45 = l_Lean_KVMap_findCore(x_8, x_19);
lean_dec(x_19);
x_46 = lean_ctor_get(x_20, 3);
lean_inc(x_46);
lean_dec(x_20);
x_47 = lean_box(0);
lean_inc(x_2);
lean_inc(x_1);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_2);
lean_ctor_set(x_48, 2, x_47);
x_49 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407_(x_48);
lean_ctor_set(x_38, 0, x_49);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_139; 
x_139 = lean_box(0);
x_50 = x_139;
goto block_101;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_43, 0);
x_141 = lean_ctor_get(x_140, 0);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; 
x_142 = lean_box(0);
x_50 = x_142;
goto block_101;
}
else
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_141, 0);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_box(0);
x_50 = x_144;
goto block_101;
}
else
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_143, 0);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; 
x_146 = lean_box(0);
x_50 = x_146;
goto block_101;
}
else
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_ctor_get(x_145, 0);
x_148 = lean_unbox(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_50 = x_149;
goto block_101;
}
else
{
uint8_t x_150; lean_object* x_151; 
lean_dec(x_27);
lean_dec(x_25);
x_150 = 0;
x_151 = l_Lean_Syntax_getRange_x3f(x_5, x_150);
if (lean_obj_tag(x_151) == 0)
{
if (lean_obj_tag(x_45) == 0)
{
x_102 = x_47;
goto block_119;
}
else
{
lean_object* x_152; 
lean_dec(x_44);
x_152 = lean_ctor_get(x_45, 0);
lean_inc(x_152);
lean_dec(x_45);
x_120 = x_47;
x_121 = x_152;
goto block_138;
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_151);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = lean_ctor_get(x_151, 0);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = lean_ctor_get(x_154, 1);
x_158 = lean_ctor_get(x_3, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
lean_inc(x_159);
x_160 = l_Lean_FileMap_utf8PosToLspPos(x_159, x_156);
lean_dec(x_156);
if (x_7 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = l_Lean_FileMap_utf8PosToLspPos(x_159, x_157);
lean_dec(x_157);
lean_ctor_set(x_154, 1, x_161);
lean_ctor_set(x_154, 0, x_160);
lean_inc(x_154);
lean_inc(x_36);
x_162 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_162, 0, x_36);
lean_ctor_set(x_162, 1, x_154);
lean_ctor_set(x_162, 2, x_154);
lean_ctor_set(x_151, 0, x_162);
if (lean_obj_tag(x_45) == 0)
{
x_102 = x_151;
goto block_119;
}
else
{
lean_object* x_163; 
lean_dec(x_44);
x_163 = lean_ctor_get(x_45, 0);
lean_inc(x_163);
lean_dec(x_45);
x_120 = x_151;
x_121 = x_163;
goto block_138;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_164 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__4;
x_165 = lean_nat_add(x_157, x_164);
lean_dec(x_157);
x_166 = l_Lean_FileMap_utf8PosToLspPos(x_159, x_165);
lean_dec(x_165);
lean_ctor_set(x_154, 1, x_166);
lean_ctor_set(x_154, 0, x_160);
lean_inc(x_154);
lean_inc(x_36);
x_167 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_167, 0, x_36);
lean_ctor_set(x_167, 1, x_154);
lean_ctor_set(x_167, 2, x_154);
lean_ctor_set(x_151, 0, x_167);
if (lean_obj_tag(x_45) == 0)
{
x_102 = x_151;
goto block_119;
}
else
{
lean_object* x_168; 
lean_dec(x_44);
x_168 = lean_ctor_get(x_45, 0);
lean_inc(x_168);
lean_dec(x_45);
x_120 = x_151;
x_121 = x_168;
goto block_138;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_154, 0);
x_170 = lean_ctor_get(x_154, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_154);
x_171 = lean_ctor_get(x_3, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
lean_inc(x_172);
x_173 = l_Lean_FileMap_utf8PosToLspPos(x_172, x_169);
lean_dec(x_169);
if (x_7 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = l_Lean_FileMap_utf8PosToLspPos(x_172, x_170);
lean_dec(x_170);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
lean_inc(x_175);
lean_inc(x_36);
x_176 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_176, 0, x_36);
lean_ctor_set(x_176, 1, x_175);
lean_ctor_set(x_176, 2, x_175);
lean_ctor_set(x_151, 0, x_176);
if (lean_obj_tag(x_45) == 0)
{
x_102 = x_151;
goto block_119;
}
else
{
lean_object* x_177; 
lean_dec(x_44);
x_177 = lean_ctor_get(x_45, 0);
lean_inc(x_177);
lean_dec(x_45);
x_120 = x_151;
x_121 = x_177;
goto block_138;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_178 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__4;
x_179 = lean_nat_add(x_170, x_178);
lean_dec(x_170);
x_180 = l_Lean_FileMap_utf8PosToLspPos(x_172, x_179);
lean_dec(x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_173);
lean_ctor_set(x_181, 1, x_180);
lean_inc(x_181);
lean_inc(x_36);
x_182 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_182, 0, x_36);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_182, 2, x_181);
lean_ctor_set(x_151, 0, x_182);
if (lean_obj_tag(x_45) == 0)
{
x_102 = x_151;
goto block_119;
}
else
{
lean_object* x_183; 
lean_dec(x_44);
x_183 = lean_ctor_get(x_45, 0);
lean_inc(x_183);
lean_dec(x_45);
x_120 = x_151;
x_121 = x_183;
goto block_138;
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_151, 0);
lean_inc(x_184);
lean_dec(x_151);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_3, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
lean_inc(x_189);
x_190 = l_Lean_FileMap_utf8PosToLspPos(x_189, x_185);
lean_dec(x_185);
if (x_7 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = l_Lean_FileMap_utf8PosToLspPos(x_189, x_186);
lean_dec(x_186);
if (lean_is_scalar(x_187)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_187;
}
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_192);
lean_inc(x_36);
x_193 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_193, 0, x_36);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_193, 2, x_192);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
if (lean_obj_tag(x_45) == 0)
{
x_102 = x_194;
goto block_119;
}
else
{
lean_object* x_195; 
lean_dec(x_44);
x_195 = lean_ctor_get(x_45, 0);
lean_inc(x_195);
lean_dec(x_45);
x_120 = x_194;
x_121 = x_195;
goto block_138;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_196 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__4;
x_197 = lean_nat_add(x_186, x_196);
lean_dec(x_186);
x_198 = l_Lean_FileMap_utf8PosToLspPos(x_189, x_197);
lean_dec(x_197);
if (lean_is_scalar(x_187)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_187;
}
lean_ctor_set(x_199, 0, x_190);
lean_ctor_set(x_199, 1, x_198);
lean_inc(x_199);
lean_inc(x_36);
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_36);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_199);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
if (lean_obj_tag(x_45) == 0)
{
x_102 = x_201;
goto block_119;
}
else
{
lean_object* x_202; 
lean_dec(x_44);
x_202 = lean_ctor_get(x_45, 0);
lean_inc(x_202);
lean_dec(x_45);
x_120 = x_201;
x_121 = x_202;
goto block_138;
}
}
}
}
}
}
}
}
}
block_101:
{
lean_dec(x_50);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; double x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_51 = lean_data_value_to_string(x_44);
x_52 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_53 = lean_string_append(x_52, x_51);
lean_dec(x_51);
x_54 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_string_append(x_55, x_46);
lean_dec(x_46);
x_57 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_61 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_61, 0, x_36);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_47);
lean_ctor_set(x_61, 3, x_60);
lean_ctor_set(x_61, 4, x_47);
lean_ctor_set(x_61, 5, x_47);
lean_ctor_set(x_61, 6, x_38);
lean_ctor_set(x_61, 7, x_47);
x_62 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_unbox_float(x_42);
lean_dec(x_42);
lean_ctor_set_float(x_62, sizeof(void*)*1, x_63);
x_64 = lean_array_push(x_26, x_62);
if (lean_is_scalar(x_27)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_27;
}
lean_ctor_set(x_65, 0, x_64);
if (lean_is_scalar(x_25)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_25;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_24);
x_28 = x_66;
goto block_33;
}
else
{
uint8_t x_67; 
lean_dec(x_44);
x_67 = !lean_is_exclusive(x_45);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; double x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_data_value_to_string(x_68);
x_70 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_string_append(x_73, x_46);
lean_dec(x_46);
x_75 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_76 = lean_string_append(x_74, x_75);
lean_ctor_set(x_45, 0, x_76);
x_77 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_78 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_78, 0, x_36);
lean_ctor_set(x_78, 1, x_45);
lean_ctor_set(x_78, 2, x_47);
lean_ctor_set(x_78, 3, x_77);
lean_ctor_set(x_78, 4, x_47);
lean_ctor_set(x_78, 5, x_47);
lean_ctor_set(x_78, 6, x_38);
lean_ctor_set(x_78, 7, x_47);
x_79 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_unbox_float(x_42);
lean_dec(x_42);
lean_ctor_set_float(x_79, sizeof(void*)*1, x_80);
x_81 = lean_array_push(x_26, x_79);
if (lean_is_scalar(x_27)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_27;
}
lean_ctor_set(x_82, 0, x_81);
if (lean_is_scalar(x_25)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_25;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_24);
x_28 = x_83;
goto block_33;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; double x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_84 = lean_ctor_get(x_45, 0);
lean_inc(x_84);
lean_dec(x_45);
x_85 = lean_data_value_to_string(x_84);
x_86 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_87 = lean_string_append(x_86, x_85);
lean_dec(x_85);
x_88 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_89 = lean_string_append(x_87, x_88);
x_90 = lean_string_append(x_89, x_46);
lean_dec(x_46);
x_91 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_92 = lean_string_append(x_90, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_95 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_95, 0, x_36);
lean_ctor_set(x_95, 1, x_93);
lean_ctor_set(x_95, 2, x_47);
lean_ctor_set(x_95, 3, x_94);
lean_ctor_set(x_95, 4, x_47);
lean_ctor_set(x_95, 5, x_47);
lean_ctor_set(x_95, 6, x_38);
lean_ctor_set(x_95, 7, x_47);
x_96 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_unbox_float(x_42);
lean_dec(x_42);
lean_ctor_set_float(x_96, sizeof(void*)*1, x_97);
x_98 = lean_array_push(x_26, x_96);
if (lean_is_scalar(x_27)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_27;
}
lean_ctor_set(x_99, 0, x_98);
if (lean_is_scalar(x_25)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_25;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_24);
x_28 = x_100;
goto block_33;
}
}
}
block_119:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; double x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_103 = lean_data_value_to_string(x_44);
x_104 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_105 = lean_string_append(x_104, x_103);
lean_dec(x_103);
x_106 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_107 = lean_string_append(x_105, x_106);
x_108 = lean_string_append(x_107, x_46);
lean_dec(x_46);
x_109 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_110 = lean_string_append(x_108, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_113 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_113, 0, x_36);
lean_ctor_set(x_113, 1, x_111);
lean_ctor_set(x_113, 2, x_47);
lean_ctor_set(x_113, 3, x_112);
lean_ctor_set(x_113, 4, x_102);
lean_ctor_set(x_113, 5, x_47);
lean_ctor_set(x_113, 6, x_38);
lean_ctor_set(x_113, 7, x_47);
x_114 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_114, 0, x_113);
x_115 = lean_unbox_float(x_42);
lean_dec(x_42);
lean_ctor_set_float(x_114, sizeof(void*)*1, x_115);
x_116 = lean_array_push(x_26, x_114);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_24);
x_28 = x_118;
goto block_33;
}
block_138:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; double x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_122 = lean_data_value_to_string(x_121);
x_123 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_124 = lean_string_append(x_123, x_122);
lean_dec(x_122);
x_125 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_126 = lean_string_append(x_124, x_125);
x_127 = lean_string_append(x_126, x_46);
lean_dec(x_46);
x_128 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_129 = lean_string_append(x_127, x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_132 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_132, 0, x_36);
lean_ctor_set(x_132, 1, x_130);
lean_ctor_set(x_132, 2, x_47);
lean_ctor_set(x_132, 3, x_131);
lean_ctor_set(x_132, 4, x_120);
lean_ctor_set(x_132, 5, x_47);
lean_ctor_set(x_132, 6, x_38);
lean_ctor_set(x_132, 7, x_47);
x_133 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_unbox_float(x_42);
lean_dec(x_42);
lean_ctor_set_float(x_133, sizeof(void*)*1, x_134);
x_135 = lean_array_push(x_26, x_133);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_24);
x_28 = x_137;
goto block_33;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_248; lean_object* x_266; lean_object* x_267; 
x_203 = lean_ctor_get(x_38, 0);
lean_inc(x_203);
lean_dec(x_38);
x_204 = lean_ctor_get(x_4, 0);
x_205 = lean_ctor_get(x_20, 1);
lean_inc(x_205);
x_206 = l_Lean_KVMap_findCore(x_8, x_19);
lean_dec(x_19);
x_207 = lean_ctor_get(x_20, 3);
lean_inc(x_207);
lean_dec(x_20);
x_208 = lean_box(0);
lean_inc(x_2);
lean_inc(x_1);
x_209 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_209, 0, x_1);
lean_ctor_set(x_209, 1, x_2);
lean_ctor_set(x_209, 2, x_208);
x_210 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407_(x_209);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_285; 
x_285 = lean_box(0);
x_212 = x_285;
goto block_247;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_204, 0);
x_287 = lean_ctor_get(x_286, 0);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; 
x_288 = lean_box(0);
x_212 = x_288;
goto block_247;
}
else
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_287, 0);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; 
x_290 = lean_box(0);
x_212 = x_290;
goto block_247;
}
else
{
lean_object* x_291; 
x_291 = lean_ctor_get(x_289, 0);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; 
x_292 = lean_box(0);
x_212 = x_292;
goto block_247;
}
else
{
lean_object* x_293; uint8_t x_294; 
x_293 = lean_ctor_get(x_291, 0);
x_294 = lean_unbox(x_293);
if (x_294 == 0)
{
lean_object* x_295; 
x_295 = lean_box(0);
x_212 = x_295;
goto block_247;
}
else
{
uint8_t x_296; lean_object* x_297; 
lean_dec(x_27);
lean_dec(x_25);
x_296 = 0;
x_297 = l_Lean_Syntax_getRange_x3f(x_5, x_296);
if (lean_obj_tag(x_297) == 0)
{
if (lean_obj_tag(x_206) == 0)
{
x_248 = x_208;
goto block_265;
}
else
{
lean_object* x_298; 
lean_dec(x_205);
x_298 = lean_ctor_get(x_206, 0);
lean_inc(x_298);
lean_dec(x_206);
x_266 = x_208;
x_267 = x_298;
goto block_284;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 x_300 = x_297;
} else {
 lean_dec_ref(x_297);
 x_300 = lean_box(0);
}
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_303 = x_299;
} else {
 lean_dec_ref(x_299);
 x_303 = lean_box(0);
}
x_304 = lean_ctor_get(x_3, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec(x_304);
lean_inc(x_305);
x_306 = l_Lean_FileMap_utf8PosToLspPos(x_305, x_301);
lean_dec(x_301);
if (x_7 == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_307 = l_Lean_FileMap_utf8PosToLspPos(x_305, x_302);
lean_dec(x_302);
if (lean_is_scalar(x_303)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_303;
}
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
lean_inc(x_308);
lean_inc(x_36);
x_309 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_309, 0, x_36);
lean_ctor_set(x_309, 1, x_308);
lean_ctor_set(x_309, 2, x_308);
if (lean_is_scalar(x_300)) {
 x_310 = lean_alloc_ctor(1, 1, 0);
} else {
 x_310 = x_300;
}
lean_ctor_set(x_310, 0, x_309);
if (lean_obj_tag(x_206) == 0)
{
x_248 = x_310;
goto block_265;
}
else
{
lean_object* x_311; 
lean_dec(x_205);
x_311 = lean_ctor_get(x_206, 0);
lean_inc(x_311);
lean_dec(x_206);
x_266 = x_310;
x_267 = x_311;
goto block_284;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_312 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__4;
x_313 = lean_nat_add(x_302, x_312);
lean_dec(x_302);
x_314 = l_Lean_FileMap_utf8PosToLspPos(x_305, x_313);
lean_dec(x_313);
if (lean_is_scalar(x_303)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_303;
}
lean_ctor_set(x_315, 0, x_306);
lean_ctor_set(x_315, 1, x_314);
lean_inc(x_315);
lean_inc(x_36);
x_316 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_316, 0, x_36);
lean_ctor_set(x_316, 1, x_315);
lean_ctor_set(x_316, 2, x_315);
if (lean_is_scalar(x_300)) {
 x_317 = lean_alloc_ctor(1, 1, 0);
} else {
 x_317 = x_300;
}
lean_ctor_set(x_317, 0, x_316);
if (lean_obj_tag(x_206) == 0)
{
x_248 = x_317;
goto block_265;
}
else
{
lean_object* x_318; 
lean_dec(x_205);
x_318 = lean_ctor_get(x_206, 0);
lean_inc(x_318);
lean_dec(x_206);
x_266 = x_317;
x_267 = x_318;
goto block_284;
}
}
}
}
}
}
}
}
block_247:
{
lean_dec(x_212);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; double x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_213 = lean_data_value_to_string(x_205);
x_214 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_215 = lean_string_append(x_214, x_213);
lean_dec(x_213);
x_216 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_217 = lean_string_append(x_215, x_216);
x_218 = lean_string_append(x_217, x_207);
lean_dec(x_207);
x_219 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_220 = lean_string_append(x_218, x_219);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_223 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_223, 0, x_36);
lean_ctor_set(x_223, 1, x_221);
lean_ctor_set(x_223, 2, x_208);
lean_ctor_set(x_223, 3, x_222);
lean_ctor_set(x_223, 4, x_208);
lean_ctor_set(x_223, 5, x_208);
lean_ctor_set(x_223, 6, x_211);
lean_ctor_set(x_223, 7, x_208);
x_224 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_224, 0, x_223);
x_225 = lean_unbox_float(x_203);
lean_dec(x_203);
lean_ctor_set_float(x_224, sizeof(void*)*1, x_225);
x_226 = lean_array_push(x_26, x_224);
if (lean_is_scalar(x_27)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_27;
}
lean_ctor_set(x_227, 0, x_226);
if (lean_is_scalar(x_25)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_25;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_24);
x_28 = x_228;
goto block_33;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; double x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_205);
x_229 = lean_ctor_get(x_206, 0);
lean_inc(x_229);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_230 = x_206;
} else {
 lean_dec_ref(x_206);
 x_230 = lean_box(0);
}
x_231 = lean_data_value_to_string(x_229);
x_232 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_233 = lean_string_append(x_232, x_231);
lean_dec(x_231);
x_234 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_235 = lean_string_append(x_233, x_234);
x_236 = lean_string_append(x_235, x_207);
lean_dec(x_207);
x_237 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_238 = lean_string_append(x_236, x_237);
if (lean_is_scalar(x_230)) {
 x_239 = lean_alloc_ctor(1, 1, 0);
} else {
 x_239 = x_230;
}
lean_ctor_set(x_239, 0, x_238);
x_240 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_241 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_241, 0, x_36);
lean_ctor_set(x_241, 1, x_239);
lean_ctor_set(x_241, 2, x_208);
lean_ctor_set(x_241, 3, x_240);
lean_ctor_set(x_241, 4, x_208);
lean_ctor_set(x_241, 5, x_208);
lean_ctor_set(x_241, 6, x_211);
lean_ctor_set(x_241, 7, x_208);
x_242 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_242, 0, x_241);
x_243 = lean_unbox_float(x_203);
lean_dec(x_203);
lean_ctor_set_float(x_242, sizeof(void*)*1, x_243);
x_244 = lean_array_push(x_26, x_242);
if (lean_is_scalar(x_27)) {
 x_245 = lean_alloc_ctor(1, 1, 0);
} else {
 x_245 = x_27;
}
lean_ctor_set(x_245, 0, x_244);
if (lean_is_scalar(x_25)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_25;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_24);
x_28 = x_246;
goto block_33;
}
}
block_265:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; double x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_249 = lean_data_value_to_string(x_205);
x_250 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_251 = lean_string_append(x_250, x_249);
lean_dec(x_249);
x_252 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_253 = lean_string_append(x_251, x_252);
x_254 = lean_string_append(x_253, x_207);
lean_dec(x_207);
x_255 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_256 = lean_string_append(x_254, x_255);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_256);
x_258 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_259 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_259, 0, x_36);
lean_ctor_set(x_259, 1, x_257);
lean_ctor_set(x_259, 2, x_208);
lean_ctor_set(x_259, 3, x_258);
lean_ctor_set(x_259, 4, x_248);
lean_ctor_set(x_259, 5, x_208);
lean_ctor_set(x_259, 6, x_211);
lean_ctor_set(x_259, 7, x_208);
x_260 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_260, 0, x_259);
x_261 = lean_unbox_float(x_203);
lean_dec(x_203);
lean_ctor_set_float(x_260, sizeof(void*)*1, x_261);
x_262 = lean_array_push(x_26, x_260);
x_263 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_263, 0, x_262);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_24);
x_28 = x_264;
goto block_33;
}
block_284:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; double x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_268 = lean_data_value_to_string(x_267);
x_269 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2;
x_270 = lean_string_append(x_269, x_268);
lean_dec(x_268);
x_271 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3;
x_272 = lean_string_append(x_270, x_271);
x_273 = lean_string_append(x_272, x_207);
lean_dec(x_207);
x_274 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_275 = lean_string_append(x_273, x_274);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_275);
x_277 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1;
x_278 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_278, 0, x_36);
lean_ctor_set(x_278, 1, x_276);
lean_ctor_set(x_278, 2, x_208);
lean_ctor_set(x_278, 3, x_277);
lean_ctor_set(x_278, 4, x_266);
lean_ctor_set(x_278, 5, x_208);
lean_ctor_set(x_278, 6, x_211);
lean_ctor_set(x_278, 7, x_208);
x_279 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_279, 0, x_278);
x_280 = lean_unbox_float(x_203);
lean_dec(x_203);
lean_ctor_set_float(x_279, sizeof(void*)*1, x_280);
x_281 = lean_array_push(x_26, x_279);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_24);
x_28 = x_283;
goto block_33;
}
}
}
block_33:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_9 = x_21;
x_10 = x_31;
x_15 = x_30;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = l_Lean_getOptionDecls(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_10, 2);
x_17 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1;
x_18 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_14, x_17, x_8, x_9, x_10, x_11, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Server_Completion_optionCompletion___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Server_Completion_optionCompletion___closed__2;
x_3 = l_Lean_Server_Completion_optionCompletion___closed__1;
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
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__3;
x_2 = l_Lean_Server_Completion_optionCompletion___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_Completion_optionCompletion___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_4, x_7);
x_9 = 0;
x_10 = l_Lean_Syntax_getSubstring_x3f(x_8, x_9, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1;
x_12 = lean_box(x_9);
lean_inc(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lambda__1___boxed), 12, 7);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_5);
lean_closure_set(x_13, 4, x_8);
lean_closure_set(x_13, 5, x_11);
lean_closure_set(x_13, 6, x_12);
x_14 = l_Lean_Server_Completion_optionCompletion___closed__4;
x_15 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_3, x_14, x_13, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 2);
lean_inc(x_18);
x_19 = lean_string_utf8_at_end(x_17, x_18);
if (x_19 == 0)
{
uint32_t x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_string_utf8_get(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_21 = 46;
x_22 = lean_uint32_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_16, 2);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_string_utf8_extract(x_23, x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_27 = lean_box(x_9);
lean_inc(x_3);
x_28 = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lambda__1___boxed), 12, 7);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_2);
lean_closure_set(x_28, 2, x_3);
lean_closure_set(x_28, 3, x_5);
lean_closure_set(x_28, 4, x_8);
lean_closure_set(x_28, 5, x_26);
lean_closure_set(x_28, 6, x_27);
x_29 = l_Lean_Server_Completion_optionCompletion___closed__4;
x_30 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_3, x_29, x_28, x_6);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_16, 2);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_string_utf8_extract(x_31, x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_35 = l_Lean_Server_Completion_optionCompletion___closed__5;
x_36 = lean_string_append(x_34, x_35);
x_37 = 1;
x_38 = lean_box(x_37);
lean_inc(x_3);
x_39 = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lambda__1___boxed), 12, 7);
lean_closure_set(x_39, 0, x_1);
lean_closure_set(x_39, 1, x_2);
lean_closure_set(x_39, 2, x_3);
lean_closure_set(x_39, 3, x_5);
lean_closure_set(x_39, 4, x_8);
lean_closure_set(x_39, 5, x_36);
lean_closure_set(x_39, 6, x_38);
x_40 = l_Lean_Server_Completion_optionCompletion___closed__4;
x_41 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_3, x_40, x_39, x_6);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_18);
lean_dec(x_17);
x_42 = lean_ctor_get(x_16, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_16, 2);
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_string_utf8_extract(x_42, x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
x_46 = lean_box(x_9);
lean_inc(x_3);
x_47 = lean_alloc_closure((void*)(l_Lean_Server_Completion_optionCompletion___lambda__1___boxed), 12, 7);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_2);
lean_closure_set(x_47, 2, x_3);
lean_closure_set(x_47, 3, x_5);
lean_closure_set(x_47, 4, x_8);
lean_closure_set(x_47, 5, x_45);
lean_closure_set(x_47, 6, x_46);
x_48 = l_Lean_Server_Completion_optionCompletion___closed__4;
x_49 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_3, x_48, x_47, x_6);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Server_Completion_optionCompletion___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_optionCompletion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_Completion_optionCompletion(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_tacticCompletion___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_7, 3);
lean_inc(x_12);
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_11);
x_14 = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_toJsonResolvableCompletionItemData____x40_Lean_Server_Completion_CompletionResolution___hyg_407_(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_4, x_16);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_18; lean_object* x_19; double x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3;
x_19 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set(x_19, 4, x_11);
lean_ctor_set(x_19, 5, x_11);
lean_ctor_set(x_19, 6, x_15);
lean_ctor_set(x_19, 7, x_11);
x_20 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3;
x_21 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_float(x_21, sizeof(void*)*1, x_20);
x_22 = lean_array_uset(x_9, x_4, x_21);
x_4 = x_17;
x_5 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; double x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
lean_ctor_set(x_12, 0, x_27);
x_28 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3;
x_29 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_12);
lean_ctor_set(x_29, 3, x_28);
lean_ctor_set(x_29, 4, x_11);
lean_ctor_set(x_29, 5, x_11);
lean_ctor_set(x_29, 6, x_15);
lean_ctor_set(x_29, 7, x_11);
x_30 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3;
x_31 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_float(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_uset(x_9, x_4, x_31);
x_4 = x_17;
x_5 = x_32;
goto _start;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; double x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_12, 0);
lean_inc(x_34);
lean_dec(x_12);
x_35 = 1;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3;
x_39 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_39, 0, x_10);
lean_ctor_set(x_39, 1, x_11);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_38);
lean_ctor_set(x_39, 4, x_11);
lean_ctor_set(x_39, 5, x_11);
lean_ctor_set(x_39, 6, x_15);
lean_ctor_set(x_39, 7, x_11);
x_40 = l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3;
x_41 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_float(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_uset(x_9, x_4, x_41);
x_4 = x_17;
x_5 = x_42;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_Doc_allTacticDocs(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_array_size(x_10);
x_12 = 0;
x_13 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_tacticCompletion___spec__1(x_1, x_2, x_11, x_12, x_10);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_array_size(x_14);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_tacticCompletion___spec__1(x_1, x_2, x_16, x_17, x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Completion_tacticCompletion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_closure((void*)(l_Lean_Server_Completion_tacticCompletion___lambda__1), 7, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = l_Lean_LocalContext_empty;
x_7 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_3, x_6, x_5, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_Completion_tacticCompletion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Server_Completion_tacticCompletion___spec__1(x_1, x_2, x_6, x_7, x_5);
return x_8;
}
}
lean_object* initialize_Lean_Data_FuzzyMatching(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Doc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_CompletionResolution(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Server_Completion_EligibleHeaderDecls(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Completion_CompletionCollectors(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_FuzzyMatching(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Doc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_CompletionResolution(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Completion_EligibleHeaderDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1 = _init_l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__1);
l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__2 = _init_l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__2();
lean_mark_persistent(l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__2);
l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__3 = _init_l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__3();
l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__4 = _init_l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__4();
lean_mark_persistent(l_Lean_Server_Completion_instInhabitedScoredCompletionItem___closed__4);
l_Lean_Server_Completion_instInhabitedScoredCompletionItem = _init_l_Lean_Server_Completion_instInhabitedScoredCompletionItem();
lean_mark_persistent(l_Lean_Server_Completion_instInhabitedScoredCompletionItem);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__1 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__1);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__2);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__3 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___lambda__3___closed__3);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__1 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__1);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__2 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__2);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__3 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__3);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__4);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__5 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__5();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__5);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__6 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__6();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__6);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__7 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__7();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__7);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__8 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__8();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addUnresolvedCompletionItem___closed__8);
l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1 = _init_l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1();
lean_mark_persistent(l_Lean_isProjectionFn___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__1___closed__1);
l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1 = _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__1);
l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2 = _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__2);
l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3 = _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__3);
l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4 = _init_l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4();
lean_mark_persistent(l_Lean_getConstInfo___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getCompletionKindForDecl___spec__3___closed__4);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__1);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__2);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addKeywordCompletionItem___closed__3);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__1);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__2);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_addNamespaceCompletionItem___closed__3);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_runM___closed__1);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__1);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__2();
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___closed__3();
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_matchDecl_x3f___lambda__2___boxed__const__1);
l_panic___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___spec__1___closed__1 = _init_l_panic___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___spec__1___closed__1);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__1);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__2);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__3);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__4 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__4();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_truncate_go___closed__4);
l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1 = _init_l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1();
lean_mark_persistent(l_Lean_Server_Completion_matchNamespace___closed__1___boxed__const__1);
l_Lean_Server_Completion_matchNamespace___closed__1 = _init_l_Lean_Server_Completion_matchNamespace___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_matchNamespace___closed__1);
l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1 = _init_l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__1);
l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2 = _init_l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lean_Server_Completion_completeNamespaces___spec__1___closed__2);
l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1 = _init_l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_completeNamespaces___lambda__3___closed__1);
l_Lean_Server_Completion_completeNamespaces___closed__1 = _init_l_Lean_Server_Completion_completeNamespaces___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_completeNamespaces___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___spec__1___closed__2);
l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1 = _init_l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_isDotCompletionMethod___lambda__2___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__16___closed__1);
l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__1 = _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__1();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__1);
l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__2 = _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__2();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__2);
l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__3 = _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__3();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__3);
l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__4 = _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__4();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__4);
l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__5 = _init_l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__5();
lean_mark_persistent(l___private_Lean_Structure_0__Lean_setStructureResolutionOrder___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_getDotCompletionTypeNames_visit___spec__25___closed__5);
l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1 = _init_l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Server_Completion_CompletionCollectors_0__Lean_Server_Completion_idCompletionCore___spec__1___lambda__1___closed__1);
l_Lean_Server_Completion_dotCompletion___closed__1 = _init_l_Lean_Server_Completion_dotCompletion___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_dotCompletion___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__2);
l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Server_Completion_fieldIdCompletion___spec__1___closed__3);
l_Lean_Server_Completion_fieldIdCompletion___closed__1 = _init_l_Lean_Server_Completion_fieldIdCompletion___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_fieldIdCompletion___closed__1);
l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__1);
l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__2);
l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__3);
l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__4 = _init_l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__4();
lean_mark_persistent(l_Lean_RBNode_forIn_visit___at_Lean_Server_Completion_optionCompletion___spec__1___closed__4);
l_Lean_Server_Completion_optionCompletion___closed__1 = _init_l_Lean_Server_Completion_optionCompletion___closed__1();
lean_mark_persistent(l_Lean_Server_Completion_optionCompletion___closed__1);
l_Lean_Server_Completion_optionCompletion___closed__2 = _init_l_Lean_Server_Completion_optionCompletion___closed__2();
lean_mark_persistent(l_Lean_Server_Completion_optionCompletion___closed__2);
l_Lean_Server_Completion_optionCompletion___closed__3 = _init_l_Lean_Server_Completion_optionCompletion___closed__3();
lean_mark_persistent(l_Lean_Server_Completion_optionCompletion___closed__3);
l_Lean_Server_Completion_optionCompletion___closed__4 = _init_l_Lean_Server_Completion_optionCompletion___closed__4();
lean_mark_persistent(l_Lean_Server_Completion_optionCompletion___closed__4);
l_Lean_Server_Completion_optionCompletion___closed__5 = _init_l_Lean_Server_Completion_optionCompletion___closed__5();
lean_mark_persistent(l_Lean_Server_Completion_optionCompletion___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
