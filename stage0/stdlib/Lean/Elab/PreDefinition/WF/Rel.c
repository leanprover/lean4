// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Rel
// Imports: Init Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Cases Lean.Meta.Tactic.Rename Lean.Elab.SyntheticMVars Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.WF.TerminationHint
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__3;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8;
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__5;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2;
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__1(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__6(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Elab_WF_elabWFRel___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1;
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_List_mapTR_loop___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2;
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__2(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4;
lean_object* l_Lean_FVarId_getUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__2;
static lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__3(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5;
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4;
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__2;
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2;
lean_object* l_Lean_MVarId_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Elab_WF_elabWFRel___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__4;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.PreDefinition.WF.Rel", 30);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Elab.PreDefinition.WF.Rel.0.Lean.Elab.WF.unpackMutual.go", 70);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3;
x_3 = lean_unsigned_to_nat(20u);
x_4 = lean_unsigned_to_nat(45u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = lean_nat_dec_lt(x_2, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_array_push(x_5, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Meta_Cases_cases(x_3, x_4, x_20, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_22);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5;
x_28 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1(x_27, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_fget(x_22, x_29);
x_31 = lean_array_fget(x_22, x_14);
lean_dec(x_22);
x_32 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_get_size(x_35);
x_37 = lean_nat_dec_lt(x_29, x_36);
lean_dec(x_36);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_lt(x_29, x_40);
lean_dec(x_40);
if (x_37 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_35);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lean_instInhabitedExpr;
x_44 = l___private_Init_Util_0__outOfBounds___rarg(x_43);
x_45 = l_Lean_Expr_fvarId_x21(x_44);
if (x_41 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_39);
x_46 = l___private_Init_Util_0__outOfBounds___rarg(x_43);
x_47 = l_Lean_Expr_fvarId_x21(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
x_49 = lean_array_push(x_5, x_48);
x_2 = x_32;
x_3 = x_34;
x_4 = x_45;
x_5 = x_49;
x_12 = x_23;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_array_fget(x_39, x_29);
lean_dec(x_39);
x_52 = l_Lean_Expr_fvarId_x21(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_42);
x_54 = lean_array_push(x_5, x_53);
x_2 = x_32;
x_3 = x_34;
x_4 = x_45;
x_5 = x_54;
x_12 = x_23;
goto _start;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_38, 0);
lean_inc(x_56);
lean_dec(x_38);
x_57 = lean_array_fget(x_35, x_29);
lean_dec(x_35);
x_58 = l_Lean_Expr_fvarId_x21(x_57);
if (x_41 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_39);
x_59 = l_Lean_instInhabitedExpr;
x_60 = l___private_Init_Util_0__outOfBounds___rarg(x_59);
x_61 = l_Lean_Expr_fvarId_x21(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
x_63 = lean_array_push(x_5, x_62);
x_2 = x_32;
x_3 = x_34;
x_4 = x_58;
x_5 = x_63;
x_12 = x_23;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_array_fget(x_39, x_29);
lean_dec(x_39);
x_66 = l_Lean_Expr_fvarId_x21(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_56);
x_68 = lean_array_push(x_5, x_67);
x_2 = x_32;
x_3 = x_34;
x_4 = x_58;
x_5 = x_68;
x_12 = x_23;
goto _start;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_21);
if (x_70 == 0)
{
return x_21;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_21, 0);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_21);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_13 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go(x_1, x_11, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Elab.PreDefinition.WF.Rel.0.Lean.Elab.WF.unpackUnary.go", 69);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(51u);
x_4 = lean_unsigned_to_nat(86u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_7);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
x_17 = lean_nat_dec_lt(x_2, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_18 = l_Lean_instInhabitedName;
x_19 = l_Array_back___rarg(x_18, x_3);
lean_dec(x_3);
x_20 = l_Lean_MVarId_rename(x_4, x_5, x_19, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_nat_add(x_6, x_2);
x_22 = lean_array_get_size(x_3);
x_23 = lean_nat_dec_lt(x_21, x_22);
lean_dec(x_22);
x_24 = lean_box(0);
if (x_23 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_21);
x_58 = l_Lean_instInhabitedName;
x_59 = l___private_Init_Util_0__outOfBounds___rarg(x_58);
x_25 = x_59;
goto block_57;
}
else
{
lean_object* x_60; 
x_60 = lean_array_fget(x_3, x_21);
lean_dec(x_21);
x_25 = x_60;
goto block_57;
}
block_57:
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = 0;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_30 = lean_array_push(x_29, x_28);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_31 = l_Lean_Meta_Cases_cases(x_4, x_5, x_30, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_array_get_size(x_32);
x_35 = lean_nat_dec_eq(x_34, x_15);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3;
x_37 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(x_36, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_fget(x_32, x_38);
lean_dec(x_32);
x_40 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_array_get_size(x_43);
x_45 = lean_nat_dec_lt(x_15, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_43);
x_46 = l_Lean_instInhabitedExpr;
x_47 = l___private_Init_Util_0__outOfBounds___rarg(x_46);
x_48 = l_Lean_Expr_fvarId_x21(x_47);
x_49 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(x_6, x_3, x_1, x_40, x_42, x_48, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_array_fget(x_43, x_15);
lean_dec(x_43);
x_51 = l_Lean_Expr_fvarId_x21(x_50);
x_52 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(x_6, x_3, x_1, x_40, x_42, x_51, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
return x_31;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_31, 0);
x_55 = lean_ctor_get(x_31, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_31);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("definition", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wf", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2;
x_3 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("i: ", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", varNames: ", 12);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", goal: ", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4;
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(x_3, x_4, x_2, x_5, x_6, x_1, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
lean_inc(x_4);
x_22 = l_Nat_repr(x_4);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_2);
x_29 = lean_array_to_list(lean_box(0), x_2);
x_30 = lean_box(0);
x_31 = l_List_mapTR_loop___at_Lean_Meta_substCore___spec__6(x_29, x_30);
x_32 = l_Lean_MessageData_ofList(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_5);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_5);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_14, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(x_3, x_4, x_2, x_5, x_6, x_1, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_42);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = l_Lean_Expr_fvarId_x21(x_13);
lean_inc(x_6);
x_17 = l_Lean_FVarId_getUserName(x_16, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_15, x_2, x_18);
x_2 = x_21;
x_3 = x_22;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_6);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_10, x_7);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_9, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_9, x_24);
lean_dec(x_9);
x_26 = lean_array_fget(x_2, x_10);
x_27 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__2;
lean_inc(x_26);
x_28 = l_Lean_Syntax_isOfKind(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_26);
x_29 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_25;
x_10 = x_29;
x_11 = lean_box(0);
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_array_get_size(x_12);
x_32 = lean_nat_sub(x_31, x_4);
lean_dec(x_31);
x_33 = lean_nat_sub(x_32, x_3);
lean_dec(x_32);
x_34 = lean_nat_add(x_33, x_10);
lean_dec(x_33);
x_35 = l_Lean_Syntax_getId(x_26);
lean_dec(x_26);
x_36 = lean_array_set(x_12, x_34, x_35);
lean_dec(x_34);
x_37 = lean_nat_add(x_10, x_8);
lean_dec(x_10);
x_9 = x_25;
x_10 = x_37;
x_11 = lean_box(0);
x_12 = x_36;
goto _start;
}
}
else
{
lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_12);
lean_ctor_set(x_39, 1, x_19);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_11, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_3, x_5);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 0);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_18);
lean_inc(x_1);
x_20 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_1, x_16, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_20, 0, x_6);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
lean_dec(x_18);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
lean_dec(x_21);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_29);
lean_ctor_set(x_6, 0, x_2);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_5 = x_31;
x_13 = x_28;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_6);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_37);
lean_inc(x_1);
x_38 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_1, x_16, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
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
lean_inc(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_2);
lean_ctor_set(x_47, 1, x_46);
x_48 = 1;
x_49 = lean_usize_add(x_5, x_48);
x_5 = x_49;
x_6 = x_47;
x_13 = x_45;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_29; 
lean_inc(x_16);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_16);
x_18 = x_29;
x_19 = x_12;
goto block_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 2);
lean_inc(x_35);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_32);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_18 = x_38;
x_19 = x_12;
goto block_28;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_40 = lean_ctor_get(x_30, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_30, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_30, 0);
lean_dec(x_42);
x_43 = lean_array_fget(x_33, x_34);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_34, x_44);
lean_dec(x_34);
lean_ctor_set(x_30, 1, x_45);
x_46 = l_Lean_LocalDecl_userName(x_31);
x_47 = lean_name_eq(x_46, x_43);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_49 = l_Lean_MVarId_rename(x_32, x_48, x_43, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_30);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_18 = x_53;
x_19 = x_51;
goto block_28;
}
else
{
uint8_t x_54; 
lean_dec(x_30);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_43);
lean_dec(x_31);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_30);
lean_ctor_set(x_58, 1, x_32);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_18 = x_59;
x_19 = x_12;
goto block_28;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_30);
x_60 = lean_array_fget(x_33, x_34);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_34, x_61);
lean_dec(x_34);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_33);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_35);
x_64 = l_Lean_LocalDecl_userName(x_31);
x_65 = lean_name_eq(x_64, x_60);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Lean_LocalDecl_fvarId(x_31);
lean_dec(x_31);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_67 = l_Lean_MVarId_rename(x_32, x_66, x_60, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_18 = x_71;
x_19 = x_69;
goto block_28;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_63);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_72 = lean_ctor_get(x_67, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
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
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_60);
lean_dec(x_31);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_63);
lean_ctor_set(x_76, 1, x_32);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_18 = x_77;
x_19 = x_12;
goto block_28;
}
}
}
}
block_28:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
lean_inc(x_1);
if (lean_is_scalar(x_17)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_17;
}
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_usize_add(x_4, x_25);
x_4 = x_26;
x_5 = x_24;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_array_get_size(x_11);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(x_1, x_12, x_11, x_15, x_16, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_box(0);
x_23 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
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
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
lean_dec(x_1);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
x_37 = lean_array_get_size(x_34);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_40 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(x_35, x_34, x_38, x_39, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_34);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_box(0);
x_46 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_44, x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_40);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_40, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_49);
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
return x_40;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_17 = x_5;
} else {
 lean_dec_ref(x_5);
 x_17 = lean_box(0);
}
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_30; 
lean_inc(x_16);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_16);
x_18 = x_30;
x_19 = x_12;
goto block_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_31, 2);
lean_inc(x_36);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_33);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_18 = x_39;
x_19 = x_12;
goto block_29;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_41 = lean_ctor_get(x_31, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_31, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_31, 0);
lean_dec(x_43);
x_44 = lean_array_fget(x_34, x_35);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_35, x_45);
lean_dec(x_35);
lean_ctor_set(x_31, 1, x_46);
x_47 = l_Lean_LocalDecl_userName(x_32);
x_48 = lean_name_eq(x_47, x_44);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_50 = l_Lean_MVarId_rename(x_33, x_49, x_44, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_31);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_18 = x_54;
x_19 = x_52;
goto block_29;
}
else
{
uint8_t x_55; 
lean_dec(x_31);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_44);
lean_dec(x_32);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_31);
lean_ctor_set(x_59, 1, x_33);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_18 = x_60;
x_19 = x_12;
goto block_29;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_31);
x_61 = lean_array_fget(x_34, x_35);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_35, x_62);
lean_dec(x_35);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_34);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_36);
x_65 = l_Lean_LocalDecl_userName(x_32);
x_66 = lean_name_eq(x_65, x_61);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Lean_LocalDecl_fvarId(x_32);
lean_dec(x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_68 = l_Lean_MVarId_rename(x_33, x_67, x_61, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_18 = x_72;
x_19 = x_70;
goto block_29;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_64);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
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
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_61);
lean_dec(x_32);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_33);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_18 = x_78;
x_19 = x_12;
goto block_29;
}
}
}
}
block_29:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_17)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_17;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec(x_16);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
lean_inc(x_1);
if (lean_is_scalar(x_17)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_17;
}
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_4, x_26);
x_4 = x_27;
x_5 = x_25;
x_12 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_2, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_get_size(x_21);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(x_22, x_21, x_25, x_26, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_unsigned_to_nat(1u);
lean_inc(x_1);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 2, x_15);
lean_inc(x_1);
x_17 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(x_2, x_3, x_1, x_4, x_16, x_14, x_1, x_15, x_1, x_14, lean_box(0), x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_16);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("too many variable names", 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
lean_dec(x_6);
x_14 = lean_array_get_size(x_5);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_9);
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(x_15, x_16, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_18);
x_21 = lean_nat_dec_lt(x_20, x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(x_1, x_2, x_3, x_4, x_18, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_18);
lean_dec(x_1);
x_24 = lean_array_fget(x_3, x_20);
lean_dec(x_20);
x_25 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2;
x_26 = l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(x_24, x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_9);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
x_16 = lean_nat_dec_lt(x_15, x_5);
x_17 = lean_ctor_get(x_1, 5);
lean_inc(x_17);
lean_dec(x_1);
if (x_16 == 0)
{
lean_object* x_47; 
x_47 = lean_unsigned_to_nat(0u);
x_18 = x_47;
goto block_46;
}
else
{
lean_object* x_48; 
x_48 = lean_nat_sub(x_5, x_15);
x_18 = x_48;
goto block_46;
}
block_46:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed), 13, 4);
lean_closure_set(x_19, 0, x_15);
lean_closure_set(x_19, 1, x_6);
lean_closure_set(x_19, 2, x_14);
lean_closure_set(x_19, 3, x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(x_17, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_3);
x_23 = l_Lean_Elab_Term_getMVarDecl(x_3, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_21);
x_27 = l_Array_toSubarray___rarg(x_21, x_26, x_2);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_3);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(x_30, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_array_get_size(x_21);
x_36 = lean_nat_sub(x_35, x_2);
lean_dec(x_35);
x_37 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(x_2, x_21, x_36, x_26, x_34, x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___boxed(lean_object** _args) {
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
x_20 = l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Elab_WF_elabWFRel___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_st_ref_take(x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_12, 7);
x_18 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_17, x_1, x_2);
lean_ctor_set(x_12, 7, x_18);
x_19 = lean_st_ref_set(x_6, x_11, x_13);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
x_28 = lean_ctor_get(x_12, 2);
x_29 = lean_ctor_get(x_12, 3);
x_30 = lean_ctor_get(x_12, 4);
x_31 = lean_ctor_get(x_12, 5);
x_32 = lean_ctor_get(x_12, 6);
x_33 = lean_ctor_get(x_12, 7);
x_34 = lean_ctor_get(x_12, 8);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_35 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_33, x_1, x_2);
x_36 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_27);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_36, 3, x_29);
lean_ctor_set(x_36, 4, x_30);
lean_ctor_set(x_36, 5, x_31);
lean_ctor_set(x_36, 6, x_32);
lean_ctor_set(x_36, 7, x_35);
lean_ctor_set(x_36, 8, x_34);
lean_ctor_set(x_11, 0, x_36);
x_37 = lean_st_ref_set(x_6, x_11, x_13);
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
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_42 = lean_ctor_get(x_11, 1);
x_43 = lean_ctor_get(x_11, 2);
x_44 = lean_ctor_get(x_11, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_45 = lean_ctor_get(x_12, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_12, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_12, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_12, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_12, 5);
lean_inc(x_50);
x_51 = lean_ctor_get(x_12, 6);
lean_inc(x_51);
x_52 = lean_ctor_get(x_12, 7);
lean_inc(x_52);
x_53 = lean_ctor_get(x_12, 8);
lean_inc(x_53);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 lean_ctor_release(x_12, 5);
 lean_ctor_release(x_12, 6);
 lean_ctor_release(x_12, 7);
 lean_ctor_release(x_12, 8);
 x_54 = x_12;
} else {
 lean_dec_ref(x_12);
 x_54 = lean_box(0);
}
x_55 = l_Lean_PersistentHashMap_insert___at_Lean_MVarId_assign___spec__1(x_52, x_1, x_2);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 9, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_46);
lean_ctor_set(x_56, 2, x_47);
lean_ctor_set(x_56, 3, x_48);
lean_ctor_set(x_56, 4, x_49);
lean_ctor_set(x_56, 5, x_50);
lean_ctor_set(x_56, 6, x_51);
lean_ctor_set(x_56, 7, x_55);
lean_ctor_set(x_56, 8, x_53);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_42);
lean_ctor_set(x_57, 2, x_43);
lean_ctor_set(x_57, 3, x_44);
x_58 = lean_st_ref_set(x_6, x_57, x_13);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_15 = lean_box(0);
x_16 = 1;
x_17 = lean_box(x_16);
x_18 = lean_box(x_16);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_19, 0, x_13);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_15);
x_20 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_19, x_20, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_MVarId_assign___at_Lean_Elab_WF_elabWFRel___spec__4(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_15 = lean_array_uget(x_2, x_4);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec(x_15);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_25, 0);
x_34 = lean_ctor_get(x_25, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_26, 2);
lean_inc(x_37);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_28);
lean_dec(x_27);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_5);
x_16 = x_39;
x_17 = x_12;
goto block_24;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_41 = lean_ctor_get(x_26, 2);
lean_dec(x_41);
x_42 = lean_ctor_get(x_26, 1);
lean_dec(x_42);
x_43 = lean_ctor_get(x_26, 0);
lean_dec(x_43);
x_44 = lean_array_fget(x_35, x_36);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_36, x_45);
lean_dec(x_36);
lean_ctor_set(x_26, 1, x_46);
x_47 = lean_ctor_get(x_33, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_33, 2);
lean_inc(x_49);
x_50 = lean_nat_dec_lt(x_48, x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_28);
lean_dec(x_27);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_5);
x_16 = x_51;
x_17 = x_12;
goto block_24;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_33);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_53 = lean_ctor_get(x_33, 2);
lean_dec(x_53);
x_54 = lean_ctor_get(x_33, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_33, 0);
lean_dec(x_55);
x_56 = lean_array_fget(x_47, x_48);
x_57 = lean_nat_add(x_48, x_45);
lean_dec(x_48);
lean_ctor_set(x_33, 1, x_57);
x_58 = lean_ctor_get(x_30, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_30, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_30, 2);
lean_inc(x_60);
x_61 = lean_nat_dec_lt(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_44);
lean_dec(x_28);
lean_dec(x_27);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_5);
x_16 = x_62;
x_17 = x_12;
goto block_24;
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_30);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_30, 2);
lean_dec(x_64);
x_65 = lean_ctor_get(x_30, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_30, 0);
lean_dec(x_66);
x_67 = lean_array_fget(x_58, x_59);
x_68 = lean_nat_add(x_59, x_45);
lean_dec(x_59);
lean_ctor_set(x_30, 1, x_68);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_56);
lean_inc(x_1);
x_69 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_44, x_1, x_28, x_27, x_67, x_56, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_70);
x_72 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5___lambda__1), 9, 2);
lean_closure_set(x_72, 0, x_70);
lean_closure_set(x_72, 1, x_56);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_73 = l_Lean_MVarId_withContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_70, x_72, x_6, x_7, x_8, x_9, x_10, x_11, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_5);
x_16 = x_75;
x_17 = x_74;
goto block_24;
}
else
{
uint8_t x_76; 
lean_dec(x_30);
lean_dec(x_33);
lean_dec(x_26);
lean_free_object(x_25);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_73);
if (x_76 == 0)
{
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 0);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_73);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_30);
lean_dec(x_33);
lean_dec(x_56);
lean_dec(x_26);
lean_free_object(x_25);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_69);
if (x_80 == 0)
{
return x_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_69, 0);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_69);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_30);
x_84 = lean_array_fget(x_58, x_59);
x_85 = lean_nat_add(x_59, x_45);
lean_dec(x_59);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_58);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_60);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_56);
lean_inc(x_1);
x_87 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_44, x_1, x_28, x_27, x_84, x_56, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_84);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_88);
x_90 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5___lambda__1), 9, 2);
lean_closure_set(x_90, 0, x_88);
lean_closure_set(x_90, 1, x_56);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_91 = l_Lean_MVarId_withContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_88, x_90, x_6, x_7, x_8, x_9, x_10, x_11, x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_ctor_set(x_5, 0, x_86);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_5);
x_16 = x_93;
x_17 = x_92;
goto block_24;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_86);
lean_dec(x_33);
lean_dec(x_26);
lean_free_object(x_25);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_86);
lean_dec(x_33);
lean_dec(x_56);
lean_dec(x_26);
lean_free_object(x_25);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_100 = x_87;
} else {
 lean_dec_ref(x_87);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
lean_dec(x_33);
x_102 = lean_array_fget(x_47, x_48);
x_103 = lean_nat_add(x_48, x_45);
lean_dec(x_48);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_47);
lean_ctor_set(x_104, 1, x_103);
lean_ctor_set(x_104, 2, x_49);
x_105 = lean_ctor_get(x_30, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_30, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_30, 2);
lean_inc(x_107);
x_108 = lean_nat_dec_lt(x_106, x_107);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_44);
lean_dec(x_28);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_104);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_5);
x_16 = x_109;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_110 = x_30;
} else {
 lean_dec_ref(x_30);
 x_110 = lean_box(0);
}
x_111 = lean_array_fget(x_105, x_106);
x_112 = lean_nat_add(x_106, x_45);
lean_dec(x_106);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 3, 0);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_105);
lean_ctor_set(x_113, 1, x_112);
lean_ctor_set(x_113, 2, x_107);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_102);
lean_inc(x_1);
x_114 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_44, x_1, x_28, x_27, x_111, x_102, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_111);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_115);
x_117 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5___lambda__1), 9, 2);
lean_closure_set(x_117, 0, x_115);
lean_closure_set(x_117, 1, x_102);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_118 = l_Lean_MVarId_withContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_115, x_117, x_6, x_7, x_8, x_9, x_10, x_11, x_116);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
lean_ctor_set(x_25, 0, x_104);
lean_ctor_set(x_5, 0, x_113);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_5);
x_16 = x_120;
x_17 = x_119;
goto block_24;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_113);
lean_dec(x_104);
lean_dec(x_26);
lean_free_object(x_25);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_121 = lean_ctor_get(x_118, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_123 = x_118;
} else {
 lean_dec_ref(x_118);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_113);
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_26);
lean_free_object(x_25);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_125 = lean_ctor_get(x_114, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_114, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_127 = x_114;
} else {
 lean_dec_ref(x_114);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_26);
x_129 = lean_array_fget(x_35, x_36);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_36, x_130);
lean_dec(x_36);
x_132 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_132, 0, x_35);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_132, 2, x_37);
x_133 = lean_ctor_get(x_33, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_33, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_33, 2);
lean_inc(x_135);
x_136 = lean_nat_dec_lt(x_134, x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_129);
lean_dec(x_28);
lean_dec(x_27);
lean_ctor_set(x_25, 1, x_132);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_5);
x_16 = x_137;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 lean_ctor_release(x_33, 2);
 x_138 = x_33;
} else {
 lean_dec_ref(x_33);
 x_138 = lean_box(0);
}
x_139 = lean_array_fget(x_133, x_134);
x_140 = lean_nat_add(x_134, x_130);
lean_dec(x_134);
if (lean_is_scalar(x_138)) {
 x_141 = lean_alloc_ctor(0, 3, 0);
} else {
 x_141 = x_138;
}
lean_ctor_set(x_141, 0, x_133);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_135);
x_142 = lean_ctor_get(x_30, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_30, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_30, 2);
lean_inc(x_144);
x_145 = lean_nat_dec_lt(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_139);
lean_dec(x_129);
lean_dec(x_28);
lean_dec(x_27);
lean_ctor_set(x_25, 1, x_132);
lean_ctor_set(x_25, 0, x_141);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_5);
x_16 = x_146;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_147 = x_30;
} else {
 lean_dec_ref(x_30);
 x_147 = lean_box(0);
}
x_148 = lean_array_fget(x_142, x_143);
x_149 = lean_nat_add(x_143, x_130);
lean_dec(x_143);
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 3, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_142);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_150, 2, x_144);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_139);
lean_inc(x_1);
x_151 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_129, x_1, x_28, x_27, x_148, x_139, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_148);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_152);
x_154 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5___lambda__1), 9, 2);
lean_closure_set(x_154, 0, x_152);
lean_closure_set(x_154, 1, x_139);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_155 = l_Lean_MVarId_withContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_152, x_154, x_6, x_7, x_8, x_9, x_10, x_11, x_153);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
lean_ctor_set(x_25, 1, x_132);
lean_ctor_set(x_25, 0, x_141);
lean_ctor_set(x_5, 0, x_150);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_5);
x_16 = x_157;
x_17 = x_156;
goto block_24;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_150);
lean_dec(x_141);
lean_dec(x_132);
lean_free_object(x_25);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_160 = x_155;
} else {
 lean_dec_ref(x_155);
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
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_150);
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_132);
lean_free_object(x_25);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_162 = lean_ctor_get(x_151, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_151, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_164 = x_151;
} else {
 lean_dec_ref(x_151);
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
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_166 = lean_ctor_get(x_25, 0);
lean_inc(x_166);
lean_dec(x_25);
x_167 = lean_ctor_get(x_26, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_26, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_26, 2);
lean_inc(x_169);
x_170 = lean_nat_dec_lt(x_168, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_28);
lean_dec(x_27);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_166);
lean_ctor_set(x_171, 1, x_26);
lean_ctor_set(x_5, 1, x_171);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_5);
x_16 = x_172;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_173 = x_26;
} else {
 lean_dec_ref(x_26);
 x_173 = lean_box(0);
}
x_174 = lean_array_fget(x_167, x_168);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_nat_add(x_168, x_175);
lean_dec(x_168);
if (lean_is_scalar(x_173)) {
 x_177 = lean_alloc_ctor(0, 3, 0);
} else {
 x_177 = x_173;
}
lean_ctor_set(x_177, 0, x_167);
lean_ctor_set(x_177, 1, x_176);
lean_ctor_set(x_177, 2, x_169);
x_178 = lean_ctor_get(x_166, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_166, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_166, 2);
lean_inc(x_180);
x_181 = lean_nat_dec_lt(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_174);
lean_dec(x_28);
lean_dec(x_27);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_166);
lean_ctor_set(x_182, 1, x_177);
lean_ctor_set(x_5, 1, x_182);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_5);
x_16 = x_183;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 lean_ctor_release(x_166, 2);
 x_184 = x_166;
} else {
 lean_dec_ref(x_166);
 x_184 = lean_box(0);
}
x_185 = lean_array_fget(x_178, x_179);
x_186 = lean_nat_add(x_179, x_175);
lean_dec(x_179);
if (lean_is_scalar(x_184)) {
 x_187 = lean_alloc_ctor(0, 3, 0);
} else {
 x_187 = x_184;
}
lean_ctor_set(x_187, 0, x_178);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_187, 2, x_180);
x_188 = lean_ctor_get(x_30, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_30, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_30, 2);
lean_inc(x_190);
x_191 = lean_nat_dec_lt(x_189, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_185);
lean_dec(x_174);
lean_dec(x_28);
lean_dec(x_27);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_187);
lean_ctor_set(x_192, 1, x_177);
lean_ctor_set(x_5, 1, x_192);
x_193 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_193, 0, x_5);
x_16 = x_193;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_194 = x_30;
} else {
 lean_dec_ref(x_30);
 x_194 = lean_box(0);
}
x_195 = lean_array_fget(x_188, x_189);
x_196 = lean_nat_add(x_189, x_175);
lean_dec(x_189);
if (lean_is_scalar(x_194)) {
 x_197 = lean_alloc_ctor(0, 3, 0);
} else {
 x_197 = x_194;
}
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_196);
lean_ctor_set(x_197, 2, x_190);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_185);
lean_inc(x_1);
x_198 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_174, x_1, x_28, x_27, x_195, x_185, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_195);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
lean_inc(x_199);
x_201 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5___lambda__1), 9, 2);
lean_closure_set(x_201, 0, x_199);
lean_closure_set(x_201, 1, x_185);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_202 = l_Lean_MVarId_withContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_199, x_201, x_6, x_7, x_8, x_9, x_10, x_11, x_200);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_187);
lean_ctor_set(x_204, 1, x_177);
lean_ctor_set(x_5, 1, x_204);
lean_ctor_set(x_5, 0, x_197);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_5);
x_16 = x_205;
x_17 = x_203;
goto block_24;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_197);
lean_dec(x_187);
lean_dec(x_177);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_206 = lean_ctor_get(x_202, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_202, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_208 = x_202;
} else {
 lean_dec_ref(x_202);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_197);
lean_dec(x_187);
lean_dec(x_185);
lean_dec(x_177);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_210 = lean_ctor_get(x_198, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_198, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_212 = x_198;
} else {
 lean_dec_ref(x_198);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_214 = lean_ctor_get(x_5, 0);
lean_inc(x_214);
lean_dec(x_5);
x_215 = lean_ctor_get(x_25, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_216 = x_25;
} else {
 lean_dec_ref(x_25);
 x_216 = lean_box(0);
}
x_217 = lean_ctor_get(x_26, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_26, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_26, 2);
lean_inc(x_219);
x_220 = lean_nat_dec_lt(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_28);
lean_dec(x_27);
if (lean_is_scalar(x_216)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_216;
}
lean_ctor_set(x_221, 0, x_215);
lean_ctor_set(x_221, 1, x_26);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_214);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_223, 0, x_222);
x_16 = x_223;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 x_224 = x_26;
} else {
 lean_dec_ref(x_26);
 x_224 = lean_box(0);
}
x_225 = lean_array_fget(x_217, x_218);
x_226 = lean_unsigned_to_nat(1u);
x_227 = lean_nat_add(x_218, x_226);
lean_dec(x_218);
if (lean_is_scalar(x_224)) {
 x_228 = lean_alloc_ctor(0, 3, 0);
} else {
 x_228 = x_224;
}
lean_ctor_set(x_228, 0, x_217);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set(x_228, 2, x_219);
x_229 = lean_ctor_get(x_215, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_215, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_215, 2);
lean_inc(x_231);
x_232 = lean_nat_dec_lt(x_230, x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_225);
lean_dec(x_28);
lean_dec(x_27);
if (lean_is_scalar(x_216)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_216;
}
lean_ctor_set(x_233, 0, x_215);
lean_ctor_set(x_233, 1, x_228);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_214);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_234);
x_16 = x_235;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 x_236 = x_215;
} else {
 lean_dec_ref(x_215);
 x_236 = lean_box(0);
}
x_237 = lean_array_fget(x_229, x_230);
x_238 = lean_nat_add(x_230, x_226);
lean_dec(x_230);
if (lean_is_scalar(x_236)) {
 x_239 = lean_alloc_ctor(0, 3, 0);
} else {
 x_239 = x_236;
}
lean_ctor_set(x_239, 0, x_229);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set(x_239, 2, x_231);
x_240 = lean_ctor_get(x_214, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_214, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_214, 2);
lean_inc(x_242);
x_243 = lean_nat_dec_lt(x_241, x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_242);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_237);
lean_dec(x_225);
lean_dec(x_28);
lean_dec(x_27);
if (lean_is_scalar(x_216)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_216;
}
lean_ctor_set(x_244, 0, x_239);
lean_ctor_set(x_244, 1, x_228);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_214);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_16 = x_246;
x_17 = x_12;
goto block_24;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 x_247 = x_214;
} else {
 lean_dec_ref(x_214);
 x_247 = lean_box(0);
}
x_248 = lean_array_fget(x_240, x_241);
x_249 = lean_nat_add(x_241, x_226);
lean_dec(x_241);
if (lean_is_scalar(x_247)) {
 x_250 = lean_alloc_ctor(0, 3, 0);
} else {
 x_250 = x_247;
}
lean_ctor_set(x_250, 0, x_240);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set(x_250, 2, x_242);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_237);
lean_inc(x_1);
x_251 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_225, x_1, x_28, x_27, x_248, x_237, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_248);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
lean_inc(x_252);
x_254 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5___lambda__1), 9, 2);
lean_closure_set(x_254, 0, x_252);
lean_closure_set(x_254, 1, x_237);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_255 = l_Lean_MVarId_withContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_252, x_254, x_6, x_7, x_8, x_9, x_10, x_11, x_253);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
lean_dec(x_255);
if (lean_is_scalar(x_216)) {
 x_257 = lean_alloc_ctor(0, 2, 0);
} else {
 x_257 = x_216;
}
lean_ctor_set(x_257, 0, x_239);
lean_ctor_set(x_257, 1, x_228);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_250);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_16 = x_259;
x_17 = x_256;
goto block_24;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_250);
lean_dec(x_239);
lean_dec(x_228);
lean_dec(x_216);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_260 = lean_ctor_get(x_255, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_255, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_262 = x_255;
} else {
 lean_dec_ref(x_255);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_250);
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_228);
lean_dec(x_216);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_264 = lean_ctor_get(x_251, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_251, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_266 = x_251;
} else {
 lean_dec_ref(x_251);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
}
}
}
block_24:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = 1;
x_22 = lean_usize_add(x_4, x_21);
x_4 = x_22;
x_5 = x_20;
x_12 = x_17;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__6___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invImage", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_1);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_3);
lean_ctor_set_uint8(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to apply 'invImage'", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_box(0);
lean_inc(x_9);
x_15 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_14, x_9, x_10, x_11, x_12, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_mvarId_x21(x_16);
x_19 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_19, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_18);
x_24 = l_Lean_MVarId_apply(x_18, x_21, x_23, x_9, x_10, x_11, x_12, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__5;
x_28 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__1___rarg(x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__5;
x_32 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__2___rarg(x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__5;
x_36 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__3___rarg(x_35, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_24, 1);
lean_inc(x_38);
lean_dec(x_24);
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_42 = l_Lean_Meta_intro1Core(x_39, x_41, x_9, x_10, x_11, x_12, x_38);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_47 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(x_2, x_46, x_45, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_array_get_size(x_3);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Array_toSubarray___rarg(x_3, x_51, x_50);
x_53 = lean_array_get_size(x_4);
x_54 = l_Array_toSubarray___rarg(x_4, x_51, x_53);
x_55 = lean_array_get_size(x_2);
x_56 = l_Array_toSubarray___rarg(x_2, x_51, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_array_get_size(x_48);
x_60 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_61 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_62 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5(x_5, x_48, x_60, x_61, x_58, x_7, x_8, x_9, x_10, x_11, x_12, x_49);
lean_dec(x_48);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_40);
x_64 = l_Lean_Expr_mvar___override(x_40);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_65 = lean_infer_type(x_64, x_9, x_10, x_11, x_12, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_69 = l_Lean_Meta_synthInstance(x_66, x_68, x_9, x_10, x_11, x_12, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__1(x_40, x_70, x_7, x_8, x_9, x_10, x_11, x_12, x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Expr_mvar___override(x_18);
x_75 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_74, x_7, x_8, x_9, x_10, x_11, x_12, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_apply_8(x_6, x_76, x_7, x_8, x_9, x_10, x_11, x_12, x_77);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_40);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_79 = !lean_is_exclusive(x_69);
if (x_79 == 0)
{
return x_69;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_69, 0);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_69);
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
lean_dec(x_40);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_83 = !lean_is_exclusive(x_65);
if (x_83 == 0)
{
return x_65;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_65, 0);
x_85 = lean_ctor_get(x_65, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_65);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_40);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_87 = !lean_is_exclusive(x_62);
if (x_87 == 0)
{
return x_62;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_62, 0);
x_89 = lean_ctor_get(x_62, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_62);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_40);
lean_dec(x_18);
lean_dec(x_12);
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
x_91 = !lean_is_exclusive(x_47);
if (x_91 == 0)
{
return x_47;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_47, 0);
x_93 = lean_ctor_get(x_47, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_47);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_40);
lean_dec(x_18);
lean_dec(x_12);
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
x_95 = !lean_is_exclusive(x_42);
if (x_95 == 0)
{
return x_42;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_42, 0);
x_97 = lean_ctor_get(x_42, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_42);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_37);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_99 = lean_ctor_get(x_24, 1);
lean_inc(x_99);
lean_dec(x_24);
x_100 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__5;
x_101 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__6___rarg(x_100, x_7, x_8, x_9, x_10, x_11, x_12, x_99);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_101;
}
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_18);
lean_dec(x_12);
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
x_102 = !lean_is_exclusive(x_24);
if (x_102 == 0)
{
return x_24;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_24, 0);
x_104 = lean_ctor_get(x_24, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_24);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_18);
lean_dec(x_12);
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
x_106 = !lean_is_exclusive(x_20);
if (x_106 == 0)
{
return x_20;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_20, 0);
x_108 = lean_ctor_get(x_20, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_20);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1), 13, 6);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_5);
lean_closure_set(x_16, 5, x_6);
x_17 = l_Lean_Elab_Term_withDeclName___rarg(x_7, x_16, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("WellFoundedRelation", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel___rarg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabWFRel start: ", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_15 = l_Lean_Meta_getLevel(x_4, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_WF_elabWFRel___rarg___closed__2;
x_21 = l_Lean_Expr_const___override(x_20, x_19);
x_22 = l_Lean_Expr_app___override(x_21, x_4);
x_23 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_22, x_1, x_5, x_6, x_3, x_7, x_2, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_27);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = 0;
x_32 = lean_box(0);
lean_inc(x_10);
x_33 = l_Lean_Meta_mkFreshTypeMVar(x_31, x_32, x_10, x_11, x_12, x_13, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_mvarId_x21(x_34);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_Elab_WF_elabWFRel___rarg___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_23, x_41, x_8, x_9, x_10, x_11, x_12, x_13, x_35);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_22, x_1, x_5, x_6, x_3, x_7, x_2, x_43, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
lean_dec(x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_12);
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
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
return x_15;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_15);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg), 14, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at_Lean_Elab_WF_elabWFRel___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_assign___at_Lean_Elab_WF_elabWFRel___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel___spec__5(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel___spec__6___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_16;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_SyntheticMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_TerminationHint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_SyntheticMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_TerminationHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1 = _init_l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__2 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2);
l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__1);
l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__2);
l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__3);
l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__4);
l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__5 = _init_l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1___closed__5);
l_Lean_Elab_WF_elabWFRel___rarg___closed__1 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__1);
l_Lean_Elab_WF_elabWFRel___rarg___closed__2 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__2);
l_Lean_Elab_WF_elabWFRel___rarg___closed__3 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__3);
l_Lean_Elab_WF_elabWFRel___rarg___closed__4 = _init_l_Lean_Elab_WF_elabWFRel___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel___rarg___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
