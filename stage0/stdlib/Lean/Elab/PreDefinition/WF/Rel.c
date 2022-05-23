// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Rel
// Imports: Init Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Rename Lean.Meta.Tactic.Intro Lean.Elab.SyntheticMVars Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.WF.TerminationHint
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__12;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_WF_instInhabitedTerminationByElement;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rename(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getNumCandidateArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__11;
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__3;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1;
static lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12;
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__6;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__4;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8;
uint8_t l_Lean_Expr_isLit(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1;
static lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___boxed(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
static lean_object* l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5(lean_object*);
lean_object* l_Lean_Elab_Term_SavedState_restore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__8;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__9;
lean_object* l_Lean_Elab_Term_withDeclName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__13;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__2;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__7;
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__10;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___boxed(lean_object**);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel___rarg___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__3;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
lean_object* l_Lean_Elab_Term_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_isForbidden___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1;
static lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_uget(x_2, x_4);
x_8 = lean_ctor_get_uint8(x_7, sizeof(void*)*4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
size_t x_13; size_t x_14; 
lean_dec(x_7);
x_13 = 1;
x_14 = lean_usize_add(x_4, x_13);
{
size_t _tmp_3 = x_14;
lean_object* _tmp_4 = x_1;
x_4 = _tmp_3;
x_5 = _tmp_4;
}
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Elab_WF_instInhabitedTerminationByElement;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get(x_3, x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1() {
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_4 = 0;
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1;
x_6 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(x_5, x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(x_1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(x_1);
lean_dec(x_1);
return x_2;
}
}
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
x_3 = lean_unsigned_to_nat(26u);
x_4 = lean_unsigned_to_nat(44u);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
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
x_36 = l_Lean_instInhabitedExpr;
x_37 = lean_array_get(x_36, x_35, x_29);
lean_dec(x_35);
x_38 = l_Lean_Expr_fvarId_x21(x_37);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_array_get(x_36, x_40, x_29);
lean_dec(x_40);
x_42 = l_Lean_Expr_fvarId_x21(x_41);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_5, x_44);
x_2 = x_32;
x_3 = x_34;
x_4 = x_38;
x_5 = x_45;
x_12 = x_23;
goto _start;
}
}
else
{
uint8_t x_47; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_21);
if (x_47 == 0)
{
return x_21;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_21, 0);
x_49 = lean_ctor_get(x_21, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_21);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
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
x_3 = lean_unsigned_to_nat(50u);
x_4 = lean_unsigned_to_nat(85u);
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
x_20 = l_Lean_Meta_rename(x_4, x_5, x_19, x_10, x_11, x_12, x_13, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_nat_add(x_6, x_2);
x_22 = l_Lean_instInhabitedName;
x_23 = lean_array_get(x_22, x_3, x_21);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = 0;
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_26);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_29 = lean_array_push(x_28, x_27);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = l_Lean_Meta_Cases_cases(x_4, x_5, x_29, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_array_get_size(x_31);
x_34 = lean_nat_dec_eq(x_33, x_15);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__3;
x_36 = l_panic___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___spec__1(x_35, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_fget(x_31, x_37);
lean_dec(x_31);
x_39 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_instInhabitedExpr;
x_44 = lean_array_get(x_43, x_42, x_15);
lean_dec(x_42);
x_45 = l_Lean_Expr_fvarId_x21(x_44);
x_46 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(x_6, x_3, x_1, x_39, x_41, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_32);
return x_46;
}
}
else
{
uint8_t x_47; 
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("definition", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("wf", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__4;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("i: ", 3);
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
x_1 = lean_mk_string_from_bytes(", varNames: ", 12);
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
x_1 = lean_mk_string_from_bytes(", goal: ", 8);
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
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
x_42 = lean_st_ref_get(x_12, x_13);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = 0;
x_15 = x_47;
x_16 = x_46;
goto block_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_dec(x_42);
x_49 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_14, x_7, x_8, x_9, x_10, x_11, x_12, x_48);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unbox(x_50);
lean_dec(x_50);
x_15 = x_52;
x_16 = x_51;
goto block_41;
}
block_41:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(x_3, x_4, x_2, x_5, x_6, x_1, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_4);
x_19 = l_Nat_repr(x_4);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__8;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__10;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_2);
x_26 = lean_array_to_list(lean_box(0), x_2);
x_27 = lean_box(0);
x_28 = l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(x_26, x_27);
x_29 = l_Lean_MessageData_ofList(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__12;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_inc(x_5);
x_33 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_33, 0, x_5);
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14;
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_14, x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1(x_3, x_4, x_2, x_5, x_6, x_1, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_39);
return x_40;
}
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
x_17 = l_Lean_Meta_getLocalDecl(x_16, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_userName(x_18);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_15, x_2, x_20);
x_2 = x_22;
x_3 = x_23;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_3, x_18);
lean_dec(x_3);
x_20 = l_Lean_instInhabitedSyntax;
x_21 = lean_array_get(x_20, x_1, x_4);
x_22 = l_Lean_Syntax_isIdent(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
x_23 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_19;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_array_get_size(x_7);
x_26 = lean_nat_sub(x_25, x_2);
lean_dec(x_25);
x_27 = lean_nat_add(x_26, x_4);
lean_dec(x_26);
x_28 = l_Lean_Syntax_getId(x_21);
lean_dec(x_21);
x_29 = lean_array_set(x_7, x_27, x_28);
lean_dec(x_27);
x_30 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_19;
x_4 = x_30;
x_7 = x_29;
goto _start;
}
}
else
{
lean_object* x_32; 
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_7);
lean_ctor_set(x_32, 1, x_14);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_14);
return x_33;
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
x_20 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_1, x_16, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_38 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_1, x_16, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_49 = l_Lean_Meta_rename(x_32, x_48, x_43, x_8, x_9, x_10, x_11, x_12);
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
x_67 = l_Lean_Meta_rename(x_32, x_66, x_60, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_23 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_21, x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
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
x_46 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_44, x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_43);
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
x_50 = l_Lean_Meta_rename(x_33, x_49, x_44, x_8, x_9, x_10, x_11, x_12);
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
x_68 = l_Lean_Meta_rename(x_33, x_67, x_61, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_11 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5(x_2, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(1u);
lean_inc(x_12);
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(x_11, x_12, x_12, x_13, x_12, x_14, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
lean_dec(x_3);
x_11 = lean_array_get_size(x_2);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
lean_inc(x_6);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__1(x_12, x_13, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_17, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(x_1, x_15, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_15);
x_23 = l_Lean_instInhabitedSyntax;
x_24 = lean_array_get(x_23, x_18, x_17);
lean_dec(x_17);
x_25 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2;
x_26 = l_Lean_throwErrorAt___at_Lean_Elab_Term_Quotation_getAntiquotationIds___spec__1(x_24, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_6);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed), 10, 1);
lean_closure_set(x_14, 0, x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__3___rarg(x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_getMVarDecl(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_16);
x_22 = l_Array_toSubarray___rarg(x_16, x_21, x_2);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_3);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_26 = l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4(x_25, x_24, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_get_size(x_16);
x_31 = lean_nat_sub(x_30, x_2);
lean_dec(x_30);
x_32 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go(x_2, x_16, x_31, x_21, x_29, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_forInAux___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_forIn___at___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_sub(x_9, x_1);
lean_dec(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = lean_ctor_get(x_12, 5);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1___boxed), 8, 1);
lean_closure_set(x_16, 0, x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg(x_15, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_14, x_3, x_18);
x_3 = x_21;
x_4 = x_22;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getNumCandidateArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_getNumCandidateArgs___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("SizeOf", 6);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sizeOf", 6);
return x_1;
}
}
static lean_object* _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2;
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_array_uget(x_12, x_3);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get(x_4, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_17, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_26 = lean_nat_add(x_17, x_19);
lean_ctor_set(x_15, 0, x_26);
x_27 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_28 = lean_array_push(x_27, x_13);
x_29 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Meta_mkAppM(x_29, x_28, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Meta_whnfD(x_31, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Expr_isLit(x_34);
lean_dec(x_34);
if (x_36 == 0)
{
size_t x_37; size_t x_38; 
lean_dec(x_17);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_3 = x_38;
x_9 = x_35;
goto _start;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; 
x_40 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_40);
x_41 = 1;
x_42 = lean_usize_add(x_3, x_41);
x_3 = x_42;
x_9 = x_35;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; 
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_45);
x_46 = 1;
x_47 = lean_usize_add(x_3, x_46);
x_3 = x_47;
x_9 = x_44;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
x_49 = lean_ctor_get(x_30, 1);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_50);
x_51 = 1;
x_52 = lean_usize_add(x_3, x_51);
x_3 = x_52;
x_9 = x_49;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_15);
x_54 = lean_nat_add(x_17, x_19);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_18);
lean_ctor_set(x_55, 2, x_19);
x_56 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_57 = lean_array_push(x_56, x_13);
x_58 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_Lean_Meta_mkAppM(x_58, x_57, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_62 = l_Lean_Meta_whnfD(x_60, x_5, x_6, x_7, x_8, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_isLit(x_63);
lean_dec(x_63);
if (x_65 == 0)
{
size_t x_66; size_t x_67; 
lean_dec(x_17);
lean_ctor_set(x_4, 0, x_55);
x_66 = 1;
x_67 = lean_usize_add(x_3, x_66);
x_3 = x_67;
x_9 = x_64;
goto _start;
}
else
{
lean_object* x_69; size_t x_70; size_t x_71; 
x_69 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_69);
lean_ctor_set(x_4, 0, x_55);
x_70 = 1;
x_71 = lean_usize_add(x_3, x_70);
x_3 = x_71;
x_9 = x_64;
goto _start;
}
}
else
{
lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; 
x_73 = lean_ctor_get(x_62, 1);
lean_inc(x_73);
lean_dec(x_62);
x_74 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_74);
lean_ctor_set(x_4, 0, x_55);
x_75 = 1;
x_76 = lean_usize_add(x_3, x_75);
x_3 = x_76;
x_9 = x_73;
goto _start;
}
}
else
{
lean_object* x_78; lean_object* x_79; size_t x_80; size_t x_81; 
x_78 = lean_ctor_get(x_59, 1);
lean_inc(x_78);
lean_dec(x_59);
x_79 = lean_array_push(x_16, x_17);
lean_ctor_set(x_4, 1, x_79);
lean_ctor_set(x_4, 0, x_55);
x_80 = 1;
x_81 = lean_usize_add(x_3, x_80);
x_3 = x_81;
x_9 = x_78;
goto _start;
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_4, 0);
x_84 = lean_ctor_get(x_4, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_4);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_83, 2);
lean_inc(x_87);
x_88 = lean_nat_dec_lt(x_85, x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_83);
lean_ctor_set(x_89, 1, x_84);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_9);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 lean_ctor_release(x_83, 2);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
x_92 = lean_nat_add(x_85, x_87);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 3, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_86);
lean_ctor_set(x_93, 2, x_87);
x_94 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_95 = lean_array_push(x_94, x_13);
x_96 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_97 = l_Lean_Meta_mkAppM(x_96, x_95, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_100 = l_Lean_Meta_whnfD(x_98, x_5, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Expr_isLit(x_101);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; size_t x_105; size_t x_106; 
lean_dec(x_85);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_93);
lean_ctor_set(x_104, 1, x_84);
x_105 = 1;
x_106 = lean_usize_add(x_3, x_105);
x_3 = x_106;
x_4 = x_104;
x_9 = x_102;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; size_t x_110; size_t x_111; 
x_108 = lean_array_push(x_84, x_85);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_93);
lean_ctor_set(x_109, 1, x_108);
x_110 = 1;
x_111 = lean_usize_add(x_3, x_110);
x_3 = x_111;
x_4 = x_109;
x_9 = x_102;
goto _start;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_116; size_t x_117; 
x_113 = lean_ctor_get(x_100, 1);
lean_inc(x_113);
lean_dec(x_100);
x_114 = lean_array_push(x_84, x_85);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_93);
lean_ctor_set(x_115, 1, x_114);
x_116 = 1;
x_117 = lean_usize_add(x_3, x_116);
x_3 = x_117;
x_4 = x_115;
x_9 = x_113;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; size_t x_123; 
x_119 = lean_ctor_get(x_97, 1);
lean_inc(x_119);
lean_dec(x_97);
x_120 = lean_array_push(x_84, x_85);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_93);
lean_ctor_set(x_121, 1, x_120);
x_122 = 1;
x_123 = lean_usize_add(x_3, x_122);
x_3 = x_123;
x_4 = x_121;
x_9 = x_119;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_array_get_size(x_2);
x_14 = l_Array_toSubarray___rarg(x_2, x_1, x_13);
x_15 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(x_14, x_18, x_20, x_16, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__3___rarg(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_getForbiddenByTrivialSizeOf___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Array_contains___at___private_Lean_Meta_FunInfo_0__Lean_Meta_collectDeps_visit___spec__2(x_7, x_3);
lean_dec(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_isForbidden___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_7, x_6);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_5, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_9);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_5, x_15);
lean_dec(x_5);
x_17 = l_Lean_Elab_WF_generateCombinations_x3f_isForbidden(x_1, x_4, x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_nat_add(x_4, x_15);
lean_inc(x_6);
lean_inc(x_10);
x_19 = lean_array_push(x_10, x_6);
x_20 = l_Lean_Elab_WF_generateCombinations_x3f_go(x_1, x_2, x_3, x_18, x_19, x_11);
lean_dec(x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_30 = lean_box(0);
x_5 = x_16;
x_6 = x_29;
x_9 = x_30;
x_11 = x_28;
goto _start;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_33 = lean_box(0);
x_5 = x_16;
x_6 = x_32;
x_9 = x_33;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_9);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_9);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_11);
return x_38;
}
}
}
static lean_object* _init_l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_push(x_6, x_5);
x_10 = lean_array_get_size(x_9);
x_11 = lean_nat_dec_lt(x_3, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_2, x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_box(0);
lean_inc(x_16);
x_20 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(x_1, x_2, x_3, x_4, x_16, x_17, x_16, x_18, x_19, x_5, x_6);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_21);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_20, 0);
lean_dec(x_29);
x_30 = l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_dec(x_20);
x_32 = l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_generateCombinations_x3f_go___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_WF_generateCombinations_x3f_go(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_6 = l_Lean_Elab_WF_generateCombinations_x3f_go(x_1, x_2, x_3, x_4, x_5, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_generateCombinations_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_WF_generateCombinations_x3f(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Meta_getMVarType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_2, 3);
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
x_21 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_19, x_20, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Meta_assignExprMVar(x_1, x_22, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = !lean_is_exclusive(x_5);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_16, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_17);
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
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_28 = lean_ctor_get(x_16, 2);
lean_dec(x_28);
x_29 = lean_ctor_get(x_16, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_31 = lean_array_fget(x_22, x_23);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_23, x_32);
lean_dec(x_23);
lean_ctor_set(x_16, 1, x_33);
x_34 = lean_ctor_get(x_20, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_20, 2);
lean_inc(x_36);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_12);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_20, 2);
lean_dec(x_40);
x_41 = lean_ctor_get(x_20, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_20, 0);
lean_dec(x_42);
x_43 = lean_array_fget(x_34, x_35);
x_44 = lean_nat_add(x_35, x_32);
lean_dec(x_35);
lean_ctor_set(x_20, 1, x_44);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_43);
lean_inc(x_1);
x_45 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_31, x_1, x_18, x_17, x_43, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_46);
x_48 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_48, 0, x_46);
lean_closure_set(x_48, 1, x_43);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_46, x_48, x_6, x_7, x_8, x_9, x_10, x_11, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; size_t x_51; size_t x_52; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = 1;
x_52 = lean_usize_add(x_4, x_51);
x_4 = x_52;
x_12 = x_50;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_20);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
uint8_t x_58; 
lean_dec(x_20);
lean_dec(x_43);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
return x_45;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_45, 0);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_45);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_20);
x_62 = lean_array_fget(x_34, x_35);
x_63 = lean_nat_add(x_35, x_32);
lean_dec(x_35);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_34);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_36);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_62);
lean_inc(x_1);
x_65 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_31, x_1, x_18, x_17, x_62, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_66);
x_68 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_68, 0, x_66);
lean_closure_set(x_68, 1, x_62);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_69 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_66, x_68, x_6, x_7, x_8, x_9, x_10, x_11, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; size_t x_71; size_t x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
lean_ctor_set(x_5, 0, x_64);
x_71 = 1;
x_72 = lean_usize_add(x_4, x_71);
x_4 = x_72;
x_12 = x_70;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_64);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_78 = lean_ctor_get(x_65, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_80 = x_65;
} else {
 lean_dec_ref(x_65);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_16);
x_82 = lean_array_fget(x_22, x_23);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_add(x_23, x_83);
lean_dec(x_23);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_22);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_24);
x_86 = lean_ctor_get(x_20, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_20, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_20, 2);
lean_inc(x_88);
x_89 = lean_nat_dec_lt(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_85);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_5);
lean_ctor_set(x_90, 1, x_12);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 x_91 = x_20;
} else {
 lean_dec_ref(x_20);
 x_91 = lean_box(0);
}
x_92 = lean_array_fget(x_86, x_87);
x_93 = lean_nat_add(x_87, x_83);
lean_dec(x_87);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(0, 3, 0);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_86);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_88);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_92);
lean_inc(x_1);
x_95 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_82, x_1, x_18, x_17, x_92, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
lean_inc(x_96);
x_98 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_98, 0, x_96);
lean_closure_set(x_98, 1, x_92);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_99 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_96, x_98, x_6, x_7, x_8, x_9, x_10, x_11, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; size_t x_101; size_t x_102; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_ctor_set(x_5, 1, x_85);
lean_ctor_set(x_5, 0, x_94);
x_101 = 1;
x_102 = lean_usize_add(x_4, x_101);
x_4 = x_102;
x_12 = x_100;
goto _start;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_94);
lean_dec(x_85);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_106 = x_99;
} else {
 lean_dec_ref(x_99);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_85);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_108 = lean_ctor_get(x_95, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_110 = x_95;
} else {
 lean_dec_ref(x_95);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_5, 0);
lean_inc(x_112);
lean_dec(x_5);
x_113 = lean_ctor_get(x_16, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_16, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_16, 2);
lean_inc(x_115);
x_116 = lean_nat_dec_lt(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_16);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_12);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 lean_ctor_release(x_16, 2);
 x_119 = x_16;
} else {
 lean_dec_ref(x_16);
 x_119 = lean_box(0);
}
x_120 = lean_array_fget(x_113, x_114);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_add(x_114, x_121);
lean_dec(x_114);
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(0, 3, 0);
} else {
 x_123 = x_119;
}
lean_ctor_set(x_123, 0, x_113);
lean_ctor_set(x_123, 1, x_122);
lean_ctor_set(x_123, 2, x_115);
x_124 = lean_ctor_get(x_112, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_112, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_112, 2);
lean_inc(x_126);
x_127 = lean_nat_dec_lt(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_120);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_112);
lean_ctor_set(x_128, 1, x_123);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_12);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 lean_ctor_release(x_112, 2);
 x_130 = x_112;
} else {
 lean_dec_ref(x_112);
 x_130 = lean_box(0);
}
x_131 = lean_array_fget(x_124, x_125);
x_132 = lean_nat_add(x_125, x_121);
lean_dec(x_125);
if (lean_is_scalar(x_130)) {
 x_133 = lean_alloc_ctor(0, 3, 0);
} else {
 x_133 = x_130;
}
lean_ctor_set(x_133, 0, x_124);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_126);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_131);
lean_inc(x_1);
x_134 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary(x_120, x_1, x_18, x_17, x_131, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
lean_inc(x_135);
x_137 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___lambda__1), 9, 2);
lean_closure_set(x_137, 0, x_135);
lean_closure_set(x_137, 1, x_131);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_138 = l_Lean_Meta_withMVarContext___at_Lean_Elab_Term_logUnassignedUsingErrorInfos___spec__4___rarg(x_135, x_137, x_6, x_7, x_8, x_9, x_10, x_11, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; size_t x_141; size_t x_142; 
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_133);
lean_ctor_set(x_140, 1, x_123);
x_141 = 1;
x_142 = lean_usize_add(x_4, x_141);
x_4 = x_142;
x_5 = x_140;
x_12 = x_139;
goto _start;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_133);
lean_dec(x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_138, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_146 = x_138;
} else {
 lean_dec_ref(x_138);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_123);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_148 = lean_ctor_get(x_134, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_134, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_150 = x_134;
} else {
 lean_dec_ref(x_134);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invImage", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to apply 'invImage'", 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_11, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
lean_ctor_set(x_11, 3, x_16);
x_17 = lean_box(0);
lean_inc(x_9);
x_18 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_17, x_9, x_10, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_mvarId_x21(x_19);
lean_dec(x_19);
x_22 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_23 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_22, x_9, x_10, x_11, x_12, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_21);
x_27 = l_Lean_Meta_apply(x_21, x_24, x_26, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_31 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_35 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_39 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_27, 1);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_ctor_get(x_28, 0);
lean_inc(x_42);
lean_dec(x_28);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
x_44 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_45 = l_Lean_Meta_intro1Core(x_42, x_44, x_9, x_10, x_11, x_12, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_50 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(x_3, x_49, x_48, x_7, x_8, x_9, x_10, x_11, x_12, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_array_get_size(x_4);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Array_toSubarray___rarg(x_4, x_54, x_53);
x_56 = lean_array_get_size(x_3);
x_57 = l_Array_toSubarray___rarg(x_3, x_54, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_array_get_size(x_51);
x_60 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_61 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_62 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(x_5, x_51, x_60, x_61, x_58, x_7, x_8, x_9, x_10, x_11, x_12, x_52);
lean_dec(x_51);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_43);
x_64 = l_Lean_mkMVar(x_43);
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
x_72 = l_Lean_Meta_assignExprMVar(x_43, x_70, x_9, x_10, x_11, x_12, x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_mkMVar(x_21);
lean_inc(x_10);
x_75 = l_Lean_Meta_instantiateMVars(x_74, x_9, x_10, x_11, x_12, x_73);
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
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
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
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
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
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
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
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_91 = !lean_is_exclusive(x_50);
if (x_91 == 0)
{
return x_50;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_50, 0);
x_93 = lean_ctor_get(x_50, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_50);
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
lean_dec(x_43);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_45);
if (x_95 == 0)
{
return x_45;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_45, 0);
x_97 = lean_ctor_get(x_45, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_45);
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
lean_dec(x_40);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = lean_ctor_get(x_27, 1);
lean_inc(x_99);
lean_dec(x_27);
x_100 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_101 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(x_100, x_7, x_8, x_9, x_10, x_11, x_12, x_99);
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
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_27);
if (x_102 == 0)
{
return x_27;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_27, 0);
x_104 = lean_ctor_get(x_27, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_27);
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
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_23);
if (x_106 == 0)
{
return x_23;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_23, 0);
x_108 = lean_ctor_get(x_23, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_23);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_110 = lean_ctor_get(x_11, 0);
x_111 = lean_ctor_get(x_11, 1);
x_112 = lean_ctor_get(x_11, 2);
x_113 = lean_ctor_get(x_11, 3);
x_114 = lean_ctor_get(x_11, 4);
x_115 = lean_ctor_get(x_11, 5);
x_116 = lean_ctor_get(x_11, 6);
x_117 = lean_ctor_get(x_11, 7);
x_118 = lean_ctor_get(x_11, 8);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_11);
x_119 = l_Lean_replaceRef(x_1, x_113);
lean_dec(x_113);
lean_dec(x_1);
x_120 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_120, 0, x_110);
lean_ctor_set(x_120, 1, x_111);
lean_ctor_set(x_120, 2, x_112);
lean_ctor_set(x_120, 3, x_119);
lean_ctor_set(x_120, 4, x_114);
lean_ctor_set(x_120, 5, x_115);
lean_ctor_set(x_120, 6, x_116);
lean_ctor_set(x_120, 7, x_117);
lean_ctor_set(x_120, 8, x_118);
x_121 = lean_box(0);
lean_inc(x_9);
x_122 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_121, x_9, x_10, x_120, x_12, x_13);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_Expr_mvarId_x21(x_123);
lean_dec(x_123);
x_126 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2;
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
x_127 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_126, x_9, x_10, x_120, x_12, x_124);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_130 = 0;
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_125);
x_131 = l_Lean_Meta_apply(x_125, x_128, x_130, x_9, x_10, x_120, x_12, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_135 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(x_134, x_7, x_8, x_9, x_10, x_120, x_12, x_133);
lean_dec(x_12);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_135;
}
else
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
lean_dec(x_131);
x_138 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_139 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(x_138, x_7, x_8, x_9, x_10, x_120, x_12, x_137);
lean_dec(x_12);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_139;
}
else
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = lean_ctor_get(x_131, 1);
lean_inc(x_141);
lean_dec(x_131);
x_142 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_143 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(x_142, x_7, x_8, x_9, x_10, x_120, x_12, x_141);
lean_dec(x_12);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_143;
}
else
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_140, 1);
lean_inc(x_144);
lean_dec(x_140);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_131, 1);
lean_inc(x_145);
lean_dec(x_131);
x_146 = lean_ctor_get(x_132, 0);
lean_inc(x_146);
lean_dec(x_132);
x_147 = lean_ctor_get(x_136, 0);
lean_inc(x_147);
lean_dec(x_136);
x_148 = 0;
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
x_149 = l_Lean_Meta_intro1Core(x_146, x_148, x_9, x_10, x_120, x_12, x_145);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_154 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual(x_3, x_153, x_152, x_7, x_8, x_9, x_10, x_120, x_12, x_151);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; size_t x_164; size_t x_165; lean_object* x_166; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_array_get_size(x_4);
x_158 = lean_unsigned_to_nat(0u);
x_159 = l_Array_toSubarray___rarg(x_4, x_158, x_157);
x_160 = lean_array_get_size(x_3);
x_161 = l_Array_toSubarray___rarg(x_3, x_158, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_array_get_size(x_155);
x_164 = lean_usize_of_nat(x_163);
lean_dec(x_163);
x_165 = 0;
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_166 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(x_5, x_155, x_164, x_165, x_162, x_7, x_8, x_9, x_10, x_120, x_12, x_156);
lean_dec(x_155);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
lean_inc(x_147);
x_168 = l_Lean_mkMVar(x_147);
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
x_169 = lean_infer_type(x_168, x_9, x_10, x_120, x_12, x_167);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = lean_box(0);
lean_inc(x_12);
lean_inc(x_120);
lean_inc(x_10);
lean_inc(x_9);
x_173 = l_Lean_Meta_synthInstance(x_170, x_172, x_9, x_10, x_120, x_12, x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = l_Lean_Meta_assignExprMVar(x_147, x_174, x_9, x_10, x_120, x_12, x_175);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l_Lean_mkMVar(x_125);
lean_inc(x_10);
x_179 = l_Lean_Meta_instantiateMVars(x_178, x_9, x_10, x_120, x_12, x_177);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_apply_8(x_6, x_180, x_7, x_8, x_9, x_10, x_120, x_12, x_181);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_147);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_183 = lean_ctor_get(x_173, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_173, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_185 = x_173;
} else {
 lean_dec_ref(x_173);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_147);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_187 = lean_ctor_get(x_169, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_169, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_189 = x_169;
} else {
 lean_dec_ref(x_169);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_147);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_191 = lean_ctor_get(x_166, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_166, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_193 = x_166;
} else {
 lean_dec_ref(x_166);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_147);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_195 = lean_ctor_get(x_154, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_154, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_197 = x_154;
} else {
 lean_dec_ref(x_154);
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
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_147);
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_199 = lean_ctor_get(x_149, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_149, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_201 = x_149;
} else {
 lean_dec_ref(x_149);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_144);
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_125);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_203 = lean_ctor_get(x_131, 1);
lean_inc(x_203);
lean_dec(x_131);
x_204 = l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4;
x_205 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(x_204, x_7, x_8, x_9, x_10, x_120, x_12, x_203);
lean_dec(x_12);
lean_dec(x_120);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_205;
}
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_206 = lean_ctor_get(x_131, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_131, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_208 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_125);
lean_dec(x_120);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_210 = lean_ctor_get(x_127, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_127, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_212 = x_127;
} else {
 lean_dec_ref(x_127);
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems(x_6);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1), 13, 6);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_1);
lean_closure_set(x_15, 3, x_6);
lean_closure_set(x_15, 4, x_3);
lean_closure_set(x_15, 5, x_4);
x_16 = l_Lean_Elab_Term_withDeclName___rarg(x_2, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_go___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_go___spec__4(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_go___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_4, x_3);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_2, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
lean_inc(x_1);
x_19 = lean_array_push(x_6, x_1);
x_20 = lean_nat_add(x_3, x_5);
lean_dec(x_3);
x_2 = x_18;
x_3 = x_20;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
}
else
{
lean_object* x_23; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_13);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 3);
x_17 = 0;
lean_inc(x_16);
lean_inc(x_15);
x_18 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_2);
lean_ctor_set(x_18, 3, x_7);
lean_ctor_set_uint8(x_18, sizeof(void*)*4, x_17);
x_19 = lean_array_push(x_6, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_20);
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
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("paren", 5);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("tupleTail", 9);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, size_t x_12, size_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_13, x_12);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_24 = lean_array_uget(x_11, x_13);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = !lean_is_exclusive(x_14);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_14, 0);
x_39 = lean_ctor_get(x_14, 1);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_35, 1);
x_45 = lean_ctor_get(x_35, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_36, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_36, 2);
lean_inc(x_48);
x_49 = lean_nat_dec_lt(x_46, x_47);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_24);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_14);
x_25 = x_50;
x_26 = x_21;
goto block_33;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_36);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_ctor_get(x_36, 2);
lean_dec(x_52);
x_53 = lean_ctor_get(x_36, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_36, 0);
lean_dec(x_54);
x_55 = lean_nat_add(x_46, x_48);
lean_ctor_set(x_36, 0, x_55);
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_41, 2);
lean_inc(x_58);
x_59 = lean_nat_dec_lt(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_46);
lean_dec(x_24);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_14);
x_25 = x_60;
x_26 = x_21;
goto block_33;
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_41);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_62 = lean_ctor_get(x_41, 2);
lean_dec(x_62);
x_63 = lean_ctor_get(x_41, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_41, 0);
lean_dec(x_64);
x_65 = lean_array_fget(x_56, x_57);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_57, x_66);
lean_dec(x_57);
lean_ctor_set(x_41, 1, x_67);
x_68 = lean_ctor_get(x_38, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_38, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_38, 2);
lean_inc(x_70);
x_71 = lean_nat_dec_lt(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_46);
lean_dec(x_24);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_14);
x_25 = x_72;
x_26 = x_21;
goto block_33;
}
else
{
uint8_t x_73; 
lean_free_object(x_35);
lean_free_object(x_34);
lean_free_object(x_14);
x_73 = !lean_is_exclusive(x_38);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_74 = lean_ctor_get(x_38, 2);
lean_dec(x_74);
x_75 = lean_ctor_get(x_38, 1);
lean_dec(x_75);
x_76 = lean_ctor_get(x_38, 0);
lean_dec(x_76);
x_77 = lean_array_fget(x_68, x_69);
x_78 = lean_nat_add(x_69, x_66);
lean_dec(x_69);
lean_ctor_set(x_38, 1, x_78);
lean_inc(x_6);
lean_inc(x_8);
x_79 = lean_array_push(x_8, x_6);
x_80 = lean_nat_sub(x_77, x_65);
lean_dec(x_65);
lean_dec(x_77);
x_81 = lean_nat_sub(x_80, x_66);
lean_dec(x_80);
x_82 = lean_unsigned_to_nat(0u);
lean_inc(x_81);
lean_inc(x_9);
x_83 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_81, x_82, x_81, x_66, x_79, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_81);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_nat_dec_lt(x_66, x_10);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_46);
lean_inc(x_19);
x_87 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_85);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_19, 8);
lean_inc(x_90);
x_91 = lean_st_ref_get(x_20, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_environment_main_module(x_94);
x_96 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_97 = lean_name_mk_string(x_7, x_96);
x_98 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_99 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_2);
lean_ctor_set(x_100, 2, x_99);
x_101 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_90);
lean_inc(x_95);
x_102 = l_Lean_addMacroScope(x_95, x_101, x_90);
x_103 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_5);
lean_inc(x_88);
x_105 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_105, 0, x_88);
lean_ctor_set(x_105, 1, x_100);
lean_ctor_set(x_105, 2, x_102);
lean_ctor_set(x_105, 3, x_104);
lean_inc(x_4);
x_106 = l_Lean_addMacroScope(x_95, x_4, x_90);
lean_inc(x_5);
lean_inc(x_3);
x_107 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_107, 0, x_88);
lean_ctor_set(x_107, 1, x_3);
lean_ctor_set(x_107, 2, x_106);
lean_ctor_set(x_107, 3, x_5);
lean_inc(x_8);
x_108 = lean_array_push(x_8, x_107);
x_109 = lean_box(2);
x_110 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_108);
x_112 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_113 = lean_array_push(x_112, x_105);
x_114 = lean_array_push(x_113, x_111);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_97);
lean_ctor_set(x_115, 2, x_114);
x_116 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_84, x_36, x_41, x_38, x_44, x_115, x_15, x_16, x_17, x_18, x_19, x_20, x_93);
lean_dec(x_24);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_25 = x_117;
x_26 = x_118;
goto block_33;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_inc(x_19);
x_119 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_85);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_19, 8);
lean_inc(x_122);
x_123 = lean_st_ref_get(x_20, x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_environment_main_module(x_126);
x_128 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_129 = lean_name_mk_string(x_7, x_128);
x_130 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_120);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_120);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_133 = lean_name_mk_string(x_7, x_132);
x_134 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_135 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_2);
lean_ctor_set(x_136, 2, x_135);
x_137 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_122);
lean_inc(x_127);
x_138 = l_Lean_addMacroScope(x_127, x_137, x_122);
x_139 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_5);
lean_inc(x_120);
x_141 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_141, 0, x_120);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_138);
lean_ctor_set(x_141, 3, x_140);
lean_inc(x_4);
x_142 = l_Lean_addMacroScope(x_127, x_4, x_122);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_120);
x_143 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_143, 0, x_120);
lean_ctor_set(x_143, 1, x_3);
lean_ctor_set(x_143, 2, x_142);
lean_ctor_set(x_143, 3, x_5);
lean_inc(x_8);
x_144 = lean_array_push(x_8, x_143);
x_145 = lean_box(2);
x_146 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_147 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_144);
x_148 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_149 = lean_array_push(x_148, x_141);
x_150 = lean_array_push(x_149, x_147);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_133);
lean_ctor_set(x_151, 2, x_150);
x_152 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_153 = lean_name_mk_string(x_7, x_152);
x_154 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_120);
x_155 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_155, 0, x_120);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Nat_repr(x_46);
x_157 = l_Lean_numLitKind;
x_158 = l_Lean_Syntax_mkLit(x_157, x_156, x_145);
lean_inc(x_8);
x_159 = lean_array_push(x_8, x_158);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_145);
lean_ctor_set(x_160, 1, x_146);
lean_ctor_set(x_160, 2, x_159);
x_161 = lean_array_push(x_148, x_155);
x_162 = lean_array_push(x_161, x_160);
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_145);
lean_ctor_set(x_163, 1, x_153);
lean_ctor_set(x_163, 2, x_162);
lean_inc(x_8);
x_164 = lean_array_push(x_8, x_163);
x_165 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_165, 0, x_145);
lean_ctor_set(x_165, 1, x_146);
lean_ctor_set(x_165, 2, x_164);
x_166 = lean_array_push(x_148, x_151);
x_167 = lean_array_push(x_166, x_165);
x_168 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_168, 0, x_145);
lean_ctor_set(x_168, 1, x_146);
lean_ctor_set(x_168, 2, x_167);
x_169 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_170 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_170, 0, x_120);
lean_ctor_set(x_170, 1, x_169);
x_171 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_172 = lean_array_push(x_171, x_131);
x_173 = lean_array_push(x_172, x_168);
x_174 = lean_array_push(x_173, x_170);
x_175 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_175, 0, x_145);
lean_ctor_set(x_175, 1, x_129);
lean_ctor_set(x_175, 2, x_174);
x_176 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_84, x_36, x_41, x_38, x_44, x_175, x_15, x_16, x_17, x_18, x_19, x_20, x_125);
lean_dec(x_24);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_25 = x_177;
x_26 = x_178;
goto block_33;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
lean_dec(x_38);
x_179 = lean_array_fget(x_68, x_69);
x_180 = lean_nat_add(x_69, x_66);
lean_dec(x_69);
x_181 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_181, 0, x_68);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_181, 2, x_70);
lean_inc(x_6);
lean_inc(x_8);
x_182 = lean_array_push(x_8, x_6);
x_183 = lean_nat_sub(x_179, x_65);
lean_dec(x_65);
lean_dec(x_179);
x_184 = lean_nat_sub(x_183, x_66);
lean_dec(x_183);
x_185 = lean_unsigned_to_nat(0u);
lean_inc(x_184);
lean_inc(x_9);
x_186 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_184, x_185, x_184, x_66, x_182, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_184);
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = lean_nat_dec_lt(x_66, x_10);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_46);
lean_inc(x_19);
x_190 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_188);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_19, 8);
lean_inc(x_193);
x_194 = lean_st_ref_get(x_20, x_192);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_environment_main_module(x_197);
x_199 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_200 = lean_name_mk_string(x_7, x_199);
x_201 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_202 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_203 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_2);
lean_ctor_set(x_203, 2, x_202);
x_204 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_193);
lean_inc(x_198);
x_205 = l_Lean_addMacroScope(x_198, x_204, x_193);
x_206 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_5);
lean_inc(x_191);
x_208 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_208, 0, x_191);
lean_ctor_set(x_208, 1, x_203);
lean_ctor_set(x_208, 2, x_205);
lean_ctor_set(x_208, 3, x_207);
lean_inc(x_4);
x_209 = l_Lean_addMacroScope(x_198, x_4, x_193);
lean_inc(x_5);
lean_inc(x_3);
x_210 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_210, 0, x_191);
lean_ctor_set(x_210, 1, x_3);
lean_ctor_set(x_210, 2, x_209);
lean_ctor_set(x_210, 3, x_5);
lean_inc(x_8);
x_211 = lean_array_push(x_8, x_210);
x_212 = lean_box(2);
x_213 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_214 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_214, 2, x_211);
x_215 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_216 = lean_array_push(x_215, x_208);
x_217 = lean_array_push(x_216, x_214);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_212);
lean_ctor_set(x_218, 1, x_200);
lean_ctor_set(x_218, 2, x_217);
x_219 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_187, x_36, x_41, x_181, x_44, x_218, x_15, x_16, x_17, x_18, x_19, x_20, x_196);
lean_dec(x_24);
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_25 = x_220;
x_26 = x_221;
goto block_33;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_inc(x_19);
x_222 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_188);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_ctor_get(x_19, 8);
lean_inc(x_225);
x_226 = lean_st_ref_get(x_20, x_224);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_environment_main_module(x_229);
x_231 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_232 = lean_name_mk_string(x_7, x_231);
x_233 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_223);
x_234 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_234, 0, x_223);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_236 = lean_name_mk_string(x_7, x_235);
x_237 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_238 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_239 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_2);
lean_ctor_set(x_239, 2, x_238);
x_240 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_225);
lean_inc(x_230);
x_241 = l_Lean_addMacroScope(x_230, x_240, x_225);
x_242 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_5);
lean_inc(x_223);
x_244 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_244, 0, x_223);
lean_ctor_set(x_244, 1, x_239);
lean_ctor_set(x_244, 2, x_241);
lean_ctor_set(x_244, 3, x_243);
lean_inc(x_4);
x_245 = l_Lean_addMacroScope(x_230, x_4, x_225);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_223);
x_246 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_246, 0, x_223);
lean_ctor_set(x_246, 1, x_3);
lean_ctor_set(x_246, 2, x_245);
lean_ctor_set(x_246, 3, x_5);
lean_inc(x_8);
x_247 = lean_array_push(x_8, x_246);
x_248 = lean_box(2);
x_249 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_250 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set(x_250, 2, x_247);
x_251 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_252 = lean_array_push(x_251, x_244);
x_253 = lean_array_push(x_252, x_250);
x_254 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_254, 0, x_248);
lean_ctor_set(x_254, 1, x_236);
lean_ctor_set(x_254, 2, x_253);
x_255 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_256 = lean_name_mk_string(x_7, x_255);
x_257 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_223);
x_258 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_258, 0, x_223);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Nat_repr(x_46);
x_260 = l_Lean_numLitKind;
x_261 = l_Lean_Syntax_mkLit(x_260, x_259, x_248);
lean_inc(x_8);
x_262 = lean_array_push(x_8, x_261);
x_263 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_263, 0, x_248);
lean_ctor_set(x_263, 1, x_249);
lean_ctor_set(x_263, 2, x_262);
x_264 = lean_array_push(x_251, x_258);
x_265 = lean_array_push(x_264, x_263);
x_266 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_266, 0, x_248);
lean_ctor_set(x_266, 1, x_256);
lean_ctor_set(x_266, 2, x_265);
lean_inc(x_8);
x_267 = lean_array_push(x_8, x_266);
x_268 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_268, 0, x_248);
lean_ctor_set(x_268, 1, x_249);
lean_ctor_set(x_268, 2, x_267);
x_269 = lean_array_push(x_251, x_254);
x_270 = lean_array_push(x_269, x_268);
x_271 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_271, 0, x_248);
lean_ctor_set(x_271, 1, x_249);
lean_ctor_set(x_271, 2, x_270);
x_272 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_273 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_273, 0, x_223);
lean_ctor_set(x_273, 1, x_272);
x_274 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_275 = lean_array_push(x_274, x_234);
x_276 = lean_array_push(x_275, x_271);
x_277 = lean_array_push(x_276, x_273);
x_278 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_278, 0, x_248);
lean_ctor_set(x_278, 1, x_232);
lean_ctor_set(x_278, 2, x_277);
x_279 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_187, x_36, x_41, x_181, x_44, x_278, x_15, x_16, x_17, x_18, x_19, x_20, x_228);
lean_dec(x_24);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_25 = x_280;
x_26 = x_281;
goto block_33;
}
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
lean_dec(x_41);
x_282 = lean_array_fget(x_56, x_57);
x_283 = lean_unsigned_to_nat(1u);
x_284 = lean_nat_add(x_57, x_283);
lean_dec(x_57);
x_285 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_285, 0, x_56);
lean_ctor_set(x_285, 1, x_284);
lean_ctor_set(x_285, 2, x_58);
x_286 = lean_ctor_get(x_38, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_38, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_38, 2);
lean_inc(x_288);
x_289 = lean_nat_dec_lt(x_287, x_288);
if (x_289 == 0)
{
lean_object* x_290; 
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_282);
lean_dec(x_46);
lean_dec(x_24);
lean_ctor_set(x_34, 0, x_285);
x_290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_290, 0, x_14);
x_25 = x_290;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
lean_free_object(x_35);
lean_free_object(x_34);
lean_free_object(x_14);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_291 = x_38;
} else {
 lean_dec_ref(x_38);
 x_291 = lean_box(0);
}
x_292 = lean_array_fget(x_286, x_287);
x_293 = lean_nat_add(x_287, x_283);
lean_dec(x_287);
if (lean_is_scalar(x_291)) {
 x_294 = lean_alloc_ctor(0, 3, 0);
} else {
 x_294 = x_291;
}
lean_ctor_set(x_294, 0, x_286);
lean_ctor_set(x_294, 1, x_293);
lean_ctor_set(x_294, 2, x_288);
lean_inc(x_6);
lean_inc(x_8);
x_295 = lean_array_push(x_8, x_6);
x_296 = lean_nat_sub(x_292, x_282);
lean_dec(x_282);
lean_dec(x_292);
x_297 = lean_nat_sub(x_296, x_283);
lean_dec(x_296);
x_298 = lean_unsigned_to_nat(0u);
lean_inc(x_297);
lean_inc(x_9);
x_299 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_297, x_298, x_297, x_283, x_295, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_297);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_nat_dec_lt(x_283, x_10);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_46);
lean_inc(x_19);
x_303 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_301);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = lean_ctor_get(x_19, 8);
lean_inc(x_306);
x_307 = lean_st_ref_get(x_20, x_305);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_environment_main_module(x_310);
x_312 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_313 = lean_name_mk_string(x_7, x_312);
x_314 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_315 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_316 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_2);
lean_ctor_set(x_316, 2, x_315);
x_317 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_306);
lean_inc(x_311);
x_318 = l_Lean_addMacroScope(x_311, x_317, x_306);
x_319 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_5);
lean_inc(x_304);
x_321 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_321, 0, x_304);
lean_ctor_set(x_321, 1, x_316);
lean_ctor_set(x_321, 2, x_318);
lean_ctor_set(x_321, 3, x_320);
lean_inc(x_4);
x_322 = l_Lean_addMacroScope(x_311, x_4, x_306);
lean_inc(x_5);
lean_inc(x_3);
x_323 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_323, 0, x_304);
lean_ctor_set(x_323, 1, x_3);
lean_ctor_set(x_323, 2, x_322);
lean_ctor_set(x_323, 3, x_5);
lean_inc(x_8);
x_324 = lean_array_push(x_8, x_323);
x_325 = lean_box(2);
x_326 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_327 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
lean_ctor_set(x_327, 2, x_324);
x_328 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_329 = lean_array_push(x_328, x_321);
x_330 = lean_array_push(x_329, x_327);
x_331 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_331, 0, x_325);
lean_ctor_set(x_331, 1, x_313);
lean_ctor_set(x_331, 2, x_330);
x_332 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_300, x_36, x_285, x_294, x_44, x_331, x_15, x_16, x_17, x_18, x_19, x_20, x_309);
lean_dec(x_24);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_25 = x_333;
x_26 = x_334;
goto block_33;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_inc(x_19);
x_335 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_301);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = lean_ctor_get(x_19, 8);
lean_inc(x_338);
x_339 = lean_st_ref_get(x_20, x_337);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_339, 1);
lean_inc(x_341);
lean_dec(x_339);
x_342 = lean_ctor_get(x_340, 0);
lean_inc(x_342);
lean_dec(x_340);
x_343 = lean_environment_main_module(x_342);
x_344 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_345 = lean_name_mk_string(x_7, x_344);
x_346 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_336);
x_347 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_347, 0, x_336);
lean_ctor_set(x_347, 1, x_346);
x_348 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_349 = lean_name_mk_string(x_7, x_348);
x_350 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_351 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_352 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_2);
lean_ctor_set(x_352, 2, x_351);
x_353 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_338);
lean_inc(x_343);
x_354 = l_Lean_addMacroScope(x_343, x_353, x_338);
x_355 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_5);
lean_inc(x_336);
x_357 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_357, 0, x_336);
lean_ctor_set(x_357, 1, x_352);
lean_ctor_set(x_357, 2, x_354);
lean_ctor_set(x_357, 3, x_356);
lean_inc(x_4);
x_358 = l_Lean_addMacroScope(x_343, x_4, x_338);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_336);
x_359 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_359, 0, x_336);
lean_ctor_set(x_359, 1, x_3);
lean_ctor_set(x_359, 2, x_358);
lean_ctor_set(x_359, 3, x_5);
lean_inc(x_8);
x_360 = lean_array_push(x_8, x_359);
x_361 = lean_box(2);
x_362 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_363 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
lean_ctor_set(x_363, 2, x_360);
x_364 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_365 = lean_array_push(x_364, x_357);
x_366 = lean_array_push(x_365, x_363);
x_367 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_367, 0, x_361);
lean_ctor_set(x_367, 1, x_349);
lean_ctor_set(x_367, 2, x_366);
x_368 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_369 = lean_name_mk_string(x_7, x_368);
x_370 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_336);
x_371 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_371, 0, x_336);
lean_ctor_set(x_371, 1, x_370);
x_372 = l_Nat_repr(x_46);
x_373 = l_Lean_numLitKind;
x_374 = l_Lean_Syntax_mkLit(x_373, x_372, x_361);
lean_inc(x_8);
x_375 = lean_array_push(x_8, x_374);
x_376 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_376, 0, x_361);
lean_ctor_set(x_376, 1, x_362);
lean_ctor_set(x_376, 2, x_375);
x_377 = lean_array_push(x_364, x_371);
x_378 = lean_array_push(x_377, x_376);
x_379 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_379, 0, x_361);
lean_ctor_set(x_379, 1, x_369);
lean_ctor_set(x_379, 2, x_378);
lean_inc(x_8);
x_380 = lean_array_push(x_8, x_379);
x_381 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_381, 0, x_361);
lean_ctor_set(x_381, 1, x_362);
lean_ctor_set(x_381, 2, x_380);
x_382 = lean_array_push(x_364, x_367);
x_383 = lean_array_push(x_382, x_381);
x_384 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_384, 0, x_361);
lean_ctor_set(x_384, 1, x_362);
lean_ctor_set(x_384, 2, x_383);
x_385 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_386 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_386, 0, x_336);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_388 = lean_array_push(x_387, x_347);
x_389 = lean_array_push(x_388, x_384);
x_390 = lean_array_push(x_389, x_386);
x_391 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_391, 0, x_361);
lean_ctor_set(x_391, 1, x_345);
lean_ctor_set(x_391, 2, x_390);
x_392 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_300, x_36, x_285, x_294, x_44, x_391, x_15, x_16, x_17, x_18, x_19, x_20, x_341);
lean_dec(x_24);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
x_25 = x_393;
x_26 = x_394;
goto block_33;
}
}
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
lean_dec(x_36);
x_395 = lean_nat_add(x_46, x_48);
x_396 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_47);
lean_ctor_set(x_396, 2, x_48);
x_397 = lean_ctor_get(x_41, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_41, 1);
lean_inc(x_398);
x_399 = lean_ctor_get(x_41, 2);
lean_inc(x_399);
x_400 = lean_nat_dec_lt(x_398, x_399);
if (x_400 == 0)
{
lean_object* x_401; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_46);
lean_dec(x_24);
lean_ctor_set(x_35, 0, x_396);
x_401 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_401, 0, x_14);
x_25 = x_401;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; 
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_402 = x_41;
} else {
 lean_dec_ref(x_41);
 x_402 = lean_box(0);
}
x_403 = lean_array_fget(x_397, x_398);
x_404 = lean_unsigned_to_nat(1u);
x_405 = lean_nat_add(x_398, x_404);
lean_dec(x_398);
if (lean_is_scalar(x_402)) {
 x_406 = lean_alloc_ctor(0, 3, 0);
} else {
 x_406 = x_402;
}
lean_ctor_set(x_406, 0, x_397);
lean_ctor_set(x_406, 1, x_405);
lean_ctor_set(x_406, 2, x_399);
x_407 = lean_ctor_get(x_38, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_38, 1);
lean_inc(x_408);
x_409 = lean_ctor_get(x_38, 2);
lean_inc(x_409);
x_410 = lean_nat_dec_lt(x_408, x_409);
if (x_410 == 0)
{
lean_object* x_411; 
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_403);
lean_dec(x_46);
lean_dec(x_24);
lean_ctor_set(x_35, 0, x_396);
lean_ctor_set(x_34, 0, x_406);
x_411 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_411, 0, x_14);
x_25 = x_411;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; 
lean_free_object(x_35);
lean_free_object(x_34);
lean_free_object(x_14);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_412 = x_38;
} else {
 lean_dec_ref(x_38);
 x_412 = lean_box(0);
}
x_413 = lean_array_fget(x_407, x_408);
x_414 = lean_nat_add(x_408, x_404);
lean_dec(x_408);
if (lean_is_scalar(x_412)) {
 x_415 = lean_alloc_ctor(0, 3, 0);
} else {
 x_415 = x_412;
}
lean_ctor_set(x_415, 0, x_407);
lean_ctor_set(x_415, 1, x_414);
lean_ctor_set(x_415, 2, x_409);
lean_inc(x_6);
lean_inc(x_8);
x_416 = lean_array_push(x_8, x_6);
x_417 = lean_nat_sub(x_413, x_403);
lean_dec(x_403);
lean_dec(x_413);
x_418 = lean_nat_sub(x_417, x_404);
lean_dec(x_417);
x_419 = lean_unsigned_to_nat(0u);
lean_inc(x_418);
lean_inc(x_9);
x_420 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_418, x_419, x_418, x_404, x_416, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_418);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_nat_dec_lt(x_404, x_10);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_46);
lean_inc(x_19);
x_424 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_422);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = lean_ctor_get(x_19, 8);
lean_inc(x_427);
x_428 = lean_st_ref_get(x_20, x_426);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_428, 1);
lean_inc(x_430);
lean_dec(x_428);
x_431 = lean_ctor_get(x_429, 0);
lean_inc(x_431);
lean_dec(x_429);
x_432 = lean_environment_main_module(x_431);
x_433 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_434 = lean_name_mk_string(x_7, x_433);
x_435 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_436 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_437 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_2);
lean_ctor_set(x_437, 2, x_436);
x_438 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_427);
lean_inc(x_432);
x_439 = l_Lean_addMacroScope(x_432, x_438, x_427);
x_440 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_5);
lean_inc(x_425);
x_442 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_442, 0, x_425);
lean_ctor_set(x_442, 1, x_437);
lean_ctor_set(x_442, 2, x_439);
lean_ctor_set(x_442, 3, x_441);
lean_inc(x_4);
x_443 = l_Lean_addMacroScope(x_432, x_4, x_427);
lean_inc(x_5);
lean_inc(x_3);
x_444 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_444, 0, x_425);
lean_ctor_set(x_444, 1, x_3);
lean_ctor_set(x_444, 2, x_443);
lean_ctor_set(x_444, 3, x_5);
lean_inc(x_8);
x_445 = lean_array_push(x_8, x_444);
x_446 = lean_box(2);
x_447 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_448 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set(x_448, 1, x_447);
lean_ctor_set(x_448, 2, x_445);
x_449 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_450 = lean_array_push(x_449, x_442);
x_451 = lean_array_push(x_450, x_448);
x_452 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_452, 0, x_446);
lean_ctor_set(x_452, 1, x_434);
lean_ctor_set(x_452, 2, x_451);
x_453 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_421, x_396, x_406, x_415, x_44, x_452, x_15, x_16, x_17, x_18, x_19, x_20, x_430);
lean_dec(x_24);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_25 = x_454;
x_26 = x_455;
goto block_33;
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_inc(x_19);
x_456 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_422);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_ctor_get(x_19, 8);
lean_inc(x_459);
x_460 = lean_st_ref_get(x_20, x_458);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
x_463 = lean_ctor_get(x_461, 0);
lean_inc(x_463);
lean_dec(x_461);
x_464 = lean_environment_main_module(x_463);
x_465 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_466 = lean_name_mk_string(x_7, x_465);
x_467 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_457);
x_468 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_468, 0, x_457);
lean_ctor_set(x_468, 1, x_467);
x_469 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_470 = lean_name_mk_string(x_7, x_469);
x_471 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_472 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_473 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_2);
lean_ctor_set(x_473, 2, x_472);
x_474 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_459);
lean_inc(x_464);
x_475 = l_Lean_addMacroScope(x_464, x_474, x_459);
x_476 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_5);
lean_inc(x_457);
x_478 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_478, 0, x_457);
lean_ctor_set(x_478, 1, x_473);
lean_ctor_set(x_478, 2, x_475);
lean_ctor_set(x_478, 3, x_477);
lean_inc(x_4);
x_479 = l_Lean_addMacroScope(x_464, x_4, x_459);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_457);
x_480 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_480, 0, x_457);
lean_ctor_set(x_480, 1, x_3);
lean_ctor_set(x_480, 2, x_479);
lean_ctor_set(x_480, 3, x_5);
lean_inc(x_8);
x_481 = lean_array_push(x_8, x_480);
x_482 = lean_box(2);
x_483 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_484 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
lean_ctor_set(x_484, 2, x_481);
x_485 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_486 = lean_array_push(x_485, x_478);
x_487 = lean_array_push(x_486, x_484);
x_488 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_488, 0, x_482);
lean_ctor_set(x_488, 1, x_470);
lean_ctor_set(x_488, 2, x_487);
x_489 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_490 = lean_name_mk_string(x_7, x_489);
x_491 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_457);
x_492 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_492, 0, x_457);
lean_ctor_set(x_492, 1, x_491);
x_493 = l_Nat_repr(x_46);
x_494 = l_Lean_numLitKind;
x_495 = l_Lean_Syntax_mkLit(x_494, x_493, x_482);
lean_inc(x_8);
x_496 = lean_array_push(x_8, x_495);
x_497 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_497, 0, x_482);
lean_ctor_set(x_497, 1, x_483);
lean_ctor_set(x_497, 2, x_496);
x_498 = lean_array_push(x_485, x_492);
x_499 = lean_array_push(x_498, x_497);
x_500 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_500, 0, x_482);
lean_ctor_set(x_500, 1, x_490);
lean_ctor_set(x_500, 2, x_499);
lean_inc(x_8);
x_501 = lean_array_push(x_8, x_500);
x_502 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_502, 0, x_482);
lean_ctor_set(x_502, 1, x_483);
lean_ctor_set(x_502, 2, x_501);
x_503 = lean_array_push(x_485, x_488);
x_504 = lean_array_push(x_503, x_502);
x_505 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_505, 0, x_482);
lean_ctor_set(x_505, 1, x_483);
lean_ctor_set(x_505, 2, x_504);
x_506 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_507 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_507, 0, x_457);
lean_ctor_set(x_507, 1, x_506);
x_508 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_509 = lean_array_push(x_508, x_468);
x_510 = lean_array_push(x_509, x_505);
x_511 = lean_array_push(x_510, x_507);
x_512 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_512, 0, x_482);
lean_ctor_set(x_512, 1, x_466);
lean_ctor_set(x_512, 2, x_511);
x_513 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_421, x_396, x_406, x_415, x_44, x_512, x_15, x_16, x_17, x_18, x_19, x_20, x_462);
lean_dec(x_24);
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_25 = x_514;
x_26 = x_515;
goto block_33;
}
}
}
}
}
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; 
x_516 = lean_ctor_get(x_35, 1);
lean_inc(x_516);
lean_dec(x_35);
x_517 = lean_ctor_get(x_36, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_36, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_36, 2);
lean_inc(x_519);
x_520 = lean_nat_dec_lt(x_517, x_518);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; 
lean_dec(x_519);
lean_dec(x_518);
lean_dec(x_517);
lean_dec(x_24);
x_521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_521, 0, x_36);
lean_ctor_set(x_521, 1, x_516);
lean_ctor_set(x_34, 1, x_521);
x_522 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_522, 0, x_14);
x_25 = x_522;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_529; 
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_523 = x_36;
} else {
 lean_dec_ref(x_36);
 x_523 = lean_box(0);
}
x_524 = lean_nat_add(x_517, x_519);
if (lean_is_scalar(x_523)) {
 x_525 = lean_alloc_ctor(0, 3, 0);
} else {
 x_525 = x_523;
}
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_518);
lean_ctor_set(x_525, 2, x_519);
x_526 = lean_ctor_get(x_41, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_41, 1);
lean_inc(x_527);
x_528 = lean_ctor_get(x_41, 2);
lean_inc(x_528);
x_529 = lean_nat_dec_lt(x_527, x_528);
if (x_529 == 0)
{
lean_object* x_530; lean_object* x_531; 
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_517);
lean_dec(x_24);
x_530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_530, 0, x_525);
lean_ctor_set(x_530, 1, x_516);
lean_ctor_set(x_34, 1, x_530);
x_531 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_531, 0, x_14);
x_25 = x_531;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint8_t x_540; 
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 x_532 = x_41;
} else {
 lean_dec_ref(x_41);
 x_532 = lean_box(0);
}
x_533 = lean_array_fget(x_526, x_527);
x_534 = lean_unsigned_to_nat(1u);
x_535 = lean_nat_add(x_527, x_534);
lean_dec(x_527);
if (lean_is_scalar(x_532)) {
 x_536 = lean_alloc_ctor(0, 3, 0);
} else {
 x_536 = x_532;
}
lean_ctor_set(x_536, 0, x_526);
lean_ctor_set(x_536, 1, x_535);
lean_ctor_set(x_536, 2, x_528);
x_537 = lean_ctor_get(x_38, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_38, 1);
lean_inc(x_538);
x_539 = lean_ctor_get(x_38, 2);
lean_inc(x_539);
x_540 = lean_nat_dec_lt(x_538, x_539);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; 
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_533);
lean_dec(x_517);
lean_dec(x_24);
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_525);
lean_ctor_set(x_541, 1, x_516);
lean_ctor_set(x_34, 1, x_541);
lean_ctor_set(x_34, 0, x_536);
x_542 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_542, 0, x_14);
x_25 = x_542;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; 
lean_free_object(x_34);
lean_free_object(x_14);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_543 = x_38;
} else {
 lean_dec_ref(x_38);
 x_543 = lean_box(0);
}
x_544 = lean_array_fget(x_537, x_538);
x_545 = lean_nat_add(x_538, x_534);
lean_dec(x_538);
if (lean_is_scalar(x_543)) {
 x_546 = lean_alloc_ctor(0, 3, 0);
} else {
 x_546 = x_543;
}
lean_ctor_set(x_546, 0, x_537);
lean_ctor_set(x_546, 1, x_545);
lean_ctor_set(x_546, 2, x_539);
lean_inc(x_6);
lean_inc(x_8);
x_547 = lean_array_push(x_8, x_6);
x_548 = lean_nat_sub(x_544, x_533);
lean_dec(x_533);
lean_dec(x_544);
x_549 = lean_nat_sub(x_548, x_534);
lean_dec(x_548);
x_550 = lean_unsigned_to_nat(0u);
lean_inc(x_549);
lean_inc(x_9);
x_551 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_549, x_550, x_549, x_534, x_547, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_549);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_554 = lean_nat_dec_lt(x_534, x_10);
if (x_554 == 0)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
lean_dec(x_517);
lean_inc(x_19);
x_555 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_553);
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = lean_ctor_get(x_19, 8);
lean_inc(x_558);
x_559 = lean_st_ref_get(x_20, x_557);
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_ctor_get(x_560, 0);
lean_inc(x_562);
lean_dec(x_560);
x_563 = lean_environment_main_module(x_562);
x_564 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_565 = lean_name_mk_string(x_7, x_564);
x_566 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_567 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_568 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_568, 0, x_566);
lean_ctor_set(x_568, 1, x_2);
lean_ctor_set(x_568, 2, x_567);
x_569 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_558);
lean_inc(x_563);
x_570 = l_Lean_addMacroScope(x_563, x_569, x_558);
x_571 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_572, 0, x_571);
lean_ctor_set(x_572, 1, x_5);
lean_inc(x_556);
x_573 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_573, 0, x_556);
lean_ctor_set(x_573, 1, x_568);
lean_ctor_set(x_573, 2, x_570);
lean_ctor_set(x_573, 3, x_572);
lean_inc(x_4);
x_574 = l_Lean_addMacroScope(x_563, x_4, x_558);
lean_inc(x_5);
lean_inc(x_3);
x_575 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_575, 0, x_556);
lean_ctor_set(x_575, 1, x_3);
lean_ctor_set(x_575, 2, x_574);
lean_ctor_set(x_575, 3, x_5);
lean_inc(x_8);
x_576 = lean_array_push(x_8, x_575);
x_577 = lean_box(2);
x_578 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_579 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_579, 0, x_577);
lean_ctor_set(x_579, 1, x_578);
lean_ctor_set(x_579, 2, x_576);
x_580 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_581 = lean_array_push(x_580, x_573);
x_582 = lean_array_push(x_581, x_579);
x_583 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_583, 0, x_577);
lean_ctor_set(x_583, 1, x_565);
lean_ctor_set(x_583, 2, x_582);
x_584 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_552, x_525, x_536, x_546, x_516, x_583, x_15, x_16, x_17, x_18, x_19, x_20, x_561);
lean_dec(x_24);
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
lean_dec(x_584);
x_25 = x_585;
x_26 = x_586;
goto block_33;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
lean_inc(x_19);
x_587 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_553);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
lean_dec(x_587);
x_590 = lean_ctor_get(x_19, 8);
lean_inc(x_590);
x_591 = lean_st_ref_get(x_20, x_589);
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
lean_dec(x_591);
x_594 = lean_ctor_get(x_592, 0);
lean_inc(x_594);
lean_dec(x_592);
x_595 = lean_environment_main_module(x_594);
x_596 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_597 = lean_name_mk_string(x_7, x_596);
x_598 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_588);
x_599 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_599, 0, x_588);
lean_ctor_set(x_599, 1, x_598);
x_600 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_601 = lean_name_mk_string(x_7, x_600);
x_602 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_603 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_604 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_2);
lean_ctor_set(x_604, 2, x_603);
x_605 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_590);
lean_inc(x_595);
x_606 = l_Lean_addMacroScope(x_595, x_605, x_590);
x_607 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set(x_608, 1, x_5);
lean_inc(x_588);
x_609 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_609, 0, x_588);
lean_ctor_set(x_609, 1, x_604);
lean_ctor_set(x_609, 2, x_606);
lean_ctor_set(x_609, 3, x_608);
lean_inc(x_4);
x_610 = l_Lean_addMacroScope(x_595, x_4, x_590);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_588);
x_611 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_611, 0, x_588);
lean_ctor_set(x_611, 1, x_3);
lean_ctor_set(x_611, 2, x_610);
lean_ctor_set(x_611, 3, x_5);
lean_inc(x_8);
x_612 = lean_array_push(x_8, x_611);
x_613 = lean_box(2);
x_614 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_615 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
lean_ctor_set(x_615, 2, x_612);
x_616 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_617 = lean_array_push(x_616, x_609);
x_618 = lean_array_push(x_617, x_615);
x_619 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_619, 0, x_613);
lean_ctor_set(x_619, 1, x_601);
lean_ctor_set(x_619, 2, x_618);
x_620 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_621 = lean_name_mk_string(x_7, x_620);
x_622 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_588);
x_623 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_623, 0, x_588);
lean_ctor_set(x_623, 1, x_622);
x_624 = l_Nat_repr(x_517);
x_625 = l_Lean_numLitKind;
x_626 = l_Lean_Syntax_mkLit(x_625, x_624, x_613);
lean_inc(x_8);
x_627 = lean_array_push(x_8, x_626);
x_628 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_628, 0, x_613);
lean_ctor_set(x_628, 1, x_614);
lean_ctor_set(x_628, 2, x_627);
x_629 = lean_array_push(x_616, x_623);
x_630 = lean_array_push(x_629, x_628);
x_631 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_631, 0, x_613);
lean_ctor_set(x_631, 1, x_621);
lean_ctor_set(x_631, 2, x_630);
lean_inc(x_8);
x_632 = lean_array_push(x_8, x_631);
x_633 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_633, 0, x_613);
lean_ctor_set(x_633, 1, x_614);
lean_ctor_set(x_633, 2, x_632);
x_634 = lean_array_push(x_616, x_619);
x_635 = lean_array_push(x_634, x_633);
x_636 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_636, 0, x_613);
lean_ctor_set(x_636, 1, x_614);
lean_ctor_set(x_636, 2, x_635);
x_637 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_638 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_638, 0, x_588);
lean_ctor_set(x_638, 1, x_637);
x_639 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_640 = lean_array_push(x_639, x_599);
x_641 = lean_array_push(x_640, x_636);
x_642 = lean_array_push(x_641, x_638);
x_643 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_643, 0, x_613);
lean_ctor_set(x_643, 1, x_597);
lean_ctor_set(x_643, 2, x_642);
x_644 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_552, x_525, x_536, x_546, x_516, x_643, x_15, x_16, x_17, x_18, x_19, x_20, x_593);
lean_dec(x_24);
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec(x_644);
x_25 = x_645;
x_26 = x_646;
goto block_33;
}
}
}
}
}
}
else
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; 
x_647 = lean_ctor_get(x_34, 0);
lean_inc(x_647);
lean_dec(x_34);
x_648 = lean_ctor_get(x_35, 1);
lean_inc(x_648);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_649 = x_35;
} else {
 lean_dec_ref(x_35);
 x_649 = lean_box(0);
}
x_650 = lean_ctor_get(x_36, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_36, 1);
lean_inc(x_651);
x_652 = lean_ctor_get(x_36, 2);
lean_inc(x_652);
x_653 = lean_nat_dec_lt(x_650, x_651);
if (x_653 == 0)
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_652);
lean_dec(x_651);
lean_dec(x_650);
lean_dec(x_24);
if (lean_is_scalar(x_649)) {
 x_654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_654 = x_649;
}
lean_ctor_set(x_654, 0, x_36);
lean_ctor_set(x_654, 1, x_648);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_647);
lean_ctor_set(x_655, 1, x_654);
lean_ctor_set(x_14, 1, x_655);
x_656 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_656, 0, x_14);
x_25 = x_656;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; uint8_t x_663; 
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_657 = x_36;
} else {
 lean_dec_ref(x_36);
 x_657 = lean_box(0);
}
x_658 = lean_nat_add(x_650, x_652);
if (lean_is_scalar(x_657)) {
 x_659 = lean_alloc_ctor(0, 3, 0);
} else {
 x_659 = x_657;
}
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_651);
lean_ctor_set(x_659, 2, x_652);
x_660 = lean_ctor_get(x_647, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_647, 1);
lean_inc(x_661);
x_662 = lean_ctor_get(x_647, 2);
lean_inc(x_662);
x_663 = lean_nat_dec_lt(x_661, x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; 
lean_dec(x_662);
lean_dec(x_661);
lean_dec(x_660);
lean_dec(x_650);
lean_dec(x_24);
if (lean_is_scalar(x_649)) {
 x_664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_664 = x_649;
}
lean_ctor_set(x_664, 0, x_659);
lean_ctor_set(x_664, 1, x_648);
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_647);
lean_ctor_set(x_665, 1, x_664);
lean_ctor_set(x_14, 1, x_665);
x_666 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_666, 0, x_14);
x_25 = x_666;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; uint8_t x_675; 
if (lean_is_exclusive(x_647)) {
 lean_ctor_release(x_647, 0);
 lean_ctor_release(x_647, 1);
 lean_ctor_release(x_647, 2);
 x_667 = x_647;
} else {
 lean_dec_ref(x_647);
 x_667 = lean_box(0);
}
x_668 = lean_array_fget(x_660, x_661);
x_669 = lean_unsigned_to_nat(1u);
x_670 = lean_nat_add(x_661, x_669);
lean_dec(x_661);
if (lean_is_scalar(x_667)) {
 x_671 = lean_alloc_ctor(0, 3, 0);
} else {
 x_671 = x_667;
}
lean_ctor_set(x_671, 0, x_660);
lean_ctor_set(x_671, 1, x_670);
lean_ctor_set(x_671, 2, x_662);
x_672 = lean_ctor_get(x_38, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_38, 1);
lean_inc(x_673);
x_674 = lean_ctor_get(x_38, 2);
lean_inc(x_674);
x_675 = lean_nat_dec_lt(x_673, x_674);
if (x_675 == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
lean_dec(x_674);
lean_dec(x_673);
lean_dec(x_672);
lean_dec(x_668);
lean_dec(x_650);
lean_dec(x_24);
if (lean_is_scalar(x_649)) {
 x_676 = lean_alloc_ctor(0, 2, 0);
} else {
 x_676 = x_649;
}
lean_ctor_set(x_676, 0, x_659);
lean_ctor_set(x_676, 1, x_648);
x_677 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_677, 0, x_671);
lean_ctor_set(x_677, 1, x_676);
lean_ctor_set(x_14, 1, x_677);
x_678 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_678, 0, x_14);
x_25 = x_678;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; uint8_t x_690; 
lean_dec(x_649);
lean_free_object(x_14);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 x_679 = x_38;
} else {
 lean_dec_ref(x_38);
 x_679 = lean_box(0);
}
x_680 = lean_array_fget(x_672, x_673);
x_681 = lean_nat_add(x_673, x_669);
lean_dec(x_673);
if (lean_is_scalar(x_679)) {
 x_682 = lean_alloc_ctor(0, 3, 0);
} else {
 x_682 = x_679;
}
lean_ctor_set(x_682, 0, x_672);
lean_ctor_set(x_682, 1, x_681);
lean_ctor_set(x_682, 2, x_674);
lean_inc(x_6);
lean_inc(x_8);
x_683 = lean_array_push(x_8, x_6);
x_684 = lean_nat_sub(x_680, x_668);
lean_dec(x_668);
lean_dec(x_680);
x_685 = lean_nat_sub(x_684, x_669);
lean_dec(x_684);
x_686 = lean_unsigned_to_nat(0u);
lean_inc(x_685);
lean_inc(x_9);
x_687 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_685, x_686, x_685, x_669, x_683, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_685);
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
lean_dec(x_687);
x_690 = lean_nat_dec_lt(x_669, x_10);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
lean_dec(x_650);
lean_inc(x_19);
x_691 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_689);
x_692 = lean_ctor_get(x_691, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_691, 1);
lean_inc(x_693);
lean_dec(x_691);
x_694 = lean_ctor_get(x_19, 8);
lean_inc(x_694);
x_695 = lean_st_ref_get(x_20, x_693);
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
x_698 = lean_ctor_get(x_696, 0);
lean_inc(x_698);
lean_dec(x_696);
x_699 = lean_environment_main_module(x_698);
x_700 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_701 = lean_name_mk_string(x_7, x_700);
x_702 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_703 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_704 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_2);
lean_ctor_set(x_704, 2, x_703);
x_705 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_694);
lean_inc(x_699);
x_706 = l_Lean_addMacroScope(x_699, x_705, x_694);
x_707 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_708 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_5);
lean_inc(x_692);
x_709 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_709, 0, x_692);
lean_ctor_set(x_709, 1, x_704);
lean_ctor_set(x_709, 2, x_706);
lean_ctor_set(x_709, 3, x_708);
lean_inc(x_4);
x_710 = l_Lean_addMacroScope(x_699, x_4, x_694);
lean_inc(x_5);
lean_inc(x_3);
x_711 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_711, 0, x_692);
lean_ctor_set(x_711, 1, x_3);
lean_ctor_set(x_711, 2, x_710);
lean_ctor_set(x_711, 3, x_5);
lean_inc(x_8);
x_712 = lean_array_push(x_8, x_711);
x_713 = lean_box(2);
x_714 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_715 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
lean_ctor_set(x_715, 2, x_712);
x_716 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_717 = lean_array_push(x_716, x_709);
x_718 = lean_array_push(x_717, x_715);
x_719 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_719, 0, x_713);
lean_ctor_set(x_719, 1, x_701);
lean_ctor_set(x_719, 2, x_718);
x_720 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_688, x_659, x_671, x_682, x_648, x_719, x_15, x_16, x_17, x_18, x_19, x_20, x_697);
lean_dec(x_24);
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
lean_dec(x_720);
x_25 = x_721;
x_26 = x_722;
goto block_33;
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
lean_inc(x_19);
x_723 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_689);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
x_726 = lean_ctor_get(x_19, 8);
lean_inc(x_726);
x_727 = lean_st_ref_get(x_20, x_725);
x_728 = lean_ctor_get(x_727, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_727, 1);
lean_inc(x_729);
lean_dec(x_727);
x_730 = lean_ctor_get(x_728, 0);
lean_inc(x_730);
lean_dec(x_728);
x_731 = lean_environment_main_module(x_730);
x_732 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_733 = lean_name_mk_string(x_7, x_732);
x_734 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_724);
x_735 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_735, 0, x_724);
lean_ctor_set(x_735, 1, x_734);
x_736 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_737 = lean_name_mk_string(x_7, x_736);
x_738 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_739 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_740 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_740, 0, x_738);
lean_ctor_set(x_740, 1, x_2);
lean_ctor_set(x_740, 2, x_739);
x_741 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_726);
lean_inc(x_731);
x_742 = l_Lean_addMacroScope(x_731, x_741, x_726);
x_743 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_744 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_744, 0, x_743);
lean_ctor_set(x_744, 1, x_5);
lean_inc(x_724);
x_745 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_745, 0, x_724);
lean_ctor_set(x_745, 1, x_740);
lean_ctor_set(x_745, 2, x_742);
lean_ctor_set(x_745, 3, x_744);
lean_inc(x_4);
x_746 = l_Lean_addMacroScope(x_731, x_4, x_726);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_724);
x_747 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_747, 0, x_724);
lean_ctor_set(x_747, 1, x_3);
lean_ctor_set(x_747, 2, x_746);
lean_ctor_set(x_747, 3, x_5);
lean_inc(x_8);
x_748 = lean_array_push(x_8, x_747);
x_749 = lean_box(2);
x_750 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_751 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
lean_ctor_set(x_751, 2, x_748);
x_752 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_753 = lean_array_push(x_752, x_745);
x_754 = lean_array_push(x_753, x_751);
x_755 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_755, 0, x_749);
lean_ctor_set(x_755, 1, x_737);
lean_ctor_set(x_755, 2, x_754);
x_756 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_757 = lean_name_mk_string(x_7, x_756);
x_758 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_724);
x_759 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_759, 0, x_724);
lean_ctor_set(x_759, 1, x_758);
x_760 = l_Nat_repr(x_650);
x_761 = l_Lean_numLitKind;
x_762 = l_Lean_Syntax_mkLit(x_761, x_760, x_749);
lean_inc(x_8);
x_763 = lean_array_push(x_8, x_762);
x_764 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_764, 0, x_749);
lean_ctor_set(x_764, 1, x_750);
lean_ctor_set(x_764, 2, x_763);
x_765 = lean_array_push(x_752, x_759);
x_766 = lean_array_push(x_765, x_764);
x_767 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_767, 0, x_749);
lean_ctor_set(x_767, 1, x_757);
lean_ctor_set(x_767, 2, x_766);
lean_inc(x_8);
x_768 = lean_array_push(x_8, x_767);
x_769 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_769, 0, x_749);
lean_ctor_set(x_769, 1, x_750);
lean_ctor_set(x_769, 2, x_768);
x_770 = lean_array_push(x_752, x_755);
x_771 = lean_array_push(x_770, x_769);
x_772 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_772, 0, x_749);
lean_ctor_set(x_772, 1, x_750);
lean_ctor_set(x_772, 2, x_771);
x_773 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_774 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_774, 0, x_724);
lean_ctor_set(x_774, 1, x_773);
x_775 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_776 = lean_array_push(x_775, x_735);
x_777 = lean_array_push(x_776, x_772);
x_778 = lean_array_push(x_777, x_774);
x_779 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_779, 0, x_749);
lean_ctor_set(x_779, 1, x_733);
lean_ctor_set(x_779, 2, x_778);
x_780 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_688, x_659, x_671, x_682, x_648, x_779, x_15, x_16, x_17, x_18, x_19, x_20, x_729);
lean_dec(x_24);
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
x_25 = x_781;
x_26 = x_782;
goto block_33;
}
}
}
}
}
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_783 = lean_ctor_get(x_14, 0);
lean_inc(x_783);
lean_dec(x_14);
x_784 = lean_ctor_get(x_34, 0);
lean_inc(x_784);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_785 = x_34;
} else {
 lean_dec_ref(x_34);
 x_785 = lean_box(0);
}
x_786 = lean_ctor_get(x_35, 1);
lean_inc(x_786);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_787 = x_35;
} else {
 lean_dec_ref(x_35);
 x_787 = lean_box(0);
}
x_788 = lean_ctor_get(x_36, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_36, 1);
lean_inc(x_789);
x_790 = lean_ctor_get(x_36, 2);
lean_inc(x_790);
x_791 = lean_nat_dec_lt(x_788, x_789);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
lean_dec(x_790);
lean_dec(x_789);
lean_dec(x_788);
lean_dec(x_24);
if (lean_is_scalar(x_787)) {
 x_792 = lean_alloc_ctor(0, 2, 0);
} else {
 x_792 = x_787;
}
lean_ctor_set(x_792, 0, x_36);
lean_ctor_set(x_792, 1, x_786);
if (lean_is_scalar(x_785)) {
 x_793 = lean_alloc_ctor(0, 2, 0);
} else {
 x_793 = x_785;
}
lean_ctor_set(x_793, 0, x_784);
lean_ctor_set(x_793, 1, x_792);
x_794 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_794, 0, x_783);
lean_ctor_set(x_794, 1, x_793);
x_795 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_795, 0, x_794);
x_25 = x_795;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; 
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_796 = x_36;
} else {
 lean_dec_ref(x_36);
 x_796 = lean_box(0);
}
x_797 = lean_nat_add(x_788, x_790);
if (lean_is_scalar(x_796)) {
 x_798 = lean_alloc_ctor(0, 3, 0);
} else {
 x_798 = x_796;
}
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_789);
lean_ctor_set(x_798, 2, x_790);
x_799 = lean_ctor_get(x_784, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_784, 1);
lean_inc(x_800);
x_801 = lean_ctor_get(x_784, 2);
lean_inc(x_801);
x_802 = lean_nat_dec_lt(x_800, x_801);
if (x_802 == 0)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
lean_dec(x_801);
lean_dec(x_800);
lean_dec(x_799);
lean_dec(x_788);
lean_dec(x_24);
if (lean_is_scalar(x_787)) {
 x_803 = lean_alloc_ctor(0, 2, 0);
} else {
 x_803 = x_787;
}
lean_ctor_set(x_803, 0, x_798);
lean_ctor_set(x_803, 1, x_786);
if (lean_is_scalar(x_785)) {
 x_804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_804 = x_785;
}
lean_ctor_set(x_804, 0, x_784);
lean_ctor_set(x_804, 1, x_803);
x_805 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_805, 0, x_783);
lean_ctor_set(x_805, 1, x_804);
x_806 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_806, 0, x_805);
x_25 = x_806;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; 
if (lean_is_exclusive(x_784)) {
 lean_ctor_release(x_784, 0);
 lean_ctor_release(x_784, 1);
 lean_ctor_release(x_784, 2);
 x_807 = x_784;
} else {
 lean_dec_ref(x_784);
 x_807 = lean_box(0);
}
x_808 = lean_array_fget(x_799, x_800);
x_809 = lean_unsigned_to_nat(1u);
x_810 = lean_nat_add(x_800, x_809);
lean_dec(x_800);
if (lean_is_scalar(x_807)) {
 x_811 = lean_alloc_ctor(0, 3, 0);
} else {
 x_811 = x_807;
}
lean_ctor_set(x_811, 0, x_799);
lean_ctor_set(x_811, 1, x_810);
lean_ctor_set(x_811, 2, x_801);
x_812 = lean_ctor_get(x_783, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_783, 1);
lean_inc(x_813);
x_814 = lean_ctor_get(x_783, 2);
lean_inc(x_814);
x_815 = lean_nat_dec_lt(x_813, x_814);
if (x_815 == 0)
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
lean_dec(x_814);
lean_dec(x_813);
lean_dec(x_812);
lean_dec(x_808);
lean_dec(x_788);
lean_dec(x_24);
if (lean_is_scalar(x_787)) {
 x_816 = lean_alloc_ctor(0, 2, 0);
} else {
 x_816 = x_787;
}
lean_ctor_set(x_816, 0, x_798);
lean_ctor_set(x_816, 1, x_786);
if (lean_is_scalar(x_785)) {
 x_817 = lean_alloc_ctor(0, 2, 0);
} else {
 x_817 = x_785;
}
lean_ctor_set(x_817, 0, x_811);
lean_ctor_set(x_817, 1, x_816);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_783);
lean_ctor_set(x_818, 1, x_817);
x_819 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_819, 0, x_818);
x_25 = x_819;
x_26 = x_21;
goto block_33;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; 
lean_dec(x_787);
lean_dec(x_785);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 lean_ctor_release(x_783, 2);
 x_820 = x_783;
} else {
 lean_dec_ref(x_783);
 x_820 = lean_box(0);
}
x_821 = lean_array_fget(x_812, x_813);
x_822 = lean_nat_add(x_813, x_809);
lean_dec(x_813);
if (lean_is_scalar(x_820)) {
 x_823 = lean_alloc_ctor(0, 3, 0);
} else {
 x_823 = x_820;
}
lean_ctor_set(x_823, 0, x_812);
lean_ctor_set(x_823, 1, x_822);
lean_ctor_set(x_823, 2, x_814);
lean_inc(x_6);
lean_inc(x_8);
x_824 = lean_array_push(x_8, x_6);
x_825 = lean_nat_sub(x_821, x_808);
lean_dec(x_808);
lean_dec(x_821);
x_826 = lean_nat_sub(x_825, x_809);
lean_dec(x_825);
x_827 = lean_unsigned_to_nat(0u);
lean_inc(x_826);
lean_inc(x_9);
x_828 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_9, x_826, x_827, x_826, x_809, x_824, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_826);
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_828, 1);
lean_inc(x_830);
lean_dec(x_828);
x_831 = lean_nat_dec_lt(x_809, x_10);
if (x_831 == 0)
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
lean_dec(x_788);
lean_inc(x_19);
x_832 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_830);
x_833 = lean_ctor_get(x_832, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_832, 1);
lean_inc(x_834);
lean_dec(x_832);
x_835 = lean_ctor_get(x_19, 8);
lean_inc(x_835);
x_836 = lean_st_ref_get(x_20, x_834);
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
x_838 = lean_ctor_get(x_836, 1);
lean_inc(x_838);
lean_dec(x_836);
x_839 = lean_ctor_get(x_837, 0);
lean_inc(x_839);
lean_dec(x_837);
x_840 = lean_environment_main_module(x_839);
x_841 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_842 = lean_name_mk_string(x_7, x_841);
x_843 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_844 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_845 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_845, 0, x_843);
lean_ctor_set(x_845, 1, x_2);
lean_ctor_set(x_845, 2, x_844);
x_846 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_835);
lean_inc(x_840);
x_847 = l_Lean_addMacroScope(x_840, x_846, x_835);
x_848 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_849 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_849, 0, x_848);
lean_ctor_set(x_849, 1, x_5);
lean_inc(x_833);
x_850 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_850, 0, x_833);
lean_ctor_set(x_850, 1, x_845);
lean_ctor_set(x_850, 2, x_847);
lean_ctor_set(x_850, 3, x_849);
lean_inc(x_4);
x_851 = l_Lean_addMacroScope(x_840, x_4, x_835);
lean_inc(x_5);
lean_inc(x_3);
x_852 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_852, 0, x_833);
lean_ctor_set(x_852, 1, x_3);
lean_ctor_set(x_852, 2, x_851);
lean_ctor_set(x_852, 3, x_5);
lean_inc(x_8);
x_853 = lean_array_push(x_8, x_852);
x_854 = lean_box(2);
x_855 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_856 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_856, 0, x_854);
lean_ctor_set(x_856, 1, x_855);
lean_ctor_set(x_856, 2, x_853);
x_857 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_858 = lean_array_push(x_857, x_850);
x_859 = lean_array_push(x_858, x_856);
x_860 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_860, 0, x_854);
lean_ctor_set(x_860, 1, x_842);
lean_ctor_set(x_860, 2, x_859);
x_861 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_829, x_798, x_811, x_823, x_786, x_860, x_15, x_16, x_17, x_18, x_19, x_20, x_838);
lean_dec(x_24);
x_862 = lean_ctor_get(x_861, 0);
lean_inc(x_862);
x_863 = lean_ctor_get(x_861, 1);
lean_inc(x_863);
lean_dec(x_861);
x_25 = x_862;
x_26 = x_863;
goto block_33;
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
lean_inc(x_19);
x_864 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_19, x_20, x_830);
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
lean_dec(x_864);
x_867 = lean_ctor_get(x_19, 8);
lean_inc(x_867);
x_868 = lean_st_ref_get(x_20, x_866);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
x_871 = lean_ctor_get(x_869, 0);
lean_inc(x_871);
lean_dec(x_869);
x_872 = lean_environment_main_module(x_871);
x_873 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8;
lean_inc(x_7);
x_874 = lean_name_mk_string(x_7, x_873);
x_875 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9;
lean_inc(x_865);
x_876 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_876, 0, x_865);
lean_ctor_set(x_876, 1, x_875);
x_877 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1;
lean_inc(x_7);
x_878 = lean_name_mk_string(x_7, x_877);
x_879 = l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3;
x_880 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2;
lean_inc(x_2);
x_881 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_881, 0, x_879);
lean_ctor_set(x_881, 1, x_2);
lean_ctor_set(x_881, 2, x_880);
x_882 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3;
lean_inc(x_867);
lean_inc(x_872);
x_883 = l_Lean_addMacroScope(x_872, x_882, x_867);
x_884 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4;
lean_inc(x_5);
x_885 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_885, 0, x_884);
lean_ctor_set(x_885, 1, x_5);
lean_inc(x_865);
x_886 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_886, 0, x_865);
lean_ctor_set(x_886, 1, x_881);
lean_ctor_set(x_886, 2, x_883);
lean_ctor_set(x_886, 3, x_885);
lean_inc(x_4);
x_887 = l_Lean_addMacroScope(x_872, x_4, x_867);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_865);
x_888 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_888, 0, x_865);
lean_ctor_set(x_888, 1, x_3);
lean_ctor_set(x_888, 2, x_887);
lean_ctor_set(x_888, 3, x_5);
lean_inc(x_8);
x_889 = lean_array_push(x_8, x_888);
x_890 = lean_box(2);
x_891 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6;
x_892 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_892, 0, x_890);
lean_ctor_set(x_892, 1, x_891);
lean_ctor_set(x_892, 2, x_889);
x_893 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7;
x_894 = lean_array_push(x_893, x_886);
x_895 = lean_array_push(x_894, x_892);
x_896 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_896, 0, x_890);
lean_ctor_set(x_896, 1, x_878);
lean_ctor_set(x_896, 2, x_895);
x_897 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10;
lean_inc(x_7);
x_898 = lean_name_mk_string(x_7, x_897);
x_899 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11;
lean_inc(x_865);
x_900 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_900, 0, x_865);
lean_ctor_set(x_900, 1, x_899);
x_901 = l_Nat_repr(x_788);
x_902 = l_Lean_numLitKind;
x_903 = l_Lean_Syntax_mkLit(x_902, x_901, x_890);
lean_inc(x_8);
x_904 = lean_array_push(x_8, x_903);
x_905 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_905, 0, x_890);
lean_ctor_set(x_905, 1, x_891);
lean_ctor_set(x_905, 2, x_904);
x_906 = lean_array_push(x_893, x_900);
x_907 = lean_array_push(x_906, x_905);
x_908 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_908, 0, x_890);
lean_ctor_set(x_908, 1, x_898);
lean_ctor_set(x_908, 2, x_907);
lean_inc(x_8);
x_909 = lean_array_push(x_8, x_908);
x_910 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_910, 0, x_890);
lean_ctor_set(x_910, 1, x_891);
lean_ctor_set(x_910, 2, x_909);
x_911 = lean_array_push(x_893, x_896);
x_912 = lean_array_push(x_911, x_910);
x_913 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_913, 0, x_890);
lean_ctor_set(x_913, 1, x_891);
lean_ctor_set(x_913, 2, x_912);
x_914 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12;
x_915 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_915, 0, x_865);
lean_ctor_set(x_915, 1, x_914);
x_916 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13;
x_917 = lean_array_push(x_916, x_876);
x_918 = lean_array_push(x_917, x_913);
x_919 = lean_array_push(x_918, x_915);
x_920 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_920, 0, x_890);
lean_ctor_set(x_920, 1, x_874);
lean_ctor_set(x_920, 2, x_919);
x_921 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_24, x_829, x_798, x_811, x_823, x_786, x_920, x_15, x_16, x_17, x_18, x_19, x_20, x_870);
lean_dec(x_24);
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_921, 1);
lean_inc(x_923);
lean_dec(x_921);
x_25 = x_922;
x_26 = x_923;
goto block_33;
}
}
}
}
}
block_33:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = 1;
x_31 = lean_usize_add(x_13, x_30);
x_13 = x_31;
x_14 = x_29;
x_21 = x_26;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__6;
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__8;
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__10;
x_2 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_inc(x_8);
x_11 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_8, 8);
lean_inc(x_14);
x_15 = lean_st_ref_get(x_9, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_environment_main_module(x_18);
x_20 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__4;
x_21 = l_Lean_addMacroScope(x_19, x_20, x_14);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__3;
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_inc(x_8);
x_25 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_8, x_9, x_17);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_9, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__13;
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___lambda__1___closed__1;
x_33 = lean_array_push(x_32, x_31);
x_34 = lean_box(2);
x_35 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__12;
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_33);
x_37 = lean_array_get_size(x_2);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Array_toSubarray___rarg(x_2, x_38, x_37);
x_40 = lean_array_get_size(x_3);
x_41 = l_Array_toSubarray___rarg(x_3, x_38, x_40);
x_42 = lean_array_get_size(x_1);
x_43 = lean_unsigned_to_nat(1u);
lean_inc(x_42);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_38);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
x_45 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackMutual_go___closed__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_usize_of_nat(x_42);
x_50 = 0;
x_51 = l_Lean_Elab_WF_elabWFRel_generateElements___closed__10;
x_52 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(x_1, x_38, x_23, x_20, x_22, x_24, x_51, x_32, x_36, x_42, x_1, x_49, x_50, x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_42);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = !lean_is_exclusive(x_52);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 0);
lean_dec(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_23 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_23, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_generateElements___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_WF_elabWFRel_generateElements(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_17 = l_Lean_Elab_WF_getForbiddenByTrivialSizeOf(x_1, x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_16, x_3, x_18);
x_3 = x_21;
x_4 = x_22;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_Elab_Term_saveState___rarg(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = 0;
x_22 = l_Lean_Elab_Term_SavedState_restore(x_10, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Elab_Term_saveState___rarg(x_8, x_9, x_10, x_11, x_12, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Elab_WF_elabWFRel_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
x_26 = 0;
x_27 = l_Lean_Elab_Term_SavedState_restore(x_15, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_10, x_9);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
x_21 = lean_array_uget(x_8, x_10);
lean_inc(x_16);
lean_inc(x_6);
x_22 = l_Lean_Elab_WF_elabWFRel_generateElements(x_1, x_6, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Lean_observing_x3f___at_Lean_Elab_WF_elabWFRel_guess___spec__3___at_Lean_Elab_WF_elabWFRel_guess___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_23, x_12, x_13, x_14, x_15, x_16, x_17, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; size_t x_28; size_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 1;
x_29 = lean_usize_add(x_10, x_28);
lean_inc(x_7);
{
size_t _tmp_9 = x_29;
lean_object* _tmp_10 = x_7;
lean_object* _tmp_17 = x_27;
x_10 = _tmp_9;
x_11 = _tmp_10;
x_18 = _tmp_17;
}
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_25, 0, x_39);
return x_25;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_42 = x_26;
} else {
 lean_dec_ref(x_26);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg___boxed), 18, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to prove termination, use `termination_by` to specify a well-founded relation", 84);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2;
x_10 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_3);
x_13 = l_Lean_Elab_WF_getNumCandidateArgs(x_3, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_get_size(x_1);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_3);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(x_3, x_17, x_18, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1;
x_23 = lean_unsigned_to_nat(32u);
x_24 = l_Lean_Elab_WF_generateCombinations_x3f(x_20, x_14, x_23);
lean_dec(x_20);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_28 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_14, x_28, x_25, x_27, x_18, x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
lean_dec(x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = lean_apply_8(x_22, x_33, x_6, x_7, x_8, x_9, x_10, x_11, x_32);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_29, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_37);
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_14);
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
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
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
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_13, 0);
x_47 = lean_ctor_get(x_13, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_13);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel_guess___rarg), 12, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_WF_elabWFRel_guess___spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_WF_elabWFRel_guess___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg___boxed(lean_object** _args) {
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
_start:
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_20 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_guess___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_20, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_8);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = 0;
x_12 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
x_16 = l_Lean_Meta_instantiateMVars(x_14, x_6, x_7, x_8, x_9, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_17);
x_19 = l_Lean_Meta_getMVars(x_17, x_6, x_7, x_8, x_9, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_22 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_20, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_8(x_3, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Elab_WF_elabWFRel_guess___rarg(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_2);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set(x_1, 0, x_6);
x_19 = lean_box(0);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_box(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_23, 0, x_18);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_19);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1), 10, 3);
lean_closure_set(x_24, 0, x_23);
lean_closure_set(x_24, 1, x_19);
lean_closure_set(x_24, 2, x_5);
x_25 = l_Lean_Elab_Term_withDeclName___rarg(x_3, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_1);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = l_Lean_Elab_WF_elabWFRel_go___rarg(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_4);
lean_dec(x_2);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_6);
x_31 = lean_box(0);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_box(x_32);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_35, 0, x_29);
lean_closure_set(x_35, 1, x_30);
lean_closure_set(x_35, 2, x_33);
lean_closure_set(x_35, 3, x_34);
lean_closure_set(x_35, 4, x_31);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg___lambda__1), 10, 3);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_31);
lean_closure_set(x_36, 2, x_5);
x_37 = l_Lean_Elab_Term_withDeclName___rarg(x_3, x_36, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_28, 0);
lean_inc(x_38);
lean_dec(x_28);
x_39 = l_Lean_Elab_WF_elabWFRel_go___rarg(x_2, x_3, x_4, x_5, x_6, x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_39;
}
}
}
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
x_3 = lean_name_mk_string(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_14 = l_Lean_Meta_getLevel(x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_WF_elabWFRel___rarg___closed__2;
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l_Lean_mkApp(x_20, x_4);
x_22 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__6;
x_43 = lean_st_ref_get(x_12, x_16);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 3);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get_uint8(x_45, sizeof(void*)*1);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = 0;
x_23 = x_48;
x_24 = x_47;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec(x_43);
x_50 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unbox(x_51);
lean_dec(x_51);
x_23 = x_53;
x_24 = x_52;
goto block_42;
}
block_42:
{
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_5, x_1, x_2, x_3, x_6, x_21, x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = 0;
x_28 = lean_box(0);
lean_inc(x_9);
x_29 = l_Lean_Meta_mkFreshTypeMVar(x_27, x_28, x_9, x_10, x_11, x_12, x_24);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Expr_mvarId_x21(x_30);
lean_dec(x_30);
x_33 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_Elab_WF_elabWFRel___rarg___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_22, x_37, x_7, x_8, x_9, x_10, x_11, x_12, x_31);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_5, x_1, x_2, x_3, x_6, x_21, x_39, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
lean_dec(x_39);
return x_41;
}
}
}
else
{
uint8_t x_54; 
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
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_WF_elabWFRel___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_elabWFRel___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_WF_elabWFRel___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_15;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rename(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Meta_Tactic_Rename(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
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
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_getRefFromElems___closed__1);
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
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__13);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary_go___closed__14);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Rel_0__Lean_Elab_WF_unpackUnary___lambda__2___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__1);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__2);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__3);
l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4 = _init_l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4();
lean_mark_persistent(l_Subarray_forInUnsafe_loop___at_Lean_Elab_WF_getForbiddenByTrivialSizeOf___spec__1___closed__4);
l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1 = _init_l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_generateCombinations_x3f_go___closed__1);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__1);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__2);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__3);
l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4 = _init_l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_go___rarg___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__11);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__12);
l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13 = _init_l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Elab_WF_elabWFRel_generateElements___spec__2___closed__13);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__1);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__2 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__2);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__3 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__3);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__4 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__4);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__5 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__5);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__6 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__6();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__6);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__7 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__7();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__7);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__8 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__8();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__8);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__9 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__9();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__9);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__10 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__10();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__10);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__11 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__11();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__11);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__12 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__12();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__12);
l_Lean_Elab_WF_elabWFRel_generateElements___closed__13 = _init_l_Lean_Elab_WF_elabWFRel_generateElements___closed__13();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_generateElements___closed__13);
l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__1);
l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_guess___rarg___lambda__1___closed__2);
l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1 = _init_l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_elabWFRel_guess___rarg___closed__1);
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
