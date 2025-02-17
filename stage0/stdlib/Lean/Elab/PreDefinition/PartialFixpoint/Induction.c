// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Induction
// Imports: Lean.Meta.Basic Lean.Meta.Match.MatcherApp.Transform Lean.Meta.Check Lean.Meta.Tactic.Subst Lean.Meta.Injective Lean.Meta.ArgsPacker Lean.Meta.PProdN Lean.Meta.Tactic.Apply Lean.Elab.PreDefinition.PartialFixpoint.Eqns Lean.Elab.Command Lean.Meta.Tactic.ElimInfo
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
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__6;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__1;
extern lean_object* l_Lean_Elab_PartialFixpoint_eqnInfoExt;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3;
lean_object* l_Lean_registerReservedNameAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___spec__1(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__9;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__3;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___boxed(lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___boxed(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5___boxed(lean_object**);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__7;
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_reduceProjs___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__10;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__14;
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1___closed__1;
static lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__1;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimOptParam___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__2;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_isInductName___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5;
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12(size_t, size_t, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__1;
lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__12;
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__3;
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__11;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__1;
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__6;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642_(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_isOptionFixpoint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_CCPOProdProjs___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1___lambda__2___boxed(lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__9;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__7;
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Meta_PProdN_packLambdas___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__3;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__2;
static lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__8;
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___boxed(lean_object**);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___rarg(lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828_(lean_object*);
lean_object* l_Lean_Meta_PProdN_proj(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__13;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__10;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_genMk___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__1;
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
extern uint8_t l_Lean_instInhabitedBinderInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__15;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__10(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__1;
lean_object* l_Lean_Meta_PProdN_projs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1___lambda__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__4;
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__8;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_PProdN_reduceProjs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__14(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__11;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__1;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__11;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9(size_t, size_t, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__2;
extern lean_object* l_Lean_Meta_instMonadMetaM;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_CCPOProdProjs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__2;
lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__3;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_mkSimpCongrTheorem___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___boxed(lean_object**);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__12;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17(size_t, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__11;
static lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1___boxed(lean_object*);
static uint64_t l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__3;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_isInductName___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__8;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__13;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___boxed__const__1;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__2;
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isInductName(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1___closed__1;
uint8_t l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__7;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__1;
lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___closed__1;
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__4;
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__2(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__21___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___closed__1;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__10;
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__6;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__5;
uint8_t l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_isInductName___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__4___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__1;
lean_object* l_Lean_Meta_PProdN_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__2;
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__21(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5___closed__1;
lean_object* l_Array_back_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__5;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__5;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__3;
lean_object* l_Lean_getConstInfoDefn___at___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_stripProjs(lean_object*);
lean_object* l_Lean_Meta_elimOptParam___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___boxed(lean_object**);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__6;
extern lean_object* l_Lean_instInhabitedName;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_instInhabitedDefinitionVal;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__1;
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__11(lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__1;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1___closed__1;
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__4;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isInductName___lambda__1___boxed(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__5(size_t, size_t, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfUntil(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__3;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__14___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_betaReduce___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__14;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__1(lean_object*);
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Order", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("admissible_and", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_mk(x_21);
x_23 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__4;
x_24 = l_Lean_Meta_mkAppOptM(x_23, x_22, x_5, x_6, x_7, x_8, x_9);
return x_24;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("admissible_pprod_snd", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("admissible_pprod_fst", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_1, x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Elab_PartialFixpoint_mkAdmProj(x_6, x_15, x_2, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_4);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_5);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_6);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_mk(x_31);
x_33 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__2;
x_34 = l_Lean_Meta_mkAppOptM(x_33, x_32, x_7, x_8, x_9, x_10, x_18);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
return x_16;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_16, 0);
x_37 = lean_ctor_get(x_16, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_16);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_3);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_4);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_5);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_6);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_2);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_mk(x_51);
x_53 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__4;
x_54 = l_Lean_Meta_mkAppOptM(x_53, x_52, x_7, x_8, x_9, x_10, x_11);
return x_54;
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkAdmProj: unexpected instance ", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_MessageData_ofExpr(x_1);
x_9 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instCCPOPProd", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("i == 0\n    ", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__3;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.PartialFixpoint.Induction", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PartialFixpoint.mkAdmProj", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__6;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__7;
x_3 = lean_unsigned_to_nat(38u);
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__5;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__2;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_Meta_whnfUntil(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_2, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_10);
lean_dec(x_3);
x_17 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__8;
x_18 = l_panic___at_Lean_Meta_PProdN_packLambdas___spec__1(x_17, x_4, x_5, x_6, x_7, x_13);
return x_18;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_ctor_set(x_10, 0, x_3);
return x_10;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_22 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__8;
x_23 = l_panic___at_Lean_Meta_PProdN_packLambdas___spec__1(x_22, x_4, x_5, x_6, x_7, x_19);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
lean_inc(x_26);
x_27 = l_Lean_Expr_cleanupAnnotations(x_26);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_3);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2(x_26, x_29, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l_Lean_Expr_appArg(x_27, lean_box(0));
x_32 = l_Lean_Expr_appFnCleanup(x_27, lean_box(0));
x_33 = l_Lean_Expr_isApp(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_3);
x_34 = lean_box(0);
x_35 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2(x_26, x_34, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Lean_Expr_appArg(x_32, lean_box(0));
x_37 = l_Lean_Expr_appFnCleanup(x_32, lean_box(0));
x_38 = l_Lean_Expr_isApp(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_3);
x_39 = lean_box(0);
x_40 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2(x_26, x_39, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_Expr_appArg(x_37, lean_box(0));
x_42 = l_Lean_Expr_appFnCleanup(x_37, lean_box(0));
x_43 = l_Lean_Expr_isApp(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_3);
x_44 = lean_box(0);
x_45 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2(x_26, x_44, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = l_Lean_Expr_appArg(x_42, lean_box(0));
x_47 = l_Lean_Expr_appFnCleanup(x_42, lean_box(0));
x_48 = l_Lean_Expr_isConstOf(x_47, x_9);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_46);
lean_dec(x_41);
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_3);
x_49 = lean_box(0);
x_50 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2(x_26, x_49, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_26);
x_51 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1(x_2, x_3, x_46, x_41, x_36, x_31, x_4, x_5, x_6, x_7, x_25);
return x_51;
}
}
}
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_10);
if (x_52 == 0)
{
return x_10;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_10, 0);
x_54 = lean_ctor_get(x_10, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_10);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkAdmProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_PartialFixpoint_mkAdmProj(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_pop(x_1);
x_5 = lean_array_push(x_4, x_2);
x_6 = lean_array_push(x_5, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_3, x_1);
lean_dec(x_3);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = l_Lean_instInhabitedExpr;
x_6 = l_Array_back_x21___rarg(x_5, x_2);
x_7 = l_Lean_Expr_cleanupAnnotations(x_6);
x_8 = l_Lean_Expr_isApp(x_7);
if (x_8 == 0)
{
lean_dec(x_7);
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Expr_appArg(x_7, lean_box(0));
x_11 = l_Lean_Expr_appFnCleanup(x_7, lean_box(0));
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Expr_appArg(x_11, lean_box(0));
x_15 = l_Lean_Expr_appFnCleanup(x_11, lean_box(0));
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
goto _start;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_appFnCleanup(x_15, lean_box(0));
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_10);
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_Expr_appFnCleanup(x_18, lean_box(0));
x_22 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__2;
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_dec(x_14);
lean_dec(x_10);
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1___lambda__1(x_2, x_14, x_10);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_2 = x_26;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_CCPOProdProjs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_mk(x_4);
x_6 = l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1(x_1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1___lambda__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_CCPOProdProjs___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_CCPOProdProjs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_PartialFixpoint_CCPOProdProjs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_6;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_11, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = lean_array_fget(x_13, x_14);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_14, x_22);
lean_dec(x_14);
lean_ctor_set(x_11, 1, x_23);
if (x_9 == 0)
{
size_t x_24; size_t x_25; 
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_5, x_24);
x_5 = x_25;
goto _start;
}
else
{
lean_object* x_27; size_t x_28; size_t x_29; 
x_27 = lean_array_push(x_12, x_21);
lean_ctor_set(x_6, 1, x_27);
x_28 = 1;
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
x_31 = lean_array_fget(x_13, x_14);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_14, x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_15);
if (x_9 == 0)
{
size_t x_35; size_t x_36; 
lean_dec(x_31);
lean_ctor_set(x_6, 0, x_34);
x_35 = 1;
x_36 = lean_usize_add(x_5, x_35);
x_5 = x_36;
goto _start;
}
else
{
lean_object* x_38; size_t x_39; size_t x_40; 
x_38 = lean_array_push(x_12, x_31);
lean_ctor_set(x_6, 1, x_38);
lean_ctor_set(x_6, 0, x_34);
x_39 = 1;
x_40 = lean_usize_add(x_5, x_39);
x_5 = x_40;
goto _start;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_6, 0);
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_6);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 2);
lean_inc(x_46);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
x_50 = lean_array_fget(x_44, x_45);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_45, x_51);
lean_dec(x_45);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 3, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_46);
if (x_9 == 0)
{
lean_object* x_54; size_t x_55; size_t x_56; 
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_43);
x_55 = 1;
x_56 = lean_usize_add(x_5, x_55);
x_5 = x_56;
x_6 = x_54;
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; 
x_58 = lean_array_push(x_43, x_50);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
x_60 = 1;
x_61 = lean_usize_add(x_5, x_60);
x_5 = x_61;
x_6 = x_59;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_toSubarray___rarg(x_2, x_4, x_3);
x_6 = lean_box(0);
x_7 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___spec__1___rarg(x_1, x_6, x_1, x_9, x_10, x_8);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__3;
x_7 = lean_string_append(x_6, x_2);
lean_dec(x_2);
x_8 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = lean_nat_add(x_3, x_4);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = lean_string_append(x_12, x_6);
x_14 = lean_box(0);
x_15 = l_Lean_Name_str___override(x_14, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Lean_Name_str___override(x_16, x_2);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1___boxed), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
x_4 = l_Array_ofFn___rarg(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = l_Lean_getConstInfoDefn___at___private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_unfoldThmType___spec__1(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_13, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_1, x_13, x_16, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
lean_inc(x_1);
x_15 = l_Lean_Expr_sort___override(x_1);
x_16 = l_Lean_mkArrow(x_12, x_15, x_7, x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_14, x_3, x_17);
x_3 = x_20;
x_4 = x_21;
x_9 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = lean_array_fget(x_4, x_6);
x_14 = lean_array_get_size(x_2);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_6);
x_15 = l_Lean_Meta_PProdN_proj(x_14, x_6, x_1, x_3);
x_16 = l_Lean_Expr_app___override(x_13, x_15);
x_17 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_18 = lean_array_push(x_8, x_16);
x_5 = x_12;
x_6 = x_17;
x_7 = lean_box(0);
x_8 = x_18;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("admissible", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_16);
lean_dec(x_5);
x_18 = lean_array_fget(x_4, x_6);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get(x_19, x_2, x_6);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_array_get(x_19, x_1, x_6);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_mk(x_28);
x_30 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_31 = l_Lean_Meta_mkAppOptM(x_30, x_29, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_nat_add(x_6, x_16);
lean_dec(x_6);
x_35 = lean_array_push(x_8, x_32);
x_5 = x_17;
x_6 = x_34;
x_7 = lean_box(0);
x_8 = x_35;
x_13 = x_33;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_37 = !lean_is_exclusive(x_31);
if (x_37 == 0)
{
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_8);
lean_ctor_set(x_41, 1, x_13);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_4, x_15);
lean_dec(x_4);
x_17 = lean_array_fget(x_3, x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_18 = l_Lean_Elab_PartialFixpoint_mkAdmProj(x_1, x_5, x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_22 = lean_array_push(x_7, x_19);
x_4 = x_16;
x_5 = x_21;
x_6 = lean_box(0);
x_7 = x_22;
x_12 = x_20;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_12);
return x_28;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("f", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = l_Lean_Name_str___override(x_13, x_12);
x_15 = lean_array_uset(x_7, x_2, x_14);
x_2 = x_11;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__2;
x_18 = lean_array_uset(x_7, x_2, x_17);
x_2 = x_11;
x_3 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_array_fget(x_3, x_5);
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_array_get(x_13, x_1, x_5);
x_15 = l_Lean_Expr_app___override(x_14, x_12);
x_16 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_17 = lean_array_push(x_7, x_15);
x_4 = x_11;
x_5 = x_16;
x_6 = lean_box(0);
x_7 = x_17;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ih", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = l_Lean_Expr_fvarId_x21(x_6);
lean_dec(x_6);
x_10 = l_Lean_Expr_hasAnyFVar_visit___at_Lean_Expr_containsFVar___spec__1(x_9, x_1);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_box(x_10);
x_14 = lean_array_uset(x_8, x_3, x_13);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12___lambda__1___boxed), 7, 1);
lean_closure_set(x_12, 0, x_11);
lean_ctor_set(x_5, 1, x_12);
x_13 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_9;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_17 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12___lambda__1___boxed), 7, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_uset(x_7, x_2, x_18);
x_2 = x_9;
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__14(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_5, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_array_uset(x_7, x_2, x_14);
x_2 = x_9;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_array_uset(x_7, x_2, x_22);
x_2 = x_9;
x_3 = x_23;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabitedOfMonad___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_push(x_1, x_5);
x_12 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__1;
x_2 = lean_alloc_closure((void*)(l_Pi_instInhabited___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_instInhabitedBinderInfo;
x_2 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__2;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedName;
x_2 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_apply_6(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__4;
x_15 = lean_array_get(x_14, x_1, x_10);
lean_dec(x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_20 = lean_apply_6(x_19, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__2), 10, 4);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_3);
x_24 = 0;
x_25 = lean_unbox(x_18);
lean_dec(x_18);
x_26 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(x_17, x_25, x_21, x_23, x_24, x_5, x_6, x_7, x_8, x_22);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___closed__1;
x_10 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg(x_2, x_3, x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__15___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_size(x_2);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__14(x_9, x_10, x_2);
x_12 = l_Lean_Meta_withLocalDecls___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__15___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclsD___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__13___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_size(x_2);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12(x_9, x_10, x_2);
x_12 = l_Lean_Meta_withLocalDeclsD___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__13___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclsDND___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__11___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_reduceProjs___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_reduceProjs___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_15 = l_Lean_Meta_PProdN_mk(x_1, x_2, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_mk(x_19);
x_21 = l_Lean_Expr_beta(x_3, x_20);
lean_inc(x_5);
x_22 = l_Lean_Meta_PProdN_proj(x_4, x_5, x_6, x_21);
x_23 = l_Lean_instInhabitedExpr;
x_24 = lean_array_get(x_23, x_7, x_5);
lean_dec(x_5);
x_25 = l_Lean_Expr_app___override(x_24, x_22);
x_26 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__1;
x_27 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__2;
lean_inc(x_13);
lean_inc(x_12);
x_28 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_25, x_26, x_27, x_12, x_13, x_17);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_array_size(x_2);
lean_inc(x_2);
x_32 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__10(x_29, x_31, x_8, x_2);
x_33 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg(x_32, x_2);
x_34 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg(x_32, x_9);
x_35 = l_Array_append___rarg(x_33, x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = 1;
x_38 = 1;
x_39 = l_Lean_Meta_mkForallFVars(x_35, x_29, x_36, x_37, x_38, x_10, x_11, x_12, x_13, x_30);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_32);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_39, 0);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_32);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_32);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
return x_39;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_39, 0);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_39);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
return x_28;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_28);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_15);
if (x_55 == 0)
{
return x_15;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_15);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_array_get_size(x_9);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__8(x_1, x_9, x_9, x_15, x_17, lean_box(0), x_16);
x_19 = lean_array_size(x_18);
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9(x_19, x_2, x_18);
x_21 = lean_box_usize(x_2);
x_22 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___boxed), 14, 8);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_9);
lean_closure_set(x_22, 2, x_4);
lean_closure_set(x_22, 3, x_5);
lean_closure_set(x_22, 4, x_6);
lean_closure_set(x_22, 5, x_7);
lean_closure_set(x_22, 6, x_1);
lean_closure_set(x_22, 7, x_21);
x_23 = l_Lean_Meta_withLocalDeclsDND___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__11___rarg(x_8, x_20, x_22, x_10, x_11, x_12, x_13, x_14);
return x_23;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedExpr;
x_2 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17(size_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_11, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_11, x_22);
lean_dec(x_11);
lean_inc(x_2);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7(x_4, x_1, x_2);
x_25 = l_Array_zip___rarg(x_24, x_5);
lean_dec(x_24);
x_26 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__2;
x_27 = lean_box_usize(x_1);
lean_inc(x_7);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_3);
lean_inc(x_6);
lean_inc(x_8);
x_28 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__2___boxed), 14, 8);
lean_closure_set(x_28, 0, x_8);
lean_closure_set(x_28, 1, x_27);
lean_closure_set(x_28, 2, x_6);
lean_closure_set(x_28, 3, x_3);
lean_closure_set(x_28, 4, x_9);
lean_closure_set(x_28, 5, x_12);
lean_closure_set(x_28, 6, x_7);
lean_closure_set(x_28, 7, x_26);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_29 = l_Lean_Meta_withLocalDeclsDND___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__11___rarg(x_26, x_25, x_28, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_nat_add(x_12, x_22);
lean_dec(x_12);
x_33 = lean_array_push(x_14, x_30);
x_11 = x_23;
x_12 = x_32;
x_13 = lean_box(0);
x_14 = x_33;
x_19 = x_31;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_19);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__18(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_6, x_12);
lean_dec(x_6);
x_14 = lean_array_fget(x_5, x_7);
x_15 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__1;
x_16 = lean_array_get(x_15, x_1, x_7);
lean_inc(x_3);
x_17 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg(x_16, x_3);
lean_inc(x_4);
x_18 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg(x_16, x_4);
lean_dec(x_16);
x_19 = l_Array_append___rarg(x_17, x_18);
lean_dec(x_18);
x_20 = l_Lean_mkAppN(x_14, x_19);
lean_dec(x_19);
x_21 = lean_nat_add(x_7, x_12);
lean_dec(x_7);
x_22 = lean_array_push(x_9, x_20);
x_6 = x_13;
x_7 = x_21;
x_8 = lean_box(0);
x_9 = x_22;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__19(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_16);
lean_dec(x_5);
x_18 = lean_array_fget(x_4, x_6);
x_19 = l_Lean_instInhabitedDefinitionVal;
x_20 = lean_array_get(x_19, x_1, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_mkSimpCongrTheorem___spec__1(x_22, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_mkAppN(x_24, x_2);
x_27 = l_Lean_Expr_app___override(x_18, x_26);
x_28 = lean_nat_add(x_6, x_16);
lean_dec(x_6);
x_29 = lean_array_push(x_8, x_27);
x_5 = x_17;
x_6 = x_28;
x_7 = lean_box(0);
x_8 = x_29;
x_13 = x_25;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_6);
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
lean_object* x_35; 
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_13);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = 0;
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_11, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_6);
if (x_8 == 0)
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_3);
x_2 = x_12;
x_3 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_13 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__4(x_2, x_1, x_4, x_1, x_10, x_12, lean_box(0), x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Meta_PProdN_pack(x_3, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_mk(x_18);
x_20 = 0;
x_21 = 1;
x_22 = 1;
x_23 = l_Lean_Meta_mkLambdaFVars(x_19, x_15, x_20, x_21, x_20, x_22, x_5, x_6, x_7, x_8, x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_19);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_Meta_PProdN_projs(x_1, x_2, x_3);
lean_inc(x_9);
x_16 = l_Lean_Meta_PProdN_projs(x_1, x_4, x_9);
x_17 = lean_array_get_size(x_5);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__18(x_6, x_5, x_15, x_16, x_5, x_17, x_19, lean_box(0), x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l_Lean_Meta_PProdN_mk(x_7, x_20, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_array_mk(x_25);
x_27 = 0;
x_28 = 1;
x_29 = 1;
x_30 = l_Lean_Meta_mkLambdaFVars(x_26, x_22, x_27, x_28, x_27, x_29, x_10, x_11, x_12, x_13, x_23);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_26);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_box(0);
lean_inc(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_mk(x_14);
x_16 = l_Lean_Expr_beta(x_1, x_15);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__2___boxed), 14, 8);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_7);
lean_closure_set(x_17, 3, x_16);
lean_closure_set(x_17, 4, x_4);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_6);
lean_closure_set(x_17, 7, x_13);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__2;
x_19 = 0;
x_20 = 0;
x_21 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(x_18, x_19, x_16, x_17, x_20, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("approx", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix_induct", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("partialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("induction", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__5;
x_2 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__6;
x_3 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__7;
x_4 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("complete body of fixpoint induction principle:", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
lean_inc(x_5);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__3), 12, 6);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_3);
lean_closure_set(x_22, 3, x_16);
lean_closure_set(x_22, 4, x_4);
lean_closure_set(x_22, 5, x_5);
x_23 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__2;
x_24 = 0;
x_25 = 0;
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_26 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(x_23, x_24, x_3, x_22, x_25, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_6);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_7);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_8);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_9);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_10);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_27);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_mk(x_43);
x_45 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__4;
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_46 = l_Lean_Meta_mkAppOptM(x_45, x_44, x_17, x_18, x_19, x_20, x_28);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__19(x_11, x_12, x_13, x_13, x_2, x_49, lean_box(0), x_14, x_17, x_18, x_19, x_20, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_53 = l_Lean_Meta_PProdN_pack(x_5, x_51, x_17, x_18, x_19, x_20, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_56 = l_Lean_Meta_mkExpectedTypeHint(x_47, x_54, x_17, x_18, x_19, x_20, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = 0;
x_60 = 1;
x_61 = 1;
x_62 = l_Lean_Meta_mkLambdaFVars(x_16, x_57, x_59, x_60, x_59, x_61, x_17, x_18, x_19, x_20, x_58);
lean_dec(x_16);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Meta_mkLambdaFVars(x_15, x_63, x_59, x_60, x_59, x_61, x_17, x_18, x_19, x_20, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Meta_mkLambdaFVars(x_13, x_66, x_59, x_60, x_59, x_61, x_17, x_18, x_19, x_20, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_mkLambdaFVars(x_12, x_69, x_60, x_60, x_59, x_24, x_17, x_18, x_19, x_20, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_72, x_17, x_18, x_19, x_20, x_73);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_74, 1);
x_78 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__9;
x_79 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_78, x_17, x_18, x_19, x_20, x_77);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
uint8_t x_82; 
lean_free_object(x_74);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_79, 0);
lean_dec(x_83);
lean_ctor_set(x_79, 0, x_76);
return x_79;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
lean_dec(x_79);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
lean_inc(x_76);
x_87 = l_Lean_indentExpr(x_76);
x_88 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__11;
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_87);
lean_ctor_set(x_74, 0, x_88);
x_89 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_74);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_78, x_90, x_17, x_18, x_19, x_20, x_86);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
lean_ctor_set(x_91, 0, x_76);
return x_91;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_76);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_74, 0);
x_97 = lean_ctor_get(x_74, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_74);
x_98 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__9;
x_99 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_98, x_17, x_18, x_19, x_20, x_97);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_103 = x_99;
} else {
 lean_dec_ref(x_99);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
lean_dec(x_99);
lean_inc(x_96);
x_106 = l_Lean_indentExpr(x_96);
x_107 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__11;
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_98, x_110, x_17, x_18, x_19, x_20, x_105);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_96);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_115 = !lean_is_exclusive(x_71);
if (x_115 == 0)
{
return x_71;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_71, 0);
x_117 = lean_ctor_get(x_71, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_71);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_119 = !lean_is_exclusive(x_68);
if (x_119 == 0)
{
return x_68;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_68, 0);
x_121 = lean_ctor_get(x_68, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_68);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_123 = !lean_is_exclusive(x_65);
if (x_123 == 0)
{
return x_65;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_65, 0);
x_125 = lean_ctor_get(x_65, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_65);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_127 = !lean_is_exclusive(x_62);
if (x_127 == 0)
{
return x_62;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_62, 0);
x_129 = lean_ctor_get(x_62, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_62);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_131 = !lean_is_exclusive(x_56);
if (x_131 == 0)
{
return x_56;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_56, 0);
x_133 = lean_ctor_get(x_56, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_56);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_47);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_135 = !lean_is_exclusive(x_53);
if (x_135 == 0)
{
return x_53;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_53, 0);
x_137 = lean_ctor_get(x_53, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_53);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_47);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_5);
x_139 = !lean_is_exclusive(x_50);
if (x_139 == 0)
{
return x_50;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_50, 0);
x_141 = lean_ctor_get(x_50, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_50);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_2);
x_143 = !lean_is_exclusive(x_46);
if (x_143 == 0)
{
return x_46;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_46, 0);
x_145 = lean_ctor_get(x_46, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_46);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_26);
if (x_147 == 0)
{
return x_26;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_26, 0);
x_149 = lean_ctor_get(x_26, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_26);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_array_get_size(x_17);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_unsigned_to_nat(0u);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_1);
x_26 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__6(x_1, x_17, x_17, x_23, x_25, lean_box(0), x_24, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_1);
lean_inc(x_2);
x_29 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkAdmAnd), 9, 2);
lean_closure_set(x_29, 0, x_2);
lean_closure_set(x_29, 1, x_1);
x_30 = l_Lean_instInhabitedExpr;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_31 = l_Lean_Meta_PProdN_genMk___rarg(x_30, x_29, x_27, x_18, x_19, x_20, x_21, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5___closed__1;
lean_inc(x_3);
x_35 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(x_3, x_34);
x_36 = lean_mk_empty_array_with_capacity(x_3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_5);
x_37 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_5, x_3, x_25, lean_box(0), x_36, x_18, x_19, x_20, x_21, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Array_unzip___rarg(x_38);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Array_zip___rarg(x_35, x_41);
lean_dec(x_41);
lean_dec(x_35);
x_44 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___boxed), 21, 15);
lean_closure_set(x_44, 0, x_13);
lean_closure_set(x_44, 1, x_12);
lean_closure_set(x_44, 2, x_10);
lean_closure_set(x_44, 3, x_42);
lean_closure_set(x_44, 4, x_9);
lean_closure_set(x_44, 5, x_2);
lean_closure_set(x_44, 6, x_1);
lean_closure_set(x_44, 7, x_6);
lean_closure_set(x_44, 8, x_14);
lean_closure_set(x_44, 9, x_32);
lean_closure_set(x_44, 10, x_5);
lean_closure_set(x_44, 11, x_15);
lean_closure_set(x_44, 12, x_11);
lean_closure_set(x_44, 13, x_16);
lean_closure_set(x_44, 14, x_17);
x_45 = l_Lean_Meta_withLocalDeclsDND___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__11___rarg(x_30, x_43, x_44, x_18, x_19, x_20, x_21, x_39);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 0);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_37);
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
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_31);
if (x_50 == 0)
{
return x_31;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_31, 0);
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_31);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_26);
if (x_54 == 0)
{
return x_26;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_26, 0);
x_56 = lean_ctor_get(x_26, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_26);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("adm", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, lean_object* x_9, lean_object* x_10, size_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_20 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__2;
x_21 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_20, x_17, x_18, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__1___boxed), 9, 3);
lean_closure_set(x_24, 0, x_14);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_2);
x_25 = 0;
x_26 = 0;
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_1);
x_27 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(x_22, x_25, x_1, x_24, x_26, x_15, x_16, x_17, x_18, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_array_get_size(x_14);
x_31 = lean_mk_empty_array_with_capacity(x_30);
x_32 = lean_unsigned_to_nat(0u);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_31);
lean_inc(x_30);
x_33 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5(x_3, x_4, x_14, x_14, x_30, x_32, lean_box(0), x_31, x_15, x_16, x_17, x_18, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_get_size(x_34);
x_37 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__3;
x_38 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(x_36, x_37);
x_39 = l_Array_zip___rarg(x_38, x_34);
lean_dec(x_34);
lean_dec(x_38);
x_40 = lean_box_usize(x_8);
x_41 = lean_box_usize(x_11);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5___boxed), 22, 16);
lean_closure_set(x_42, 0, x_5);
lean_closure_set(x_42, 1, x_6);
lean_closure_set(x_42, 2, x_7);
lean_closure_set(x_42, 3, x_40);
lean_closure_set(x_42, 4, x_9);
lean_closure_set(x_42, 5, x_10);
lean_closure_set(x_42, 6, x_41);
lean_closure_set(x_42, 7, x_4);
lean_closure_set(x_42, 8, x_2);
lean_closure_set(x_42, 9, x_1);
lean_closure_set(x_42, 10, x_14);
lean_closure_set(x_42, 11, x_30);
lean_closure_set(x_42, 12, x_28);
lean_closure_set(x_42, 13, x_12);
lean_closure_set(x_42, 14, x_13);
lean_closure_set(x_42, 15, x_31);
x_43 = l_Lean_instInhabitedExpr;
x_44 = l_Lean_Meta_withLocalDeclsDND___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__11___rarg(x_43, x_39, x_42, x_15, x_16, x_17, x_18, x_35);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_27);
if (x_49 == 0)
{
return x_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("motive", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_array_get_size(x_1);
lean_inc(x_5);
x_14 = l_Lean_Elab_PartialFixpoint_CCPOProdProjs(x_13, x_5);
x_15 = lean_array_size(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__2(x_2, x_15, x_3, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_17);
x_20 = l_Lean_Meta_PProdN_pack(x_19, x_17, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_size(x_17);
lean_inc(x_17);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__3(x_19, x_23, x_3, x_17, x_8, x_9, x_10, x_11, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_get_size(x_25);
x_28 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__2;
x_29 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames(x_27, x_28);
x_30 = l_Array_zip___rarg(x_29, x_25);
lean_dec(x_25);
lean_dec(x_29);
x_31 = lean_box_usize(x_3);
x_32 = lean_box_usize(x_15);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___boxed), 19, 13);
lean_closure_set(x_33, 0, x_21);
lean_closure_set(x_33, 1, x_19);
lean_closure_set(x_33, 2, x_14);
lean_closure_set(x_33, 3, x_17);
lean_closure_set(x_33, 4, x_5);
lean_closure_set(x_33, 5, x_4);
lean_closure_set(x_33, 6, x_13);
lean_closure_set(x_33, 7, x_31);
lean_closure_set(x_33, 8, x_1);
lean_closure_set(x_33, 9, x_6);
lean_closure_set(x_33, 10, x_32);
lean_closure_set(x_33, 11, x_7);
lean_closure_set(x_33, 12, x_2);
x_34 = l_Lean_instInhabitedExpr;
x_35 = l_Lean_Meta_withLocalDeclsDND___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__11___rarg(x_34, x_30, x_33, x_8, x_9, x_10, x_11, x_26);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_20);
if (x_36 == 0)
{
return x_20;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_20, 0);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_20);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpected function body ", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_MessageData_ofExpr(x_1);
x_9 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(x_4, x_11, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_PProdN_stripProjs(x_13);
x_16 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_15);
x_17 = l_Lean_Meta_whnfUntil(x_15, x_16, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_MessageData_ofExpr(x_13);
x_21 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__2;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_24, x_6, x_7, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_13);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = l_Lean_Expr_cleanupAnnotations(x_27);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_2);
x_30 = lean_box(0);
x_31 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8(x_15, x_30, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = l_Lean_Expr_appArg(x_28, lean_box(0));
x_33 = l_Lean_Expr_appFnCleanup(x_28, lean_box(0));
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8(x_15, x_35, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = l_Lean_Expr_appArg(x_33, lean_box(0));
x_38 = l_Lean_Expr_appFnCleanup(x_33, lean_box(0));
x_39 = l_Lean_Expr_isApp(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
x_40 = lean_box(0);
x_41 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8(x_15, x_40, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Lean_Expr_appArg(x_38, lean_box(0));
x_43 = l_Lean_Expr_appFnCleanup(x_38, lean_box(0));
x_44 = l_Lean_Expr_isApp(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
x_45 = lean_box(0);
x_46 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8(x_15, x_45, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Lean_Expr_appArg(x_43, lean_box(0));
x_48 = l_Lean_Expr_appFnCleanup(x_43, lean_box(0));
x_49 = l_Lean_Expr_isConstOf(x_48, x_16);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
x_50 = lean_box(0);
x_51 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8(x_15, x_50, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_51;
}
else
{
lean_object* x_52; 
lean_dec(x_15);
x_52 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7(x_2, x_4, x_3, x_47, x_42, x_37, x_32, x_6, x_7, x_8, x_9, x_26);
return x_52;
}
}
}
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_17);
if (x_53 == 0)
{
return x_17;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_17, 0);
x_55 = lean_ctor_get(x_17, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_17);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_12);
if (x_57 == 0)
{
return x_12;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_12, 0);
x_59 = lean_ctor_get(x_12, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_12);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" is not defined by partial_fixpoint", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_elimOptParam___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_elimOptParam___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__6;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__8;
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___closed__1;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fixpoint_induct", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_13 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1;
lean_inc(x_1);
x_14 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_12, x_13, x_11, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = l_Lean_MessageData_ofName(x_1);
x_16 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_15);
lean_ctor_set(x_7, 0, x_16);
x_17 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__3;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_18, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_array_size(x_22);
x_24 = 0;
x_25 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1(x_23, x_24, x_22, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_instInhabitedDefinitionVal;
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get(x_28, x_26, x_29);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_21, 3);
lean_inc(x_32);
lean_dec(x_21);
x_33 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___boxed__const__1;
lean_inc(x_31);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___boxed), 10, 3);
lean_closure_set(x_34, 0, x_31);
lean_closure_set(x_34, 1, x_26);
lean_closure_set(x_34, 2, x_33);
x_35 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_36 = l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg(x_31, x_32, x_34, x_35, x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_37);
x_39 = lean_infer_type(x_37, x_2, x_3, x_4, x_5, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4;
x_43 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5;
lean_inc(x_5);
lean_inc(x_4);
x_44 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_40, x_42, x_43, x_4, x_5, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9;
lean_inc(x_45);
x_49 = l_Lean_CollectLevelParams_main(x_45, x_48);
x_50 = lean_ctor_get(x_49, 2);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_30, 0);
lean_inc(x_51);
lean_dec(x_30);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__21(x_50, x_52, x_47);
lean_dec(x_50);
x_54 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__11;
x_55 = l_Lean_Name_append(x_1, x_54);
lean_inc(x_55);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_56, 2, x_45);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_47);
lean_ctor_set(x_7, 0, x_55);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_37);
lean_ctor_set(x_57, 2, x_7);
lean_ctor_set_tag(x_14, 2);
lean_ctor_set(x_14, 0, x_57);
x_58 = l_Lean_addDecl(x_14, x_4, x_5, x_46);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_37);
lean_dec(x_30);
lean_free_object(x_14);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_44);
if (x_59 == 0)
{
return x_44;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_44, 0);
x_61 = lean_ctor_get(x_44, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_44);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_37);
lean_dec(x_30);
lean_free_object(x_14);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_39);
if (x_63 == 0)
{
return x_39;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_39, 0);
x_65 = lean_ctor_get(x_39, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_39);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_30);
lean_free_object(x_14);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_36);
if (x_67 == 0)
{
return x_36;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_36, 0);
x_69 = lean_ctor_get(x_36, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_36);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_free_object(x_14);
lean_dec(x_21);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_25);
if (x_71 == 0)
{
return x_25;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_25, 0);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_25);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_14, 0);
lean_inc(x_75);
lean_dec(x_14);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
x_77 = lean_array_size(x_76);
x_78 = 0;
x_79 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1(x_77, x_78, x_76, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_instInhabitedDefinitionVal;
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_array_get(x_82, x_80, x_83);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_75, 3);
lean_inc(x_86);
lean_dec(x_75);
x_87 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___boxed__const__1;
lean_inc(x_85);
x_88 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___boxed), 10, 3);
lean_closure_set(x_88, 0, x_85);
lean_closure_set(x_88, 1, x_80);
lean_closure_set(x_88, 2, x_87);
x_89 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_90 = l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg(x_85, x_86, x_88, x_89, x_2, x_3, x_4, x_5, x_81);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_91);
x_93 = lean_infer_type(x_91, x_2, x_3, x_4, x_5, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4;
x_97 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5;
lean_inc(x_5);
lean_inc(x_4);
x_98 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_94, x_96, x_97, x_4, x_5, x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_box(0);
x_102 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9;
lean_inc(x_99);
x_103 = l_Lean_CollectLevelParams_main(x_99, x_102);
x_104 = lean_ctor_get(x_103, 2);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_84, 0);
lean_inc(x_105);
lean_dec(x_84);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__21(x_104, x_106, x_101);
lean_dec(x_104);
x_108 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__11;
x_109 = l_Lean_Name_append(x_1, x_108);
lean_inc(x_109);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
lean_ctor_set(x_110, 2, x_99);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_101);
lean_ctor_set(x_7, 0, x_109);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_91);
lean_ctor_set(x_111, 2, x_7);
x_112 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_addDecl(x_112, x_4, x_5, x_100);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_91);
lean_dec(x_84);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_114 = lean_ctor_get(x_98, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_98, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_116 = x_98;
} else {
 lean_dec_ref(x_98);
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
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_91);
lean_dec(x_84);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_118 = lean_ctor_get(x_93, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_93, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_120 = x_93;
} else {
 lean_dec_ref(x_93);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_84);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_ctor_get(x_90, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_90, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_124 = x_90;
} else {
 lean_dec_ref(x_90);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_75);
lean_free_object(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_ctor_get(x_79, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_79, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_128 = x_79;
} else {
 lean_dec_ref(x_79);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_7, 0);
x_131 = lean_ctor_get(x_7, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_7);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_134 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1;
lean_inc(x_1);
x_135 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_133, x_134, x_132, x_1);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_136 = l_Lean_MessageData_ofName(x_1);
x_137 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__3;
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_140, x_2, x_3, x_4, x_5, x_131);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; size_t x_145; size_t x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_135, 0);
lean_inc(x_142);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_143 = x_135;
} else {
 lean_dec_ref(x_135);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
x_145 = lean_array_size(x_144);
x_146 = 0;
x_147 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1(x_145, x_146, x_144, x_2, x_3, x_4, x_5, x_131);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_instInhabitedDefinitionVal;
x_151 = lean_unsigned_to_nat(0u);
x_152 = lean_array_get(x_150, x_148, x_151);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_142, 3);
lean_inc(x_154);
lean_dec(x_142);
x_155 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___boxed__const__1;
lean_inc(x_153);
x_156 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___boxed), 10, 3);
lean_closure_set(x_156, 0, x_153);
lean_closure_set(x_156, 1, x_148);
lean_closure_set(x_156, 2, x_155);
x_157 = 0;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_158 = l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg(x_153, x_154, x_156, x_157, x_2, x_3, x_4, x_5, x_149);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_159);
x_161 = lean_infer_type(x_159, x_2, x_3, x_4, x_5, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4;
x_165 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5;
lean_inc(x_5);
lean_inc(x_4);
x_166 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_162, x_164, x_165, x_4, x_5, x_163);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_box(0);
x_170 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9;
lean_inc(x_167);
x_171 = l_Lean_CollectLevelParams_main(x_167, x_170);
x_172 = lean_ctor_get(x_171, 2);
lean_inc(x_172);
lean_dec(x_171);
x_173 = lean_ctor_get(x_152, 0);
lean_inc(x_173);
lean_dec(x_152);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__21(x_172, x_174, x_169);
lean_dec(x_172);
x_176 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__11;
x_177 = l_Lean_Name_append(x_1, x_176);
lean_inc(x_177);
x_178 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_178, 2, x_167);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_169);
x_180 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_159);
lean_ctor_set(x_180, 2, x_179);
if (lean_is_scalar(x_143)) {
 x_181 = lean_alloc_ctor(2, 1, 0);
} else {
 x_181 = x_143;
 lean_ctor_set_tag(x_181, 2);
}
lean_ctor_set(x_181, 0, x_180);
x_182 = l_Lean_addDecl(x_181, x_4, x_5, x_168);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_159);
lean_dec(x_152);
lean_dec(x_143);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_183 = lean_ctor_get(x_166, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_166, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_185 = x_166;
} else {
 lean_dec_ref(x_166);
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
lean_dec(x_159);
lean_dec(x_152);
lean_dec(x_143);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_187 = lean_ctor_get(x_161, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_161, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_189 = x_161;
} else {
 lean_dec_ref(x_161);
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
lean_dec(x_152);
lean_dec(x_143);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = lean_ctor_get(x_158, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_158, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_193 = x_158;
} else {
 lean_dec_ref(x_158);
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
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_147, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_147, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_197 = x_147;
} else {
 lean_dec_ref(x_147);
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
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot derive fixpoint induction principle (please report this issue)\n", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_indentD(x_1);
x_3 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__2;
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_deriveInduction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Elab_PartialFixpoint_deriveInduction___closed__1;
x_9 = l_Lean_Meta_mapErrorImp___rarg(x_7, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__14(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_16 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_16 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___boxed(lean_object** _args) {
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
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_21 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_22 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17(x_20, x_2, x_3, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_10);
lean_dec(x_5);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__18(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__19(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__21(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___boxed(lean_object** _args) {
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
lean_object* x_22; 
x_22 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5___boxed(lean_object** _args) {
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
lean_object* x_22 = _args[21];
_start:
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_24 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_25 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5(x_1, x_2, x_3, x_23, x_5, x_6, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_8);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___boxed(lean_object** _args) {
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
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_21 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_22 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_20, x_9, x_10, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_3);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_isInductName___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_isInductName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_isInductName___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_isInductName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_PartialFixpoint_isInductName___closed__1;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isInductName(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__10;
x_6 = lean_string_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_box(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_10 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1;
lean_inc(x_3);
x_11 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_9, x_10, x_1, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = l_Lean_Elab_PartialFixpoint_isInductName___closed__2;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_instInhabitedName;
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get(x_15, x_14, x_16);
lean_dec(x_14);
x_18 = lean_name_eq(x_3, x_17);
lean_dec(x_17);
lean_dec(x_3);
x_19 = lean_box(x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_20 = 0;
x_21 = lean_box(x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isInductName___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_PartialFixpoint_isInductName___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__2() {
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
static uint64_t _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__3() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__2;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__8() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__7;
x_3 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__6;
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
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__5;
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__2;
x_4 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__3;
x_5 = 0;
x_6 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__9;
x_7 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___closed__1;
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
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__5;
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
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__5;
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
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__5;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__11;
x_3 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__12;
x_4 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__8;
x_5 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__13;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__1;
lean_inc(x_1);
x_11 = l_Lean_Elab_PartialFixpoint_isInductName(x_9, x_1);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_5);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_apply_4(x_10, x_13, x_2, x_3, x_8);
return x_14;
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_5);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__14;
x_17 = lean_st_mk_ref(x_16, x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__10;
lean_inc(x_18);
x_21 = l_Lean_Elab_PartialFixpoint_deriveInduction(x_15, x_20, x_18, x_2, x_3, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_18, x_22);
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = 1;
x_27 = lean_box(x_26);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
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
lean_dec(x_18);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; lean_object* x_37; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = 0;
x_37 = lean_box(x_36);
lean_ctor_set(x_5, 0, x_37);
return x_5;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_5, 0);
x_39 = lean_ctor_get(x_5, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_5);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__1;
lean_inc(x_1);
x_42 = l_Lean_Elab_PartialFixpoint_isInductName(x_40, x_1);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = lean_apply_4(x_41, x_44, x_2, x_3, x_39);
return x_45;
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
lean_dec(x_1);
x_47 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__14;
x_48 = lean_st_mk_ref(x_47, x_39);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__10;
lean_inc(x_49);
x_52 = l_Lean_Elab_PartialFixpoint_deriveInduction(x_46, x_51, x_49, x_2, x_3, x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_st_ref_get(x_49, x_53);
lean_dec(x_49);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = 1;
x_58 = lean_box(x_57);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_49);
x_60 = lean_ctor_get(x_52, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_62 = x_52;
} else {
 lean_dec_ref(x_52);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = 0;
x_65 = lean_box(x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_39);
return x_66;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_isInductName), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__1;
x_3 = l_Lean_registerReservedNamePredicate(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__2;
x_6 = l_Lean_registerReservedNameAction(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Expr_isLambda(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lean_Expr_bindingBody_x21(x_1);
lean_dec(x_1);
x_1 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instCCPOPi", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__2;
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_7 = l_Lean_Expr_isLambda(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = l_Lean_Expr_bindingBody_x21(x_6);
lean_dec(x_6);
x_1 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instCCPOOption", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__2;
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Expr_isAppOfArity(x_9, x_10, x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_box(0);
x_2 = x_15;
x_4 = x_16;
goto _start;
}
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_array_get_size(x_1);
x_4 = l_Lean_Elab_PartialFixpoint_CCPOProdProjs(x_3, x_2);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1___closed__1;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_5, x_5);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1___closed__1;
return x_10;
}
else
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_13 = lean_box(0);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4(x_4, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isOptionFixpoint: unexpected value ", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PartialFixpoint.isOptionFixpoint", 42, 42);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_expr_dbg_to_string(x_1);
x_4 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__3;
x_7 = lean_string_append(x_5, x_6);
x_8 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__6;
x_9 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__2;
x_10 = lean_unsigned_to_nat(189u);
x_11 = lean_unsigned_to_nat(48u);
x_12 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_7);
lean_dec(x_7);
x_13 = l_panic___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__1(x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defnInfo.hasValue\n  ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__3;
x_2 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__6;
x_2 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__2;
x_3 = lean_unsigned_to_nat(186u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__2;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_isOptionFixpoint(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_4 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_3, x_4, x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Lean_instInhabitedName;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_8, x_10);
x_12 = lean_name_eq(x_2, x_11);
lean_dec(x_11);
lean_dec(x_2);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_7, 2);
lean_inc(x_14);
lean_dec(x_7);
x_15 = l_Lean_Environment_find_x3f(x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_8);
x_16 = 0;
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 0;
x_19 = l_Lean_ConstantInfo_hasValue(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_8);
x_20 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__3;
x_21 = l_panic___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__1(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_21);
x_23 = 1;
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = l_Lean_ConstantInfo_value_x21(x_17, x_18);
lean_dec(x_17);
x_25 = l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__2(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_26);
x_27 = l_Lean_Expr_cleanupAnnotations(x_26);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_8);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2(x_26, x_29);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_30);
x_32 = 1;
return x_32;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Expr_appFnCleanup(x_27, lean_box(0));
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_8);
x_35 = lean_box(0);
x_36 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2(x_26, x_35);
lean_dec(x_26);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = 0;
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_36);
x_38 = 1;
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Expr_appFnCleanup(x_33, lean_box(0));
x_40 = l_Lean_Expr_isApp(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_8);
x_41 = lean_box(0);
x_42 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2(x_26, x_41);
lean_dec(x_26);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = 0;
return x_43;
}
else
{
uint8_t x_44; 
lean_dec(x_42);
x_44 = 1;
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Lean_Expr_appArg(x_39, lean_box(0));
x_46 = l_Lean_Expr_appFnCleanup(x_39, lean_box(0));
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_8);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2(x_26, x_48);
lean_dec(x_26);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = 0;
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_49);
x_51 = 1;
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = l_Lean_Expr_appFnCleanup(x_46, lean_box(0));
x_53 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__2;
x_54 = l_Lean_Expr_isConstOf(x_52, x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_45);
lean_dec(x_8);
x_55 = lean_box(0);
x_56 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2(x_26, x_55);
lean_dec(x_26);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = 0;
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_56);
x_58 = 1;
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_26);
x_59 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1(x_8, x_45);
lean_dec(x_8);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = 0;
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_59);
x_61 = 1;
return x_61;
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isOptionFixpoint___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("partial_correctness", 19, 19);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint(x_1, x_3);
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("admissible_pi_apply", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_8, x_7);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_17 = lean_array_uget(x_6, x_8);
lean_inc(x_1);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_1);
x_19 = lean_array_mk(x_18);
x_20 = 0;
x_21 = 1;
x_22 = 1;
x_23 = l_Lean_Meta_mkLambdaFVars(x_19, x_9, x_20, x_21, x_20, x_22, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
lean_inc(x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
lean_inc(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_2);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_mk(x_31);
x_33 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__2;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_34 = l_Lean_Meta_mkAppOptM(x_33, x_32, x_10, x_11, x_12, x_13, x_25);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = 1;
x_38 = lean_usize_add(x_8, x_37);
x_8 = x_38;
x_9 = x_35;
x_14 = x_36;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("admissible_eq_some", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__1;
x_4 = l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("admissible_pi", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_mkAppN(x_1, x_2);
lean_inc(x_2);
x_10 = lean_array_pop(x_2);
x_11 = l_Lean_instInhabitedExpr;
x_12 = l_Array_back_x21___rarg(x_11, x_2);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_14);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_mk(x_15);
x_17 = l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__3;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_mkAppM(x_17, x_16, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_mk(x_14);
x_22 = 0;
x_23 = 1;
x_24 = 1;
x_25 = l_Lean_Meta_mkLambdaFVars(x_21, x_19, x_22, x_23, x_22, x_24, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_mk(x_34);
x_36 = l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__5;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_37 = l_Lean_Meta_mkAppOptM(x_36, x_35, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_box(0);
x_41 = l_Array_reverse___rarg(x_10);
x_42 = lean_array_size(x_41);
x_43 = 0;
x_44 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1(x_13, x_28, x_13, x_40, x_41, x_41, x_42, x_43, x_38, x_4, x_5, x_6, x_7, x_39);
lean_dec(x_41);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_37);
if (x_53 == 0)
{
return x_37;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_25);
if (x_57 == 0)
{
return x_25;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_25, 0);
x_59 = lean_ctor_get(x_25, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_25);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
return x_18;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_18, 0);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_18);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___boxed), 8, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = 0;
x_12 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_8, x_10, x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_16, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_1, x_13, x_16, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__1;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_array_push(x_1, x_2);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1___closed__1;
x_10 = 0;
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Meta_mkForallFVars(x_8, x_9, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
return x_13;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("r", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__2;
x_9 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_8, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1___boxed), 7, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = 0;
x_14 = 0;
x_15 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(x_10, x_13, x_2, x_12, x_14, x_3, x_4, x_5, x_6, x_11);
return x_15;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected `Option`, got:", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_indentExpr(x_1);
x_9 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = l_Lean_Expr_cleanupAnnotations(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3(x_9, x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = l_Lean_Expr_appArg(x_11, lean_box(0));
x_16 = l_Lean_Expr_appFnCleanup(x_11, lean_box(0));
x_17 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__4___closed__1;
x_18 = l_Lean_Expr_isConstOf(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3(x_9, x_19, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_9);
x_21 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2(x_1, x_15, x_3, x_4, x_5, x_6, x_10);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__4), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___closed__1;
x_15 = 0;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_11, x_14, x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_13, x_2, x_17);
x_2 = x_20;
x_3 = x_21;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("motive_", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_4, x_15);
lean_dec(x_4);
x_17 = lean_array_fget(x_3, x_5);
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_dec_eq(x_18, x_15);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__12___lambda__1___boxed), 7, 1);
lean_closure_set(x_20, 0, x_17);
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
lean_inc(x_21);
x_22 = l___private_Init_Data_Repr_0__Nat_reprFast(x_21);
x_23 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__3;
x_26 = lean_string_append(x_24, x_25);
x_27 = lean_box(0);
x_28 = l_Lean_Name_str___override(x_27, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
x_30 = lean_array_push(x_7, x_29);
x_4 = x_16;
x_5 = x_21;
x_6 = lean_box(0);
x_7 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__2;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_20);
x_34 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_35 = lean_array_push(x_7, x_33);
x_4 = x_16;
x_5 = x_34;
x_6 = lean_box(0);
x_7 = x_35;
goto _start;
}
}
else
{
lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_4);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("some", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__1;
x_2 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_3);
x_10 = lean_array_pop(x_3);
x_11 = l_Lean_instInhabitedExpr;
x_12 = l_Array_back_x21___rarg(x_11, x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_mk(x_14);
x_16 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_mkAppM(x_16, x_15, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_1);
x_20 = l_Lean_mkAppN(x_1, x_10);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Meta_mkEq(x_20, x_18, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_mkAppN(x_2, x_3);
x_25 = l_Lean_mkArrow(x_22, x_24, x_7, x_8, x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
x_29 = 0;
x_30 = 1;
x_31 = 1;
x_32 = l_Lean_Meta_mkForallFVars(x_3, x_27, x_29, x_30, x_31, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_3);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 0, x_1);
x_35 = lean_array_mk(x_25);
x_36 = l_Lean_Meta_mkLambdaFVars(x_35, x_33, x_29, x_30, x_29, x_31, x_5, x_6, x_7, x_8, x_34);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_free_object(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = 0;
x_44 = 1;
x_45 = 1;
x_46 = l_Lean_Meta_mkForallFVars(x_3, x_41, x_43, x_44, x_45, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_3);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_13);
x_50 = lean_array_mk(x_49);
x_51 = l_Lean_Meta_mkLambdaFVars(x_50, x_47, x_43, x_44, x_43, x_45, x_5, x_6, x_7, x_8, x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_54 = x_46;
} else {
 lean_dec_ref(x_46);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_21);
if (x_56 == 0)
{
return x_21;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_21, 0);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_21);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_17);
if (x_60 == 0)
{
return x_17;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_17, 0);
x_62 = lean_ctor_get(x_17, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_17);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___boxed), 9, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
x_12 = 0;
x_13 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_9, x_11, x_12, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_4, x_15);
lean_dec(x_4);
x_17 = lean_array_fget(x_3, x_5);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__2;
x_19 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_18, x_10, x_11, x_12);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_instInhabitedExpr;
x_23 = lean_array_get(x_22, x_1, x_5);
x_24 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__2), 7, 1);
lean_closure_set(x_24, 0, x_17);
x_25 = 0;
x_26 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_27 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_Simp_Arith_withAbstractAtoms_go___spec__1___rarg(x_20, x_25, x_23, x_24, x_26, x_8, x_9, x_10, x_11, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_31 = lean_array_push(x_7, x_28);
x_4 = x_16;
x_5 = x_30;
x_6 = lean_box(0);
x_7 = x_31;
x_12 = x_29;
goto _start;
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
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__6(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Elab_PartialFixpoint_mkOptionAdm(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_13, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_6);
if (x_8 == 0)
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
else
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = l_Array_contains___at_Lean_registerInternalExceptionId___spec__1(x_1, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_3);
x_2 = x_12;
x_3 = x_15;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("complete body of partial correctness principle:", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_get_size(x_5);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4(x_1, x_5, x_5, x_11, x_13, lean_box(0), x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l_Array_append___rarg(x_2, x_15);
lean_dec(x_15);
x_18 = lean_array_size(x_17);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__5(x_18, x_3, x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Lean_Meta_mkAppOptM(x_4, x_19, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_size(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__6(x_23, x_3, x_5, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_mkAppN(x_21, x_25);
lean_dec(x_25);
x_28 = 0;
x_29 = 1;
x_30 = 1;
x_31 = l_Lean_Meta_mkLambdaFVars(x_5, x_27, x_28, x_29, x_28, x_30, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 0;
x_35 = l_Lean_Meta_mkLambdaFVars(x_2, x_32, x_29, x_29, x_28, x_34, x_6, x_7, x_8, x_9, x_33);
lean_dec(x_2);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_36, x_6, x_7, x_8, x_9, x_37);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__9;
x_43 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_42, x_6, x_7, x_8, x_9, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; 
lean_free_object(x_38);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_43, 0);
lean_dec(x_47);
lean_ctor_set(x_43, 0, x_40);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
lean_inc(x_40);
x_51 = l_Lean_indentExpr(x_40);
x_52 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__2;
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_51);
lean_ctor_set(x_38, 0, x_52);
x_53 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_38);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_42, x_54, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_40);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_40);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_60 = lean_ctor_get(x_38, 0);
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_38);
x_62 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__9;
x_63 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_62, x_6, x_7, x_8, x_9, x_61);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_67 = x_63;
} else {
 lean_dec_ref(x_63);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_60);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
lean_inc(x_60);
x_70 = l_Lean_indentExpr(x_60);
x_71 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__2;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_62, x_74, x_6, x_7, x_8, x_9, x_69);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_60);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_79 = !lean_is_exclusive(x_35);
if (x_79 == 0)
{
return x_35;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_35, 0);
x_81 = lean_ctor_get(x_35, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_35);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_31);
if (x_83 == 0)
{
return x_31;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_31, 0);
x_85 = lean_ctor_get(x_31, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_31);
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
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_24);
if (x_87 == 0)
{
return x_24;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_24, 0);
x_89 = lean_ctor_get(x_24, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_24);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_20);
if (x_91 == 0)
{
return x_20;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_20, 0);
x_93 = lean_ctor_get(x_20, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_20);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_14);
if (x_95 == 0)
{
return x_14;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_14, 0);
x_97 = lean_ctor_get(x_14, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_14);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_array_size(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__1(x_4, x_11, x_2, x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_size(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_13);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2(x_15, x_2, x_13, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_get_size(x_17);
x_20 = lean_mk_empty_array_with_capacity(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3(x_1, x_17, x_17, x_19, x_21, lean_box(0), x_20, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_17);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box_usize(x_2);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___boxed), 10, 4);
lean_closure_set(x_26, 0, x_13);
lean_closure_set(x_26, 1, x_4);
lean_closure_set(x_26, 2, x_25);
lean_closure_set(x_26, 3, x_3);
x_27 = l_Lean_instInhabitedExpr;
x_28 = l_Lean_Meta_withLocalDeclsD___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__13___rarg(x_27, x_23, x_26, x_6, x_7, x_8, x_9, x_24);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_betaReduce___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_betaReduce___lambda__2___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_14 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1;
lean_inc(x_1);
x_15 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_13, x_14, x_12, x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_16 = l_Lean_MessageData_ofName(x_1);
x_17 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_17);
x_18 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__3;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_19, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_array_size(x_23);
x_25 = 0;
x_26 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1(x_24, x_25, x_23, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_instInhabitedDefinitionVal;
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get(x_29, x_27, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_22, 3);
lean_inc(x_33);
lean_dec(x_22);
x_34 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___boxed__const__1;
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__2___boxed), 10, 3);
lean_closure_set(x_35, 0, x_27);
lean_closure_set(x_35, 1, x_34);
lean_closure_set(x_35, 2, x_2);
x_36 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg(x_32, x_33, x_35, x_36, x_3, x_4, x_5, x_6, x_28);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_38);
x_40 = lean_infer_type(x_38, x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4;
x_44 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5;
lean_inc(x_6);
lean_inc(x_5);
x_45 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_41, x_43, x_44, x_5, x_6, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__1;
x_49 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__2;
lean_inc(x_6);
lean_inc(x_5);
x_50 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_46, x_48, x_49, x_5, x_6, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(0);
x_54 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9;
lean_inc(x_51);
x_55 = l_Lean_CollectLevelParams_main(x_51, x_54);
x_56 = lean_ctor_get(x_55, 2);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get(x_31, 0);
lean_inc(x_57);
lean_dec(x_31);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__7(x_56, x_58, x_53);
lean_dec(x_56);
x_60 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__3;
x_61 = l_Lean_Name_append(x_1, x_60);
lean_inc(x_61);
x_62 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_51);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_53);
lean_ctor_set(x_8, 0, x_61);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_38);
lean_ctor_set(x_63, 2, x_8);
lean_ctor_set_tag(x_15, 2);
lean_ctor_set(x_15, 0, x_63);
x_64 = l_Lean_addDecl(x_15, x_5, x_6, x_52);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_38);
lean_dec(x_31);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_50);
if (x_65 == 0)
{
return x_50;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_50, 0);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_50);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_38);
lean_dec(x_31);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_45);
if (x_69 == 0)
{
return x_45;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_45, 0);
x_71 = lean_ctor_get(x_45, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_45);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_38);
lean_dec(x_31);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_40);
if (x_73 == 0)
{
return x_40;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_40, 0);
x_75 = lean_ctor_get(x_40, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_40);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_31);
lean_free_object(x_15);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_37);
if (x_77 == 0)
{
return x_37;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_37, 0);
x_79 = lean_ctor_get(x_37, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_37);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_free_object(x_15);
lean_dec(x_22);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_26);
if (x_81 == 0)
{
return x_26;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_26, 0);
x_83 = lean_ctor_get(x_26, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_26);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_15, 0);
lean_inc(x_85);
lean_dec(x_15);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_array_size(x_86);
x_88 = 0;
x_89 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1(x_87, x_88, x_86, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_instInhabitedDefinitionVal;
x_93 = lean_unsigned_to_nat(0u);
x_94 = lean_array_get(x_92, x_90, x_93);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
x_96 = lean_ctor_get(x_85, 3);
lean_inc(x_96);
lean_dec(x_85);
x_97 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___boxed__const__1;
x_98 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__2___boxed), 10, 3);
lean_closure_set(x_98, 0, x_90);
lean_closure_set(x_98, 1, x_97);
lean_closure_set(x_98, 2, x_2);
x_99 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_100 = l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg(x_95, x_96, x_98, x_99, x_3, x_4, x_5, x_6, x_91);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_101);
x_103 = lean_infer_type(x_101, x_3, x_4, x_5, x_6, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4;
x_107 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5;
lean_inc(x_6);
lean_inc(x_5);
x_108 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_104, x_106, x_107, x_5, x_6, x_105);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__1;
x_112 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__2;
lean_inc(x_6);
lean_inc(x_5);
x_113 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_109, x_111, x_112, x_5, x_6, x_110);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_box(0);
x_117 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9;
lean_inc(x_114);
x_118 = l_Lean_CollectLevelParams_main(x_114, x_117);
x_119 = lean_ctor_get(x_118, 2);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_ctor_get(x_94, 0);
lean_inc(x_120);
lean_dec(x_94);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__7(x_119, x_121, x_116);
lean_dec(x_119);
x_123 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__3;
x_124 = l_Lean_Name_append(x_1, x_123);
lean_inc(x_124);
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_122);
lean_ctor_set(x_125, 2, x_114);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_116);
lean_ctor_set(x_8, 0, x_124);
x_126 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_101);
lean_ctor_set(x_126, 2, x_8);
x_127 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = l_Lean_addDecl(x_127, x_5, x_6, x_115);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_101);
lean_dec(x_94);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_129 = lean_ctor_get(x_113, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_113, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_131 = x_113;
} else {
 lean_dec_ref(x_113);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_101);
lean_dec(x_94);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_133 = lean_ctor_get(x_108, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_108, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_135 = x_108;
} else {
 lean_dec_ref(x_108);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_101);
lean_dec(x_94);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_137 = lean_ctor_get(x_103, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_103, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_139 = x_103;
} else {
 lean_dec_ref(x_103);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_94);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_141 = lean_ctor_get(x_100, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_100, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_143 = x_100;
} else {
 lean_dec_ref(x_100);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_85);
lean_free_object(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_ctor_get(x_89, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_89, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_147 = x_89;
} else {
 lean_dec_ref(x_89);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = lean_ctor_get(x_8, 0);
x_150 = lean_ctor_get(x_8, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_8);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
lean_dec(x_149);
x_152 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_153 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1;
lean_inc(x_1);
x_154 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_152, x_153, x_151, x_1);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_2);
x_155 = l_Lean_MessageData_ofName(x_1);
x_156 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
x_158 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__3;
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_159, x_3, x_4, x_5, x_6, x_150);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; size_t x_164; size_t x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_154, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_162 = x_154;
} else {
 lean_dec_ref(x_154);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
x_164 = lean_array_size(x_163);
x_165 = 0;
x_166 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__1(x_164, x_165, x_163, x_3, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = l_Lean_instInhabitedDefinitionVal;
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_array_get(x_169, x_167, x_170);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_161, 3);
lean_inc(x_173);
lean_dec(x_161);
x_174 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___boxed__const__1;
x_175 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__2___boxed), 10, 3);
lean_closure_set(x_175, 0, x_167);
lean_closure_set(x_175, 1, x_174);
lean_closure_set(x_175, 2, x_2);
x_176 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_177 = l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__20___rarg(x_172, x_173, x_175, x_176, x_3, x_4, x_5, x_6, x_168);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_178);
x_180 = lean_infer_type(x_178, x_3, x_4, x_5, x_6, x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4;
x_184 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5;
lean_inc(x_6);
lean_inc(x_5);
x_185 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_181, x_183, x_184, x_5, x_6, x_182);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__1;
x_189 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__2;
lean_inc(x_6);
lean_inc(x_5);
x_190 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_186, x_188, x_189, x_5, x_6, x_187);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_box(0);
x_194 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9;
lean_inc(x_191);
x_195 = l_Lean_CollectLevelParams_main(x_191, x_194);
x_196 = lean_ctor_get(x_195, 2);
lean_inc(x_196);
lean_dec(x_195);
x_197 = lean_ctor_get(x_171, 0);
lean_inc(x_197);
lean_dec(x_171);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__7(x_196, x_198, x_193);
lean_dec(x_196);
x_200 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__3;
x_201 = l_Lean_Name_append(x_1, x_200);
lean_inc(x_201);
x_202 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_199);
lean_ctor_set(x_202, 2, x_191);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_193);
x_204 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_178);
lean_ctor_set(x_204, 2, x_203);
if (lean_is_scalar(x_162)) {
 x_205 = lean_alloc_ctor(2, 1, 0);
} else {
 x_205 = x_162;
 lean_ctor_set_tag(x_205, 2);
}
lean_ctor_set(x_205, 0, x_204);
x_206 = l_Lean_addDecl(x_205, x_5, x_6, x_192);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_178);
lean_dec(x_171);
lean_dec(x_162);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_207 = lean_ctor_get(x_190, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_190, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_209 = x_190;
} else {
 lean_dec_ref(x_190);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_178);
lean_dec(x_171);
lean_dec(x_162);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_211 = lean_ctor_get(x_185, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_185, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_213 = x_185;
} else {
 lean_dec_ref(x_185);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_178);
lean_dec(x_171);
lean_dec(x_162);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_215 = lean_ctor_get(x_180, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_180, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_217 = x_180;
} else {
 lean_dec_ref(x_180);
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
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_171);
lean_dec(x_162);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_219 = lean_ctor_get(x_177, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_177, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_221 = x_177;
} else {
 lean_dec_ref(x_177);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_219);
lean_ctor_set(x_222, 1, x_220);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_ctor_get(x_166, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_166, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_225 = x_166;
} else {
 lean_dec_ref(x_166);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot derive partial correctness theorem (please report this issue)\n", 69, 69);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_indentD(x_1);
x_3 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__2;
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4;
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3), 7, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5___closed__1;
x_11 = l_Lean_Meta_mapErrorImp___rarg(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__11;
lean_inc(x_1);
x_8 = l_Lean_Name_append(x_1, x_7);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
x_13 = l_Lean_Environment_contains(x_12, x_8);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Elab_PartialFixpoint_deriveInduction(x_1, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5(x_1, x_8, x_15, x_2, x_3, x_4, x_5, x_16);
lean_dec(x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5(x_1, x_8, x_22, x_2, x_3, x_4, x_5, x_11);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__6(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterTR_loop___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__14;
x_7 = lean_st_mk_ref(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__10;
lean_inc(x_8);
x_11 = l_Lean_Elab_PartialFixpoint_derivePartialCorrectness(x_1, x_10, x_8, x_3, x_4, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_8, x_12);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = 0;
x_17 = lean_box(x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint(x_10, x_1);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_14 = lean_box(0);
x_15 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__1(x_1, x_14, x_3, x_4, x_9);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_Lean_Elab_PartialFixpoint_isOptionFixpoint(x_18, x_1);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__1(x_1, x_23, x_3, x_4, x_17);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1;
x_8 = lean_string_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__2(x_5, x_12, x_2, x_3, x_4);
return x_13;
}
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__3), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__1;
x_3 = l_Lean_registerReservedNamePredicate(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__2;
x_6 = l_Lean_registerReservedNameAction(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__2;
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__4;
x_2 = l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__5;
x_2 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PreDefinition", 13, 13);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__6;
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PartialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__8;
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Induction", 9, 9);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__10;
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__12;
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__14;
x_2 = lean_unsigned_to_nat(4828u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__9;
x_3 = 0;
x_4 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__15;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Injective(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_ArgsPacker(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_PProdN(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_ElimInfo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Induction(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherApp_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Injective(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ArgsPacker(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PProdN(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_ElimInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__1);
l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__2);
l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__3);
l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmAnd___closed__4);
l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__1);
l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__2);
l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__3);
l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__1___closed__4);
l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__1);
l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__2);
l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__3);
l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___lambda__2___closed__4);
l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__1);
l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__2);
l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__3);
l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__4);
l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__5 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__5);
l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__6 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__6);
l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__7 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__7);
l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__8 = _init_l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__8();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkAdmProj___closed__8);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_maskArray___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Induction_0__Lean_Elab_PartialFixpoint_numberNames___lambda__1___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__1 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__2 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__2();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__5___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__7___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__9___closed__2);
l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1___closed__1 = _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___lambda__1___closed__1);
l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__1 = _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__1);
l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__2 = _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__2);
l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__3 = _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__3);
l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__4 = _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__16___rarg___closed__4);
l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__1 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__2 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__2();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___lambda__1___closed__2);
l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__1 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__2 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__2();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_deriveInduction___spec__17___closed__2);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__1 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__1);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__2 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__2);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__3 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__3);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__4 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__4);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__5 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__5);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__6 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__6);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__7 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__7);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__8 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__8();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__8);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__9 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__9();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__9);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__10 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__10();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__10);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__11 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__11();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__4___closed__11);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5___closed__1 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__5___closed__1);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__1 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__1);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__2 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__2);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__3 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__6___closed__3);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__1 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__1);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__2 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__7___closed__2);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__1 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__1);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__2 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__8___closed__2);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__1 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__1);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__2 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__9___closed__2);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__1);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__2 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__2);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__3 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__3);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__4);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__5);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__6 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__6);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__7 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__7);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__8 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__8();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__8);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__9);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__10 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__10();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__10);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__11 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__11();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___closed__11);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___boxed__const__1 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__10___boxed__const__1);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__1 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__1);
l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__2 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___lambda__11___closed__2);
l_Lean_Elab_PartialFixpoint_deriveInduction___closed__1 = _init_l_Lean_Elab_PartialFixpoint_deriveInduction___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_deriveInduction___closed__1);
l_Lean_Elab_PartialFixpoint_isInductName___closed__1 = _init_l_Lean_Elab_PartialFixpoint_isInductName___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_isInductName___closed__1);
l_Lean_Elab_PartialFixpoint_isInductName___closed__2 = _init_l_Lean_Elab_PartialFixpoint_isInductName___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_isInductName___closed__2);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__1 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__2 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__2);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__3 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__3();
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__4 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__4);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__5 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__5);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__6 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__6);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__7 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__7);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__8 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__8);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__9 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__9();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__9);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__10 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__10();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__10);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__11 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__11();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__11);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__12 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__12();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__12);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__13 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__13();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__13);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__14 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__14();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____lambda__2___closed__14);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__1 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__2 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637____closed__2);
if (builtin) {res = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_2637_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__1 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__1();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__1);
l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__2 = _init_l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__2();
lean_mark_persistent(l_Lean_Loop_forIn_loop___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__3___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_isOptionFixpoint___spec__4___closed__2);
l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1___closed__1 = _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__1___closed__1);
l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__1 = _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__1);
l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__2 = _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_isOptionFixpoint___lambda__2___closed__2);
l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1 = _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__1);
l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__2 = _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__2);
l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__3 = _init_l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_isOptionFixpoint___closed__3);
l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1 = _init_l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_isPartialCorrectnessName___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_PartialFixpoint_mkOptionAdm___spec__1___closed__2);
l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__1);
l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__2);
l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__3);
l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__4);
l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__5 = _init_l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkOptionAdm___lambda__1___closed__5);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__3___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__4___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__4___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___lambda__4___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__2___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__1 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__2 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__2();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__3___closed__2);
l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__1 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__2 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_PartialFixpoint_derivePartialCorrectness___spec__4___lambda__1___closed__2);
l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__1 = _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__1);
l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__2 = _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__1___closed__2);
l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__1 = _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__1);
l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__2 = _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__2);
l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__3 = _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___closed__3);
l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___boxed__const__1 = _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__3___boxed__const__1);
l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__1 = _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__1);
l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__2 = _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__4___closed__2);
l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5___closed__1 = _init_l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_derivePartialCorrectness___lambda__5___closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__1 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__2 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642____closed__2);
if (builtin) {res = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4642_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__1 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__1();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__1);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__2 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__2();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__2);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__3 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__3();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__3);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__4 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__4();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__4);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__5 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__5();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__5);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__6 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__6();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__6);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__7 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__7();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__7);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__8 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__8();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__8);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__9 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__9();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__9);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__10 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__10();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__10);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__11 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__11();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__11);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__12 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__12();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__12);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__13 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__13();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__13);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__14 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__14();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__14);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__15 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__15();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828____closed__15);
if (builtin) {res = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Induction___hyg_4828_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
