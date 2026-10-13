// Lean compiler output
// Module: Lean.Meta.Constructions.CasesOnSameCtor
// Imports: public import Lean.Meta.Basic import Lean.Meta.CompletionName import Lean.Meta.Constructions.CtorIdx import Lean.Meta.Constructions.CtorElim import Lean.Elab.App import Lean.Meta.SameCtorUtils
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
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_MessageData_nil;
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewEqs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCtorIdxName(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withSharedCtorIndices___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_unzip___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_Cases_unifyEqs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_elabAsElim;
lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_mkConstructorElimName(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_Meta_markMatcherLike(lean_object*, lean_object*);
lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0 = (const lean_object*)&l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object**);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 10, 150, 230, 97, 79, 179, 234)}};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object**);
static const lean_ctor_object l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__20;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__21 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__21_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__22;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__23 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__23_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__24;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__25 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__25_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__26;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Meta.Constructions.CasesOnSameCtor"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__0_value;
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.mkCasesOnSameCtorHet"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__1_value;
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unexpected universe levels on `casesOn`"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__2 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__2_value;
static lean_once_cell_t l_Lean_mkCasesOnSameCtorHet___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtorHet___closed__3;
static const lean_string_object l_Lean_mkCasesOnSameCtorHet___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_mkCasesOnSameCtorHet___closed__4 = (const lean_object*)&l_Lean_mkCasesOnSameCtorHet___closed__4_value;
static lean_once_cell_t l_Lean_mkCasesOnSameCtorHet___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtorHet___closed__5;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "could not apply "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " to close\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "unifyEqns\? unexpectedly closed goal"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtor___lam__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object**);
static const lean_string_object l_Lean_mkCasesOnSameCtor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "het"};
static const lean_object* l_Lean_mkCasesOnSameCtor___closed__0 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___closed__0_value;
static const lean_ctor_object l_Lean_mkCasesOnSameCtor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOnSameCtor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 194, 63, 63, 137, 239, 65, 92)}};
static const lean_object* l_Lean_mkCasesOnSameCtor___closed__1 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___closed__1_value;
static const lean_string_object l_Lean_mkCasesOnSameCtor___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.mkCasesOnSameCtor"};
static const lean_object* l_Lean_mkCasesOnSameCtor___closed__2 = (const lean_object*)&l_Lean_mkCasesOnSameCtor___closed__2_value;
static lean_once_cell_t l_Lean_mkCasesOnSameCtor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtor___closed__3;
static lean_once_cell_t l_Lean_mkCasesOnSameCtor___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnSameCtor___closed__4;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_9_ = lean_apply_7(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed(lean_object* v_k_10_, lean_object* v_b_11_, lean_object* v_c_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(v_k_10_, v_b_11_, v_c_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(lean_object* v_type_19_, lean_object* v_k_20_, uint8_t v_cleanupAnnotations_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_){
_start:
{
lean_object* v___f_27_; uint8_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___f_27_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_27_, 0, v_k_20_);
v___x_28_ = 0;
v___x_29_ = lean_box(0);
v___x_30_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_28_, v___x_29_, v_type_19_, v___f_27_, v_cleanupAnnotations_21_, v___x_28_, v___y_22_, v___y_23_, v___y_24_, v___y_25_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_38_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_38_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_38_ == 0)
{
v___x_33_ = v___x_30_;
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_a_31_);
lean_dec(v___x_30_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_38_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_36_; 
if (v_isShared_34_ == 0)
{
v___x_36_ = v___x_33_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_31_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
else
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_46_; 
v_a_39_ = lean_ctor_get(v___x_30_, 0);
v_isSharedCheck_46_ = !lean_is_exclusive(v___x_30_);
if (v_isSharedCheck_46_ == 0)
{
v___x_41_ = v___x_30_;
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_30_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_46_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_44_; 
if (v_isShared_42_ == 0)
{
v___x_44_ = v___x_41_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_a_39_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___boxed(lean_object* v_type_47_, lean_object* v_k_48_, lean_object* v_cleanupAnnotations_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_55_; lean_object* v_res_56_; 
v_cleanupAnnotations_boxed_55_ = lean_unbox(v_cleanupAnnotations_49_);
v_res_56_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_type_47_, v_k_48_, v_cleanupAnnotations_boxed_55_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(lean_object* v_00_u03b1_57_, lean_object* v_type_58_, lean_object* v_k_59_, uint8_t v_cleanupAnnotations_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_type_58_, v_k_59_, v_cleanupAnnotations_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___boxed(lean_object* v_00_u03b1_67_, lean_object* v_type_68_, lean_object* v_k_69_, lean_object* v_cleanupAnnotations_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_76_; lean_object* v_res_77_; 
v_cleanupAnnotations_boxed_76_ = lean_unbox(v_cleanupAnnotations_70_);
v_res_77_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(v_00_u03b1_67_, v_type_68_, v_k_69_, v_cleanupAnnotations_boxed_76_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
lean_dec(v___y_74_);
lean_dec_ref(v___y_73_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(lean_object* v_k_78_, lean_object* v_b_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; 
lean_inc(v___y_83_);
lean_inc_ref(v___y_82_);
lean_inc(v___y_81_);
lean_inc_ref(v___y_80_);
v___x_85_ = lean_apply_6(v_k_78_, v_b_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, lean_box(0));
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed(lean_object* v_k_86_, lean_object* v_b_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(v_k_86_, v_b_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_);
lean_dec(v___y_91_);
lean_dec_ref(v___y_90_);
lean_dec(v___y_89_);
lean_dec_ref(v___y_88_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(lean_object* v_name_94_, uint8_t v_bi_95_, lean_object* v_type_96_, lean_object* v_k_97_, uint8_t v_kind_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v___f_104_; lean_object* v___x_105_; 
v___f_104_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_104_, 0, v_k_97_);
v___x_105_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_94_, v_bi_95_, v_type_96_, v___f_104_, v_kind_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_113_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_113_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_113_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_111_; 
if (v_isShared_109_ == 0)
{
v___x_111_ = v___x_108_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_a_106_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
else
{
lean_object* v_a_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_121_; 
v_a_114_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_121_ == 0)
{
v___x_116_ = v___x_105_;
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_a_114_);
lean_dec(v___x_105_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_121_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_119_; 
if (v_isShared_117_ == 0)
{
v___x_119_ = v___x_116_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v_a_114_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___boxed(lean_object* v_name_122_, lean_object* v_bi_123_, lean_object* v_type_124_, lean_object* v_k_125_, lean_object* v_kind_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
uint8_t v_bi_boxed_132_; uint8_t v_kind_boxed_133_; lean_object* v_res_134_; 
v_bi_boxed_132_ = lean_unbox(v_bi_123_);
v_kind_boxed_133_ = lean_unbox(v_kind_126_);
v_res_134_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_122_, v_bi_boxed_132_, v_type_124_, v_k_125_, v_kind_boxed_133_, v___y_127_, v___y_128_, v___y_129_, v___y_130_);
lean_dec(v___y_130_);
lean_dec_ref(v___y_129_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(lean_object* v_00_u03b1_135_, lean_object* v_name_136_, uint8_t v_bi_137_, lean_object* v_type_138_, lean_object* v_k_139_, uint8_t v_kind_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_136_, v_bi_137_, v_type_138_, v_k_139_, v_kind_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___boxed(lean_object* v_00_u03b1_147_, lean_object* v_name_148_, lean_object* v_bi_149_, lean_object* v_type_150_, lean_object* v_k_151_, lean_object* v_kind_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
uint8_t v_bi_boxed_158_; uint8_t v_kind_boxed_159_; lean_object* v_res_160_; 
v_bi_boxed_158_ = lean_unbox(v_bi_149_);
v_kind_boxed_159_ = lean_unbox(v_kind_152_);
v_res_160_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(v_00_u03b1_147_, v_name_148_, v_bi_boxed_158_, v_type_150_, v_k_151_, v_kind_boxed_159_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(lean_object* v_type_161_, lean_object* v_maxFVars_x3f_162_, lean_object* v_k_163_, uint8_t v_cleanupAnnotations_164_, uint8_t v_whnfType_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___f_171_; lean_object* v___x_172_; 
v___f_171_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_171_, 0, v_k_163_);
v___x_172_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_161_, v_maxFVars_x3f_162_, v___f_171_, v_cleanupAnnotations_164_, v_whnfType_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
v_a_181_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_172_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_172_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg___boxed(lean_object* v_type_189_, lean_object* v_maxFVars_x3f_190_, lean_object* v_k_191_, lean_object* v_cleanupAnnotations_192_, lean_object* v_whnfType_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_199_; uint8_t v_whnfType_boxed_200_; lean_object* v_res_201_; 
v_cleanupAnnotations_boxed_199_ = lean_unbox(v_cleanupAnnotations_192_);
v_whnfType_boxed_200_ = lean_unbox(v_whnfType_193_);
v_res_201_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_189_, v_maxFVars_x3f_190_, v_k_191_, v_cleanupAnnotations_boxed_199_, v_whnfType_boxed_200_, v___y_194_, v___y_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(lean_object* v_00_u03b1_202_, lean_object* v_type_203_, lean_object* v_maxFVars_x3f_204_, lean_object* v_k_205_, uint8_t v_cleanupAnnotations_206_, uint8_t v_whnfType_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_203_, v_maxFVars_x3f_204_, v_k_205_, v_cleanupAnnotations_206_, v_whnfType_207_, v___y_208_, v___y_209_, v___y_210_, v___y_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___boxed(lean_object* v_00_u03b1_214_, lean_object* v_type_215_, lean_object* v_maxFVars_x3f_216_, lean_object* v_k_217_, lean_object* v_cleanupAnnotations_218_, lean_object* v_whnfType_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_225_; uint8_t v_whnfType_boxed_226_; lean_object* v_res_227_; 
v_cleanupAnnotations_boxed_225_ = lean_unbox(v_cleanupAnnotations_218_);
v_whnfType_boxed_226_ = lean_unbox(v_whnfType_219_);
v_res_227_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(v_00_u03b1_214_, v_type_215_, v_maxFVars_x3f_216_, v_k_217_, v_cleanupAnnotations_boxed_225_, v_whnfType_boxed_226_, v___y_220_, v___y_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(lean_object* v_name_228_, lean_object* v_levelParams_229_, lean_object* v_type_230_, lean_object* v_value_231_, lean_object* v_hints_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; uint8_t v___y_237_; uint8_t v___y_244_; lean_object* v_env_247_; uint8_t v___x_248_; 
v___x_235_ = lean_st_ref_get(v___y_233_);
v_env_247_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref_n(v_env_247_, 2);
lean_dec(v___x_235_);
v___x_248_ = l_Lean_Environment_hasUnsafe(v_env_247_, v_type_230_);
if (v___x_248_ == 0)
{
uint8_t v___x_249_; 
v___x_249_ = l_Lean_Environment_hasUnsafe(v_env_247_, v_value_231_);
v___y_244_ = v___x_249_;
goto v___jp_243_;
}
else
{
lean_dec_ref(v_env_247_);
v___y_244_ = v___x_248_;
goto v___jp_243_;
}
v___jp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
lean_inc(v_name_228_);
v___x_238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_238_, 0, v_name_228_);
lean_ctor_set(v___x_238_, 1, v_levelParams_229_);
lean_ctor_set(v___x_238_, 2, v_type_230_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_240_, 0, v_name_228_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_241_, 0, v___x_238_);
lean_ctor_set(v___x_241_, 1, v_value_231_);
lean_ctor_set(v___x_241_, 2, v_hints_232_);
lean_ctor_set(v___x_241_, 3, v___x_240_);
lean_ctor_set_uint8(v___x_241_, sizeof(void*)*4, v___y_237_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
v___jp_243_:
{
if (v___y_244_ == 0)
{
uint8_t v___x_245_; 
v___x_245_ = 1;
v___y_237_ = v___x_245_;
goto v___jp_236_;
}
else
{
uint8_t v___x_246_; 
v___x_246_ = 0;
v___y_237_ = v___x_246_;
goto v___jp_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg___boxed(lean_object* v_name_250_, lean_object* v_levelParams_251_, lean_object* v_type_252_, lean_object* v_value_253_, lean_object* v_hints_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_250_, v_levelParams_251_, v_type_252_, v_value_253_, v_hints_254_, v___y_255_);
lean_dec(v___y_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(lean_object* v_name_258_, lean_object* v_levelParams_259_, lean_object* v_type_260_, lean_object* v_value_261_, lean_object* v_hints_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_258_, v_levelParams_259_, v_type_260_, v_value_261_, v_hints_262_, v___y_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___boxed(lean_object* v_name_269_, lean_object* v_levelParams_270_, lean_object* v_type_271_, lean_object* v_value_272_, lean_object* v_hints_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(v_name_269_, v_levelParams_270_, v_type_271_, v_value_272_, v_hints_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object* v___y_280_, uint8_t v_isExporting_281_, lean_object* v___x_282_, lean_object* v___y_283_, lean_object* v___x_284_, lean_object* v_a_x3f_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v_nextMacroScope_289_; lean_object* v_ngen_290_; lean_object* v_auxDeclNGen_291_; lean_object* v_traceState_292_; lean_object* v_recordedDeps_293_; lean_object* v_messages_294_; lean_object* v_infoState_295_; lean_object* v_snapshotTasks_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_321_; 
v___x_287_ = lean_st_ref_take(v___y_280_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
v_nextMacroScope_289_ = lean_ctor_get(v___x_287_, 1);
v_ngen_290_ = lean_ctor_get(v___x_287_, 2);
v_auxDeclNGen_291_ = lean_ctor_get(v___x_287_, 3);
v_traceState_292_ = lean_ctor_get(v___x_287_, 4);
v_recordedDeps_293_ = lean_ctor_get(v___x_287_, 6);
v_messages_294_ = lean_ctor_get(v___x_287_, 7);
v_infoState_295_ = lean_ctor_get(v___x_287_, 8);
v_snapshotTasks_296_ = lean_ctor_get(v___x_287_, 9);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_321_ == 0)
{
lean_object* v_unused_322_; 
v_unused_322_ = lean_ctor_get(v___x_287_, 5);
lean_dec(v_unused_322_);
v___x_298_ = v___x_287_;
v_isShared_299_ = v_isSharedCheck_321_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_snapshotTasks_296_);
lean_inc(v_infoState_295_);
lean_inc(v_messages_294_);
lean_inc(v_recordedDeps_293_);
lean_inc(v_traceState_292_);
lean_inc(v_auxDeclNGen_291_);
lean_inc(v_ngen_290_);
lean_inc(v_nextMacroScope_289_);
lean_inc(v_env_288_);
lean_dec(v___x_287_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_321_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_Environment_setExporting(v_env_288_, v_isExporting_281_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 5, v___x_282_);
lean_ctor_set(v___x_298_, 0, v___x_300_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_nextMacroScope_289_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_ngen_290_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_auxDeclNGen_291_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_320_, 5, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_320_, 6, v_recordedDeps_293_);
lean_ctor_set(v_reuseFailAlloc_320_, 7, v_messages_294_);
lean_ctor_set(v_reuseFailAlloc_320_, 8, v_infoState_295_);
lean_ctor_set(v_reuseFailAlloc_320_, 9, v_snapshotTasks_296_);
v___x_302_ = v_reuseFailAlloc_320_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v_mctx_305_; lean_object* v_zetaDeltaFVarIds_306_; lean_object* v_postponed_307_; lean_object* v_diag_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_318_; 
v___x_303_ = lean_st_ref_put(v___y_280_, v___x_302_);
v___x_304_ = lean_st_ref_take(v___y_283_);
v_mctx_305_ = lean_ctor_get(v___x_304_, 0);
v_zetaDeltaFVarIds_306_ = lean_ctor_get(v___x_304_, 2);
v_postponed_307_ = lean_ctor_get(v___x_304_, 3);
v_diag_308_ = lean_ctor_get(v___x_304_, 4);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_318_ == 0)
{
lean_object* v_unused_319_; 
v_unused_319_ = lean_ctor_get(v___x_304_, 1);
lean_dec(v_unused_319_);
v___x_310_ = v___x_304_;
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_diag_308_);
lean_inc(v_postponed_307_);
lean_inc(v_zetaDeltaFVarIds_306_);
lean_inc(v_mctx_305_);
lean_dec(v___x_304_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_318_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = lean_box(0);
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 1, v___x_284_);
v___x_314_ = v___x_310_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_mctx_305_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_zetaDeltaFVarIds_306_);
lean_ctor_set(v_reuseFailAlloc_317_, 3, v_postponed_307_);
lean_ctor_set(v_reuseFailAlloc_317_, 4, v_diag_308_);
v___x_314_ = v_reuseFailAlloc_317_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_st_ref_put(v___y_283_, v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_312_);
return v___x_316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object* v___y_323_, lean_object* v_isExporting_324_, lean_object* v___x_325_, lean_object* v___y_326_, lean_object* v___x_327_, lean_object* v_a_x3f_328_, lean_object* v___y_329_){
_start:
{
uint8_t v_isExporting_boxed_330_; lean_object* v_res_331_; 
v_isExporting_boxed_330_ = lean_unbox(v_isExporting_324_);
v_res_331_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_323_, v_isExporting_boxed_330_, v___x_325_, v___y_326_, v___x_327_, v_a_x3f_328_);
lean_dec(v_a_x3f_328_);
lean_dec(v___y_326_);
lean_dec(v___y_323_);
return v_res_331_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_332_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_338_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_ctor_set(v___x_338_, 2, v___x_337_);
lean_ctor_set(v___x_338_, 3, v___x_337_);
lean_ctor_set(v___x_338_, 4, v___x_337_);
lean_ctor_set(v___x_338_, 5, v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object* v_x_339_, uint8_t v_isExporting_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v_env_347_; lean_object* v___x_348_; uint8_t v_isModule_349_; 
v___x_346_ = lean_st_ref_get(v___y_344_);
v_env_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_env_347_);
lean_dec(v___x_346_);
v___x_348_ = l_Lean_Environment_header(v_env_347_);
v_isModule_349_ = lean_ctor_get_uint8(v___x_348_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_348_);
if (v_isModule_349_ == 0)
{
lean_object* v___x_350_; 
lean_dec_ref(v_env_347_);
lean_inc(v___y_344_);
lean_inc_ref(v___y_343_);
lean_inc(v___y_342_);
lean_inc_ref(v___y_341_);
v___x_350_ = lean_apply_5(v_x_339_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, lean_box(0));
return v___x_350_;
}
else
{
uint8_t v_isExporting_351_; 
v_isExporting_351_ = lean_ctor_get_uint8(v_env_347_, sizeof(void*)*13);
lean_dec_ref(v_env_347_);
if (v_isExporting_340_ == 0)
{
if (v_isExporting_351_ == 0)
{
lean_object* v___x_418_; 
lean_inc(v___y_344_);
lean_inc_ref(v___y_343_);
lean_inc(v___y_342_);
lean_inc_ref(v___y_341_);
v___x_418_ = lean_apply_5(v_x_339_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, lean_box(0));
return v___x_418_;
}
else
{
goto v___jp_352_;
}
}
else
{
if (v_isExporting_351_ == 0)
{
goto v___jp_352_;
}
else
{
lean_object* v___x_419_; 
lean_inc(v___y_344_);
lean_inc_ref(v___y_343_);
lean_inc(v___y_342_);
lean_inc_ref(v___y_341_);
v___x_419_ = lean_apply_5(v_x_339_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, lean_box(0));
return v___x_419_;
}
}
v___jp_352_:
{
lean_object* v___x_353_; lean_object* v_env_354_; lean_object* v_nextMacroScope_355_; lean_object* v_ngen_356_; lean_object* v_auxDeclNGen_357_; lean_object* v_traceState_358_; lean_object* v_recordedDeps_359_; lean_object* v_messages_360_; lean_object* v_infoState_361_; lean_object* v_snapshotTasks_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_416_; 
v___x_353_ = lean_st_ref_take(v___y_344_);
v_env_354_ = lean_ctor_get(v___x_353_, 0);
v_nextMacroScope_355_ = lean_ctor_get(v___x_353_, 1);
v_ngen_356_ = lean_ctor_get(v___x_353_, 2);
v_auxDeclNGen_357_ = lean_ctor_get(v___x_353_, 3);
v_traceState_358_ = lean_ctor_get(v___x_353_, 4);
v_recordedDeps_359_ = lean_ctor_get(v___x_353_, 6);
v_messages_360_ = lean_ctor_get(v___x_353_, 7);
v_infoState_361_ = lean_ctor_get(v___x_353_, 8);
v_snapshotTasks_362_ = lean_ctor_get(v___x_353_, 9);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_416_ == 0)
{
lean_object* v_unused_417_; 
v_unused_417_ = lean_ctor_get(v___x_353_, 5);
lean_dec(v_unused_417_);
v___x_364_ = v___x_353_;
v_isShared_365_ = v_isSharedCheck_416_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_snapshotTasks_362_);
lean_inc(v_infoState_361_);
lean_inc(v_messages_360_);
lean_inc(v_recordedDeps_359_);
lean_inc(v_traceState_358_);
lean_inc(v_auxDeclNGen_357_);
lean_inc(v_ngen_356_);
lean_inc(v_nextMacroScope_355_);
lean_inc(v_env_354_);
lean_dec(v___x_353_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_416_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_366_ = l_Lean_Environment_setExporting(v_env_354_, v_isExporting_340_);
v___x_367_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 5, v___x_367_);
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_369_ = v___x_364_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_nextMacroScope_355_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_ngen_356_);
lean_ctor_set(v_reuseFailAlloc_415_, 3, v_auxDeclNGen_357_);
lean_ctor_set(v_reuseFailAlloc_415_, 4, v_traceState_358_);
lean_ctor_set(v_reuseFailAlloc_415_, 5, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_415_, 6, v_recordedDeps_359_);
lean_ctor_set(v_reuseFailAlloc_415_, 7, v_messages_360_);
lean_ctor_set(v_reuseFailAlloc_415_, 8, v_infoState_361_);
lean_ctor_set(v_reuseFailAlloc_415_, 9, v_snapshotTasks_362_);
v___x_369_ = v_reuseFailAlloc_415_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_mctx_372_; lean_object* v_zetaDeltaFVarIds_373_; lean_object* v_postponed_374_; lean_object* v_diag_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_413_; 
v___x_370_ = lean_st_ref_put(v___y_344_, v___x_369_);
v___x_371_ = lean_st_ref_take(v___y_342_);
v_mctx_372_ = lean_ctor_get(v___x_371_, 0);
v_zetaDeltaFVarIds_373_ = lean_ctor_get(v___x_371_, 2);
v_postponed_374_ = lean_ctor_get(v___x_371_, 3);
v_diag_375_ = lean_ctor_get(v___x_371_, 4);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; 
v_unused_414_ = lean_ctor_get(v___x_371_, 1);
lean_dec(v_unused_414_);
v___x_377_ = v___x_371_;
v_isShared_378_ = v_isSharedCheck_413_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_diag_375_);
lean_inc(v_postponed_374_);
lean_inc(v_zetaDeltaFVarIds_373_);
lean_inc(v_mctx_372_);
lean_dec(v___x_371_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_413_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_379_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 1, v___x_379_);
v___x_381_ = v___x_377_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_mctx_372_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v_zetaDeltaFVarIds_373_);
lean_ctor_set(v_reuseFailAlloc_412_, 3, v_postponed_374_);
lean_ctor_set(v_reuseFailAlloc_412_, 4, v_diag_375_);
v___x_381_ = v_reuseFailAlloc_412_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v_r_383_; 
v___x_382_ = lean_st_ref_put(v___y_342_, v___x_381_);
lean_inc(v___y_344_);
lean_inc_ref(v___y_343_);
lean_inc(v___y_342_);
lean_inc_ref(v___y_341_);
v_r_383_ = lean_apply_5(v_x_339_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, lean_box(0));
if (lean_obj_tag(v_r_383_) == 0)
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_400_; 
v_a_384_ = lean_ctor_get(v_r_383_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v_r_383_);
if (v_isSharedCheck_400_ == 0)
{
v___x_386_ = v_r_383_;
v_isShared_387_ = v_isSharedCheck_400_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v_r_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_400_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
lean_inc(v_a_384_);
if (v_isShared_387_ == 0)
{
lean_ctor_set_tag(v___x_386_, 1);
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_399_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
v___x_390_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_344_, v_isExporting_351_, v___x_367_, v___y_342_, v___x_379_, v___x_389_);
lean_dec_ref(v___x_389_);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_397_ == 0)
{
lean_object* v_unused_398_; 
v_unused_398_ = lean_ctor_get(v___x_390_, 0);
lean_dec(v_unused_398_);
v___x_392_ = v___x_390_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_dec(v___x_390_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v_a_384_);
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_384_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
else
{
lean_object* v_a_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
v_a_401_ = lean_ctor_get(v_r_383_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v_r_383_, 1);
v___x_402_ = lean_box(0);
v___x_403_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_344_, v_isExporting_351_, v___x_367_, v___y_342_, v___x_379_, v___x_402_);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_411_);
v___x_405_ = v___x_403_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_dec(v___x_403_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set_tag(v___x_405_, 1);
lean_ctor_set(v___x_405_, 0, v_a_401_);
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_401_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_420_, lean_object* v_isExporting_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
uint8_t v_isExporting_boxed_427_; lean_object* v_res_428_; 
v_isExporting_boxed_427_ = lean_unbox(v_isExporting_421_);
v_res_428_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_420_, v_isExporting_boxed_427_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_429_, lean_object* v_x_430_, uint8_t v_isExporting_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_430_, v_isExporting_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_438_, lean_object* v_x_439_, lean_object* v_isExporting_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
uint8_t v_isExporting_boxed_446_; lean_object* v_res_447_; 
v_isExporting_boxed_446_ = lean_unbox(v_isExporting_440_);
v_res_447_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_438_, v_x_439_, v_isExporting_boxed_446_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_msg_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___f_455_; lean_object* v___x_15764__overap_456_; lean_object* v___x_457_; 
v___f_455_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15764__overap_456_ = lean_panic_fn_borrowed(v___f_455_, v_msg_449_);
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
v___x_457_ = lean_apply_5(v___x_15764__overap_456_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, lean_box(0));
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_msg_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_msg_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object* v_name_465_, lean_object* v_type_466_, lean_object* v_k_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
uint8_t v___x_473_; uint8_t v___x_474_; lean_object* v___x_475_; 
v___x_473_ = 0;
v___x_474_ = 0;
v___x_475_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_465_, v___x_473_, v_type_466_, v_k_467_, v___x_474_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object* v_name_476_, lean_object* v_type_477_, lean_object* v_k_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_476_, v_type_477_, v_k_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object* v___x_485_, lean_object* v_ism2_486_, lean_object* v_motive_487_, uint8_t v___x_488_, uint8_t v___x_489_, uint8_t v___x_490_, lean_object* v_a_491_, lean_object* v___f_492_, lean_object* v_zs1_493_, lean_object* v_val_494_, lean_object* v___x_495_, lean_object* v_indName_496_, lean_object* v_v_497_, lean_object* v___x_498_, lean_object* v_params_499_, lean_object* v___x_500_, lean_object* v_h_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = l_Array_append___redArg(v___x_485_, v_ism2_486_);
v___x_508_ = l_Lean_mkAppN(v_motive_487_, v___x_507_);
lean_dec_ref(v___x_507_);
v___x_509_ = l_Lean_Meta_mkLambdaFVars(v_ism2_486_, v___x_508_, v___x_488_, v___x_489_, v___x_488_, v___x_489_, v___x_490_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_511_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_511_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_491_, v___f_492_, v___x_488_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
if (lean_obj_tag(v___x_511_) == 0)
{
lean_object* v_a_512_; lean_object* v___y_514_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_a_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_a_512_);
lean_dec_ref_known(v___x_511_, 1);
v___x_517_ = l_Lean_InductiveVal_numCtors(v_val_494_);
v___x_518_ = lean_nat_dec_eq(v___x_517_, v___x_495_);
lean_dec(v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v___x_500_);
v___x_519_ = l_Lean_mkConstructorElimName(v_indName_496_, v_v_497_);
v___x_520_ = l_Lean_mkConst(v___x_519_, v___x_498_);
v___x_521_ = lean_mk_empty_array_with_capacity(v___x_495_);
v___x_522_ = lean_array_push(v___x_521_, v_a_510_);
v___x_523_ = l_Array_append___redArg(v_params_499_, v___x_522_);
lean_dec_ref(v___x_522_);
v___x_524_ = l_Array_append___redArg(v___x_523_, v_ism2_486_);
v___x_525_ = lean_unsigned_to_nat(2u);
v___x_526_ = lean_mk_empty_array_with_capacity(v___x_525_);
lean_inc_ref(v_h_501_);
v___x_527_ = lean_array_push(v___x_526_, v_h_501_);
v___x_528_ = lean_array_push(v___x_527_, v_a_512_);
v___x_529_ = l_Array_append___redArg(v___x_524_, v___x_528_);
lean_dec_ref(v___x_528_);
v___x_530_ = l_Lean_mkAppN(v___x_520_, v___x_529_);
lean_dec_ref(v___x_529_);
v___y_514_ = v___x_530_;
goto v___jp_513_;
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v_v_497_);
v___x_531_ = l_Lean_mkConst(v___x_500_, v___x_498_);
v___x_532_ = lean_mk_empty_array_with_capacity(v___x_495_);
lean_inc_ref(v___x_532_);
v___x_533_ = lean_array_push(v___x_532_, v_a_510_);
v___x_534_ = l_Array_append___redArg(v_params_499_, v___x_533_);
lean_dec_ref(v___x_533_);
v___x_535_ = l_Array_append___redArg(v___x_534_, v_ism2_486_);
v___x_536_ = lean_array_push(v___x_532_, v_a_512_);
v___x_537_ = l_Array_append___redArg(v___x_535_, v___x_536_);
lean_dec_ref(v___x_536_);
v___x_538_ = l_Lean_mkAppN(v___x_531_, v___x_537_);
lean_dec_ref(v___x_537_);
v___y_514_ = v___x_538_;
goto v___jp_513_;
}
v___jp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_array_push(v_zs1_493_, v_h_501_);
v___x_516_ = l_Lean_Meta_mkLambdaFVars(v___x_515_, v___y_514_, v___x_488_, v___x_489_, v___x_488_, v___x_489_, v___x_490_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec_ref(v___x_515_);
return v___x_516_;
}
}
else
{
lean_dec(v_a_510_);
lean_dec_ref(v_h_501_);
lean_dec(v___x_500_);
lean_dec_ref(v_params_499_);
lean_dec(v___x_498_);
lean_dec(v_v_497_);
lean_dec_ref(v_zs1_493_);
return v___x_511_;
}
}
else
{
lean_dec_ref(v_h_501_);
lean_dec(v___x_500_);
lean_dec_ref(v_params_499_);
lean_dec(v___x_498_);
lean_dec(v_v_497_);
lean_dec_ref(v_zs1_493_);
lean_dec_ref(v___f_492_);
lean_dec_ref(v_a_491_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_539_ = _args[0];
lean_object* v_ism2_540_ = _args[1];
lean_object* v_motive_541_ = _args[2];
lean_object* v___x_542_ = _args[3];
lean_object* v___x_543_ = _args[4];
lean_object* v___x_544_ = _args[5];
lean_object* v_a_545_ = _args[6];
lean_object* v___f_546_ = _args[7];
lean_object* v_zs1_547_ = _args[8];
lean_object* v_val_548_ = _args[9];
lean_object* v___x_549_ = _args[10];
lean_object* v_indName_550_ = _args[11];
lean_object* v_v_551_ = _args[12];
lean_object* v___x_552_ = _args[13];
lean_object* v_params_553_ = _args[14];
lean_object* v___x_554_ = _args[15];
lean_object* v_h_555_ = _args[16];
lean_object* v___y_556_ = _args[17];
lean_object* v___y_557_ = _args[18];
lean_object* v___y_558_ = _args[19];
lean_object* v___y_559_ = _args[20];
lean_object* v___y_560_ = _args[21];
_start:
{
uint8_t v___x_20922__boxed_561_; uint8_t v___x_20923__boxed_562_; uint8_t v___x_20924__boxed_563_; lean_object* v_res_564_; 
v___x_20922__boxed_561_ = lean_unbox(v___x_542_);
v___x_20923__boxed_562_ = lean_unbox(v___x_543_);
v___x_20924__boxed_563_ = lean_unbox(v___x_544_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_539_, v_ism2_540_, v_motive_541_, v___x_20922__boxed_561_, v___x_20923__boxed_562_, v___x_20924__boxed_563_, v_a_545_, v___f_546_, v_zs1_547_, v_val_548_, v___x_549_, v_indName_550_, v_v_551_, v___x_552_, v_params_553_, v___x_554_, v_h_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v_indName_550_);
lean_dec(v___x_549_);
lean_dec_ref(v_val_548_);
lean_dec_ref(v_ism2_540_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object* v___x_565_, lean_object* v_alts_566_, lean_object* v___x_567_, lean_object* v_zs1_568_, uint8_t v___x_569_, uint8_t v___x_570_, uint8_t v___x_571_, lean_object* v_zs2_572_, lean_object* v_x_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_579_ = lean_array_get_borrowed(v___x_565_, v_alts_566_, v___x_567_);
v___x_580_ = l_Array_append___redArg(v_zs1_568_, v_zs2_572_);
lean_inc(v___x_579_);
v___x_581_ = l_Lean_mkAppN(v___x_579_, v___x_580_);
lean_dec_ref(v___x_580_);
v___x_582_ = l_Lean_Meta_mkLambdaFVars(v_zs2_572_, v___x_581_, v___x_569_, v___x_570_, v___x_569_, v___x_570_, v___x_571_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object* v___x_583_, lean_object* v_alts_584_, lean_object* v___x_585_, lean_object* v_zs1_586_, lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v___x_589_, lean_object* v_zs2_590_, lean_object* v_x_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
uint8_t v___x_21034__boxed_597_; uint8_t v___x_21035__boxed_598_; uint8_t v___x_21036__boxed_599_; lean_object* v_res_600_; 
v___x_21034__boxed_597_ = lean_unbox(v___x_587_);
v___x_21035__boxed_598_ = lean_unbox(v___x_588_);
v___x_21036__boxed_599_ = lean_unbox(v___x_589_);
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_583_, v_alts_584_, v___x_585_, v_zs1_586_, v___x_21034__boxed_597_, v___x_21035__boxed_598_, v___x_21036__boxed_599_, v_zs2_590_, v_x_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v_x_591_);
lean_dec_ref(v_zs2_590_);
lean_dec(v___x_585_);
lean_dec_ref(v_alts_584_);
lean_dec_ref(v___x_583_);
return v_res_600_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_601_; lean_object* v_dummy_602_; 
v___x_601_ = lean_box(0);
v_dummy_602_ = l_Lean_Expr_sort___override(v___x_601_);
return v_dummy_602_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_box(0);
v___x_610_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4));
v___x_611_ = l_Lean_mkConst(v___x_610_, v___x_609_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object* v___x_612_, lean_object* v_alts_613_, lean_object* v___x_614_, uint8_t v___x_615_, uint8_t v___x_616_, uint8_t v___x_617_, lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v___x_620_, lean_object* v_ism2_621_, lean_object* v_motive_622_, lean_object* v_a_623_, lean_object* v_val_624_, lean_object* v_indName_625_, lean_object* v_v_626_, lean_object* v___x_627_, lean_object* v_params_628_, lean_object* v___x_629_, lean_object* v___x_630_, lean_object* v___x_631_, lean_object* v_zs1_632_, lean_object* v_ctorRet1_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___f_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_639_ = lean_box(v___x_615_);
v___x_640_ = lean_box(v___x_616_);
v___x_641_ = lean_box(v___x_617_);
lean_inc_ref(v_zs1_632_);
lean_inc(v___x_614_);
v___f_642_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_642_, 0, v___x_612_);
lean_closure_set(v___f_642_, 1, v_alts_613_);
lean_closure_set(v___f_642_, 2, v___x_614_);
lean_closure_set(v___f_642_, 3, v_zs1_632_);
lean_closure_set(v___f_642_, 4, v___x_639_);
lean_closure_set(v___f_642_, 5, v___x_640_);
lean_closure_set(v___f_642_, 6, v___x_641_);
v___x_643_ = l_Lean_mkAppN(v___x_618_, v_zs1_632_);
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
v___x_644_ = lean_whnf(v_ctorRet1_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v_dummy_646_; lean_object* v_nargs_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
v_dummy_646_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_647_ = l_Lean_Expr_getAppNumArgs(v_a_645_);
lean_inc(v_nargs_647_);
v___x_648_ = lean_mk_array(v_nargs_647_, v_dummy_646_);
v___x_649_ = lean_nat_sub(v_nargs_647_, v___x_619_);
lean_dec(v_nargs_647_);
v___x_650_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_645_, v___x_648_, v___x_649_);
v___x_651_ = lean_array_get_size(v___x_650_);
v___x_652_ = l_Array_toSubarray___redArg(v___x_650_, v___x_620_, v___x_651_);
v___x_653_ = l_Subarray_copy___redArg(v___x_652_);
v___x_654_ = lean_array_push(v___x_653_, v___x_643_);
v___x_655_ = lean_box(v___x_615_);
v___x_656_ = lean_box(v___x_616_);
v___x_657_ = lean_box(v___x_617_);
lean_inc(v___x_619_);
v___f_658_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed), 22, 16);
lean_closure_set(v___f_658_, 0, v___x_654_);
lean_closure_set(v___f_658_, 1, v_ism2_621_);
lean_closure_set(v___f_658_, 2, v_motive_622_);
lean_closure_set(v___f_658_, 3, v___x_655_);
lean_closure_set(v___f_658_, 4, v___x_656_);
lean_closure_set(v___f_658_, 5, v___x_657_);
lean_closure_set(v___f_658_, 6, v_a_623_);
lean_closure_set(v___f_658_, 7, v___f_642_);
lean_closure_set(v___f_658_, 8, v_zs1_632_);
lean_closure_set(v___f_658_, 9, v_val_624_);
lean_closure_set(v___f_658_, 10, v___x_619_);
lean_closure_set(v___f_658_, 11, v_indName_625_);
lean_closure_set(v___f_658_, 12, v_v_626_);
lean_closure_set(v___f_658_, 13, v___x_627_);
lean_closure_set(v___f_658_, 14, v_params_628_);
lean_closure_set(v___f_658_, 15, v___x_629_);
v___x_659_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2));
v___x_660_ = l_Lean_Level_ofNat(v___x_619_);
lean_dec(v___x_619_);
v___x_661_ = lean_box(0);
v___x_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_mkConst(v___x_659_, v___x_662_);
v___x_664_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
v___x_665_ = l_Lean_mkRawNatLit(v___x_614_);
v___x_666_ = l_Lean_mkApp3(v___x_663_, v___x_664_, v___x_630_, v___x_665_);
v___x_667_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_631_, v___x_666_, v___f_658_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
return v___x_667_;
}
else
{
lean_dec_ref(v___x_643_);
lean_dec_ref(v___f_642_);
lean_dec_ref(v_zs1_632_);
lean_dec(v___x_631_);
lean_dec_ref(v___x_630_);
lean_dec(v___x_629_);
lean_dec_ref(v_params_628_);
lean_dec(v___x_627_);
lean_dec(v_v_626_);
lean_dec(v_indName_625_);
lean_dec_ref(v_val_624_);
lean_dec_ref(v_a_623_);
lean_dec_ref(v_motive_622_);
lean_dec_ref(v_ism2_621_);
lean_dec(v___x_620_);
lean_dec(v___x_619_);
lean_dec(v___x_614_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_668_ = _args[0];
lean_object* v_alts_669_ = _args[1];
lean_object* v___x_670_ = _args[2];
lean_object* v___x_671_ = _args[3];
lean_object* v___x_672_ = _args[4];
lean_object* v___x_673_ = _args[5];
lean_object* v___x_674_ = _args[6];
lean_object* v___x_675_ = _args[7];
lean_object* v___x_676_ = _args[8];
lean_object* v_ism2_677_ = _args[9];
lean_object* v_motive_678_ = _args[10];
lean_object* v_a_679_ = _args[11];
lean_object* v_val_680_ = _args[12];
lean_object* v_indName_681_ = _args[13];
lean_object* v_v_682_ = _args[14];
lean_object* v___x_683_ = _args[15];
lean_object* v_params_684_ = _args[16];
lean_object* v___x_685_ = _args[17];
lean_object* v___x_686_ = _args[18];
lean_object* v___x_687_ = _args[19];
lean_object* v_zs1_688_ = _args[20];
lean_object* v_ctorRet1_689_ = _args[21];
lean_object* v___y_690_ = _args[22];
lean_object* v___y_691_ = _args[23];
lean_object* v___y_692_ = _args[24];
lean_object* v___y_693_ = _args[25];
lean_object* v___y_694_ = _args[26];
_start:
{
uint8_t v___x_21095__boxed_695_; uint8_t v___x_21096__boxed_696_; uint8_t v___x_21097__boxed_697_; lean_object* v_res_698_; 
v___x_21095__boxed_695_ = lean_unbox(v___x_671_);
v___x_21096__boxed_696_ = lean_unbox(v___x_672_);
v___x_21097__boxed_697_ = lean_unbox(v___x_673_);
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_668_, v_alts_669_, v___x_670_, v___x_21095__boxed_695_, v___x_21096__boxed_696_, v___x_21097__boxed_697_, v___x_674_, v___x_675_, v___x_676_, v_ism2_677_, v_motive_678_, v_a_679_, v_val_680_, v_indName_681_, v_v_682_, v___x_683_, v_params_684_, v___x_685_, v___x_686_, v___x_687_, v_zs1_688_, v_ctorRet1_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object* v_tail_702_, lean_object* v_params_703_, lean_object* v_alts_704_, lean_object* v___x_705_, lean_object* v_ism2_706_, lean_object* v_motive_707_, lean_object* v_val_708_, lean_object* v_indName_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v___x_712_, size_t v_sz_713_, size_t v_i_714_, lean_object* v_bs_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
uint8_t v___x_721_; 
v___x_721_ = lean_usize_dec_lt(v_i_714_, v_sz_713_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; 
lean_dec_ref(v___x_712_);
lean_dec(v___x_711_);
lean_dec(v___x_710_);
lean_dec(v_indName_709_);
lean_dec_ref(v_val_708_);
lean_dec_ref(v_motive_707_);
lean_dec_ref(v_ism2_706_);
lean_dec(v___x_705_);
lean_dec_ref(v_alts_704_);
lean_dec_ref(v_params_703_);
lean_dec(v_tail_702_);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v_bs_715_);
return v___x_722_;
}
else
{
lean_object* v___x_723_; uint8_t v___x_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v_v_728_; lean_object* v___x_729_; lean_object* v_bs_x27_730_; lean_object* v___y_732_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_723_ = l_Lean_instInhabitedExpr;
v___x_724_ = 0;
v___x_725_ = 1;
v___x_726_ = lean_unsigned_to_nat(1u);
v___x_727_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v_v_728_ = lean_array_uget(v_bs_715_, v_i_714_);
v___x_729_ = lean_unsigned_to_nat(0u);
v_bs_x27_730_ = lean_array_uset(v_bs_715_, v_i_714_, v___x_729_);
v___x_746_ = lean_usize_to_nat(v_i_714_);
lean_inc(v_tail_702_);
lean_inc(v_v_728_);
v___x_747_ = l_Lean_mkConst(v_v_728_, v_tail_702_);
v___x_748_ = l_Lean_mkAppN(v___x_747_, v_params_703_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc_ref(v___x_748_);
v___x_749_ = lean_infer_type(v___x_748_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___f_754_; lean_object* v___x_755_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc_n(v_a_750_, 2);
lean_dec_ref_known(v___x_749_, 1);
v___x_751_ = lean_box(v___x_724_);
v___x_752_ = lean_box(v___x_721_);
v___x_753_ = lean_box(v___x_725_);
lean_inc_ref(v___x_712_);
lean_inc(v___x_711_);
lean_inc_ref(v_params_703_);
lean_inc(v___x_710_);
lean_inc(v_indName_709_);
lean_inc_ref(v_val_708_);
lean_inc_ref(v_motive_707_);
lean_inc_ref(v_ism2_706_);
lean_inc(v___x_705_);
lean_inc_ref(v_alts_704_);
v___f_754_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed), 27, 20);
lean_closure_set(v___f_754_, 0, v___x_723_);
lean_closure_set(v___f_754_, 1, v_alts_704_);
lean_closure_set(v___f_754_, 2, v___x_746_);
lean_closure_set(v___f_754_, 3, v___x_751_);
lean_closure_set(v___f_754_, 4, v___x_752_);
lean_closure_set(v___f_754_, 5, v___x_753_);
lean_closure_set(v___f_754_, 6, v___x_748_);
lean_closure_set(v___f_754_, 7, v___x_726_);
lean_closure_set(v___f_754_, 8, v___x_705_);
lean_closure_set(v___f_754_, 9, v_ism2_706_);
lean_closure_set(v___f_754_, 10, v_motive_707_);
lean_closure_set(v___f_754_, 11, v_a_750_);
lean_closure_set(v___f_754_, 12, v_val_708_);
lean_closure_set(v___f_754_, 13, v_indName_709_);
lean_closure_set(v___f_754_, 14, v_v_728_);
lean_closure_set(v___f_754_, 15, v___x_710_);
lean_closure_set(v___f_754_, 16, v_params_703_);
lean_closure_set(v___f_754_, 17, v___x_711_);
lean_closure_set(v___f_754_, 18, v___x_712_);
lean_closure_set(v___f_754_, 19, v___x_727_);
v___x_755_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_750_, v___f_754_, v___x_724_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
v___y_732_ = v___x_755_;
goto v___jp_731_;
}
else
{
lean_dec_ref(v___x_748_);
lean_dec(v___x_746_);
lean_dec(v_v_728_);
v___y_732_ = v___x_749_;
goto v___jp_731_;
}
v___jp_731_:
{
if (lean_obj_tag(v___y_732_) == 0)
{
lean_object* v_a_733_; size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; 
v_a_733_ = lean_ctor_get(v___y_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___y_732_, 1);
v___x_734_ = ((size_t)1ULL);
v___x_735_ = lean_usize_add(v_i_714_, v___x_734_);
v___x_736_ = lean_array_uset(v_bs_x27_730_, v_i_714_, v_a_733_);
v_i_714_ = v___x_735_;
v_bs_715_ = v___x_736_;
goto _start;
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec_ref(v_bs_x27_730_);
lean_dec_ref(v___x_712_);
lean_dec(v___x_711_);
lean_dec(v___x_710_);
lean_dec(v_indName_709_);
lean_dec_ref(v_val_708_);
lean_dec_ref(v_motive_707_);
lean_dec_ref(v_ism2_706_);
lean_dec(v___x_705_);
lean_dec_ref(v_alts_704_);
lean_dec_ref(v_params_703_);
lean_dec(v_tail_702_);
v_a_738_ = lean_ctor_get(v___y_732_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___y_732_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___y_732_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___y_732_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_tail_756_ = _args[0];
lean_object* v_params_757_ = _args[1];
lean_object* v_alts_758_ = _args[2];
lean_object* v___x_759_ = _args[3];
lean_object* v_ism2_760_ = _args[4];
lean_object* v_motive_761_ = _args[5];
lean_object* v_val_762_ = _args[6];
lean_object* v_indName_763_ = _args[7];
lean_object* v___x_764_ = _args[8];
lean_object* v___x_765_ = _args[9];
lean_object* v___x_766_ = _args[10];
lean_object* v_sz_767_ = _args[11];
lean_object* v_i_768_ = _args[12];
lean_object* v_bs_769_ = _args[13];
lean_object* v___y_770_ = _args[14];
lean_object* v___y_771_ = _args[15];
lean_object* v___y_772_ = _args[16];
lean_object* v___y_773_ = _args[17];
lean_object* v___y_774_ = _args[18];
_start:
{
size_t v_sz_boxed_775_; size_t v_i_boxed_776_; lean_object* v_res_777_; 
v_sz_boxed_775_ = lean_unbox_usize(v_sz_767_);
lean_dec(v_sz_767_);
v_i_boxed_776_ = lean_unbox_usize(v_i_768_);
lean_dec(v_i_768_);
v_res_777_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_756_, v_params_757_, v_alts_758_, v___x_759_, v_ism2_760_, v_motive_761_, v_val_762_, v_indName_763_, v___x_764_, v___x_765_, v___x_766_, v_sz_boxed_775_, v_i_boxed_776_, v_bs_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_778_, lean_object* v___x_779_, lean_object* v_a_780_, lean_object* v_ism1_781_, uint8_t v___x_782_, uint8_t v___x_783_, uint8_t v___x_784_, lean_object* v_name_785_, lean_object* v___x_786_, lean_object* v_params_787_, lean_object* v___x_788_, lean_object* v_tail_789_, lean_object* v_alts_790_, lean_object* v_numParams_791_, lean_object* v_ism2_792_, lean_object* v_val_793_, lean_object* v_indName_794_, lean_object* v___x_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v_heq_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_inc_ref(v_motive_778_);
v___x_804_ = l_Lean_mkAppN(v_motive_778_, v___x_779_);
v___x_805_ = l_Lean_mkArrow(v_a_780_, v___x_804_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v___x_807_ = l_Lean_Meta_mkLambdaFVars(v_ism1_781_, v_a_806_, v___x_782_, v___x_783_, v___x_782_, v___x_783_, v___x_784_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; size_t v_sz_813_; size_t v___x_814_; lean_object* v___x_815_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
lean_inc(v___x_786_);
v___x_809_ = l_Lean_mkConst(v_name_785_, v___x_786_);
v___x_810_ = l_Lean_mkAppN(v___x_809_, v_params_787_);
v___x_811_ = l_Lean_Expr_app___override(v___x_810_, v_a_808_);
v___x_812_ = l_Lean_mkAppN(v___x_811_, v_ism1_781_);
v_sz_813_ = lean_array_size(v___x_788_);
v___x_814_ = ((size_t)0ULL);
lean_inc_ref(v_motive_778_);
lean_inc_ref(v_ism2_792_);
lean_inc_ref(v_alts_790_);
lean_inc_ref(v_params_787_);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_789_, v_params_787_, v_alts_790_, v_numParams_791_, v_ism2_792_, v_motive_778_, v_val_793_, v_indName_794_, v___x_786_, v___x_795_, v___x_796_, v_sz_813_, v___x_814_, v___x_788_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_815_, 1);
v___x_817_ = l_Lean_mkAppN(v___x_812_, v_a_816_);
lean_dec(v_a_816_);
lean_inc_ref(v_heq_798_);
v___x_818_ = l_Lean_Meta_mkEqSymm(v_heq_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = l_Lean_Expr_app___override(v___x_817_, v_a_819_);
v___x_821_ = lean_mk_empty_array_with_capacity(v___x_797_);
lean_inc_ref(v___x_821_);
v___x_822_ = lean_array_push(v___x_821_, v_motive_778_);
v___x_823_ = l_Array_append___redArg(v_params_787_, v___x_822_);
lean_dec_ref(v___x_822_);
v___x_824_ = l_Array_append___redArg(v___x_823_, v_ism1_781_);
v___x_825_ = l_Array_append___redArg(v___x_824_, v_ism2_792_);
lean_dec_ref(v_ism2_792_);
v___x_826_ = lean_array_push(v___x_821_, v_heq_798_);
v___x_827_ = l_Array_append___redArg(v___x_825_, v___x_826_);
lean_dec_ref(v___x_826_);
v___x_828_ = l_Array_append___redArg(v___x_827_, v_alts_790_);
lean_dec_ref(v_alts_790_);
v___x_829_ = l_Lean_Meta_mkLambdaFVars(v___x_828_, v___x_820_, v___x_782_, v___x_783_, v___x_782_, v___x_783_, v___x_784_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec_ref(v___x_828_);
return v___x_829_;
}
else
{
lean_dec_ref(v___x_817_);
lean_dec_ref(v_heq_798_);
lean_dec_ref(v_ism2_792_);
lean_dec_ref(v_alts_790_);
lean_dec_ref(v_params_787_);
lean_dec_ref(v_motive_778_);
return v___x_818_;
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec_ref(v___x_812_);
lean_dec_ref(v_heq_798_);
lean_dec_ref(v_ism2_792_);
lean_dec_ref(v_alts_790_);
lean_dec_ref(v_params_787_);
lean_dec_ref(v_motive_778_);
v_a_830_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_815_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_815_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_835_; 
if (v_isShared_833_ == 0)
{
v___x_835_ = v___x_832_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_830_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
else
{
lean_dec_ref(v_heq_798_);
lean_dec_ref(v___x_796_);
lean_dec(v___x_795_);
lean_dec(v_indName_794_);
lean_dec_ref(v_val_793_);
lean_dec_ref(v_ism2_792_);
lean_dec(v_numParams_791_);
lean_dec_ref(v_alts_790_);
lean_dec(v_tail_789_);
lean_dec_ref(v___x_788_);
lean_dec_ref(v_params_787_);
lean_dec(v___x_786_);
lean_dec(v_name_785_);
lean_dec_ref(v_motive_778_);
return v___x_807_;
}
}
else
{
lean_dec_ref(v_heq_798_);
lean_dec_ref(v___x_796_);
lean_dec(v___x_795_);
lean_dec(v_indName_794_);
lean_dec_ref(v_val_793_);
lean_dec_ref(v_ism2_792_);
lean_dec(v_numParams_791_);
lean_dec_ref(v_alts_790_);
lean_dec(v_tail_789_);
lean_dec_ref(v___x_788_);
lean_dec_ref(v_params_787_);
lean_dec(v___x_786_);
lean_dec(v_name_785_);
lean_dec_ref(v_motive_778_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object** _args){
lean_object* v_motive_838_ = _args[0];
lean_object* v___x_839_ = _args[1];
lean_object* v_a_840_ = _args[2];
lean_object* v_ism1_841_ = _args[3];
lean_object* v___x_842_ = _args[4];
lean_object* v___x_843_ = _args[5];
lean_object* v___x_844_ = _args[6];
lean_object* v_name_845_ = _args[7];
lean_object* v___x_846_ = _args[8];
lean_object* v_params_847_ = _args[9];
lean_object* v___x_848_ = _args[10];
lean_object* v_tail_849_ = _args[11];
lean_object* v_alts_850_ = _args[12];
lean_object* v_numParams_851_ = _args[13];
lean_object* v_ism2_852_ = _args[14];
lean_object* v_val_853_ = _args[15];
lean_object* v_indName_854_ = _args[16];
lean_object* v___x_855_ = _args[17];
lean_object* v___x_856_ = _args[18];
lean_object* v___x_857_ = _args[19];
lean_object* v_heq_858_ = _args[20];
lean_object* v___y_859_ = _args[21];
lean_object* v___y_860_ = _args[22];
lean_object* v___y_861_ = _args[23];
lean_object* v___y_862_ = _args[24];
lean_object* v___y_863_ = _args[25];
_start:
{
uint8_t v___x_21326__boxed_864_; uint8_t v___x_21327__boxed_865_; uint8_t v___x_21328__boxed_866_; lean_object* v_res_867_; 
v___x_21326__boxed_864_ = lean_unbox(v___x_842_);
v___x_21327__boxed_865_ = lean_unbox(v___x_843_);
v___x_21328__boxed_866_ = lean_unbox(v___x_844_);
v_res_867_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_838_, v___x_839_, v_a_840_, v_ism1_841_, v___x_21326__boxed_864_, v___x_21327__boxed_865_, v___x_21328__boxed_866_, v_name_845_, v___x_846_, v_params_847_, v___x_848_, v_tail_849_, v_alts_850_, v_numParams_851_, v_ism2_852_, v_val_853_, v_indName_854_, v___x_855_, v___x_856_, v___x_857_, v_heq_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___x_857_);
lean_dec_ref(v_ism1_841_);
lean_dec_ref(v___x_839_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_868_, lean_object* v_tail_869_, lean_object* v_params_870_, lean_object* v_ism1_871_, lean_object* v_ism2_872_, lean_object* v_motive_873_, lean_object* v___x_874_, uint8_t v___x_875_, uint8_t v___x_876_, uint8_t v___x_877_, lean_object* v_name_878_, lean_object* v___x_879_, lean_object* v___x_880_, lean_object* v_numParams_881_, lean_object* v_val_882_, lean_object* v___x_883_, lean_object* v___x_884_, lean_object* v_alts_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
lean_inc(v_indName_868_);
v___x_891_ = l_Lean_mkCtorIdxName(v_indName_868_);
lean_inc(v_tail_869_);
v___x_892_ = l_Lean_mkConst(v___x_891_, v_tail_869_);
lean_inc_ref_n(v_params_870_, 2);
v___x_893_ = l_Array_append___redArg(v_params_870_, v_ism1_871_);
lean_inc_ref(v___x_892_);
v___x_894_ = l_Lean_mkAppN(v___x_892_, v___x_893_);
lean_dec_ref(v___x_893_);
v___x_895_ = l_Array_append___redArg(v_params_870_, v_ism2_872_);
v___x_896_ = l_Lean_mkAppN(v___x_892_, v___x_895_);
lean_dec_ref(v___x_895_);
lean_inc_ref(v___x_896_);
lean_inc_ref(v___x_894_);
v___x_897_ = l_Lean_Meta_mkEq(v___x_894_, v___x_896_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
lean_inc_ref(v___x_896_);
v___x_899_ = l_Lean_Meta_mkEq(v___x_896_, v___x_894_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___f_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = lean_box(v___x_875_);
v___x_902_ = lean_box(v___x_876_);
v___x_903_ = lean_box(v___x_877_);
v___f_904_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__0___boxed), 26, 20);
lean_closure_set(v___f_904_, 0, v_motive_873_);
lean_closure_set(v___f_904_, 1, v___x_874_);
lean_closure_set(v___f_904_, 2, v_a_900_);
lean_closure_set(v___f_904_, 3, v_ism1_871_);
lean_closure_set(v___f_904_, 4, v___x_901_);
lean_closure_set(v___f_904_, 5, v___x_902_);
lean_closure_set(v___f_904_, 6, v___x_903_);
lean_closure_set(v___f_904_, 7, v_name_878_);
lean_closure_set(v___f_904_, 8, v___x_879_);
lean_closure_set(v___f_904_, 9, v_params_870_);
lean_closure_set(v___f_904_, 10, v___x_880_);
lean_closure_set(v___f_904_, 11, v_tail_869_);
lean_closure_set(v___f_904_, 12, v_alts_885_);
lean_closure_set(v___f_904_, 13, v_numParams_881_);
lean_closure_set(v___f_904_, 14, v_ism2_872_);
lean_closure_set(v___f_904_, 15, v_val_882_);
lean_closure_set(v___f_904_, 16, v_indName_868_);
lean_closure_set(v___f_904_, 17, v___x_883_);
lean_closure_set(v___f_904_, 18, v___x_896_);
lean_closure_set(v___f_904_, 19, v___x_884_);
v___x_905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_906_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_905_, v_a_898_, v___f_904_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_906_;
}
else
{
lean_dec(v_a_898_);
lean_dec_ref(v___x_896_);
lean_dec_ref(v_alts_885_);
lean_dec(v___x_884_);
lean_dec(v___x_883_);
lean_dec_ref(v_val_882_);
lean_dec(v_numParams_881_);
lean_dec_ref(v___x_880_);
lean_dec(v___x_879_);
lean_dec(v_name_878_);
lean_dec_ref(v___x_874_);
lean_dec_ref(v_motive_873_);
lean_dec_ref(v_ism2_872_);
lean_dec_ref(v_ism1_871_);
lean_dec_ref(v_params_870_);
lean_dec(v_tail_869_);
lean_dec(v_indName_868_);
return v___x_899_;
}
}
else
{
lean_dec_ref(v___x_896_);
lean_dec_ref(v___x_894_);
lean_dec_ref(v_alts_885_);
lean_dec(v___x_884_);
lean_dec(v___x_883_);
lean_dec_ref(v_val_882_);
lean_dec(v_numParams_881_);
lean_dec_ref(v___x_880_);
lean_dec(v___x_879_);
lean_dec(v_name_878_);
lean_dec_ref(v___x_874_);
lean_dec_ref(v_motive_873_);
lean_dec_ref(v_ism2_872_);
lean_dec_ref(v_ism1_871_);
lean_dec_ref(v_params_870_);
lean_dec(v_tail_869_);
lean_dec(v_indName_868_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object** _args){
lean_object* v_indName_907_ = _args[0];
lean_object* v_tail_908_ = _args[1];
lean_object* v_params_909_ = _args[2];
lean_object* v_ism1_910_ = _args[3];
lean_object* v_ism2_911_ = _args[4];
lean_object* v_motive_912_ = _args[5];
lean_object* v___x_913_ = _args[6];
lean_object* v___x_914_ = _args[7];
lean_object* v___x_915_ = _args[8];
lean_object* v___x_916_ = _args[9];
lean_object* v_name_917_ = _args[10];
lean_object* v___x_918_ = _args[11];
lean_object* v___x_919_ = _args[12];
lean_object* v_numParams_920_ = _args[13];
lean_object* v_val_921_ = _args[14];
lean_object* v___x_922_ = _args[15];
lean_object* v___x_923_ = _args[16];
lean_object* v_alts_924_ = _args[17];
lean_object* v___y_925_ = _args[18];
lean_object* v___y_926_ = _args[19];
lean_object* v___y_927_ = _args[20];
lean_object* v___y_928_ = _args[21];
lean_object* v___y_929_ = _args[22];
_start:
{
uint8_t v___x_21449__boxed_930_; uint8_t v___x_21450__boxed_931_; uint8_t v___x_21451__boxed_932_; lean_object* v_res_933_; 
v___x_21449__boxed_930_ = lean_unbox(v___x_914_);
v___x_21450__boxed_931_ = lean_unbox(v___x_915_);
v___x_21451__boxed_932_ = lean_unbox(v___x_916_);
v_res_933_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_907_, v_tail_908_, v_params_909_, v_ism1_910_, v_ism2_911_, v_motive_912_, v___x_913_, v___x_21449__boxed_930_, v___x_21450__boxed_931_, v___x_21451__boxed_932_, v_name_917_, v___x_918_, v___x_919_, v_numParams_920_, v_val_921_, v___x_922_, v___x_923_, v_alts_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_941_, 0, v_snd_934_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_942_, lean_object* v_x_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_942_, v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v_x_943_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_950_, size_t v_i_951_, lean_object* v_bs_952_){
_start:
{
uint8_t v___x_953_; 
v___x_953_ = lean_usize_dec_lt(v_i_951_, v_sz_950_);
if (v___x_953_ == 0)
{
return v_bs_952_;
}
else
{
lean_object* v_v_954_; lean_object* v_fst_955_; lean_object* v_snd_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_970_; 
v_v_954_ = lean_array_uget(v_bs_952_, v_i_951_);
v_fst_955_ = lean_ctor_get(v_v_954_, 0);
v_snd_956_ = lean_ctor_get(v_v_954_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_v_954_);
if (v_isSharedCheck_970_ == 0)
{
v___x_958_ = v_v_954_;
v_isShared_959_ = v_isSharedCheck_970_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_snd_956_);
lean_inc(v_fst_955_);
lean_dec(v_v_954_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_970_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v_bs_x27_961_; lean_object* v___f_962_; lean_object* v___x_964_; 
v___x_960_ = lean_unsigned_to_nat(0u);
v_bs_x27_961_ = lean_array_uset(v_bs_952_, v_i_951_, v___x_960_);
v___f_962_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_962_, 0, v_snd_956_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 1, v___f_962_);
v___x_964_ = v___x_958_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_fst_955_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___f_962_);
v___x_964_ = v_reuseFailAlloc_969_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
size_t v___x_965_; size_t v___x_966_; lean_object* v___x_967_; 
v___x_965_ = ((size_t)1ULL);
v___x_966_ = lean_usize_add(v_i_951_, v___x_965_);
v___x_967_ = lean_array_uset(v_bs_x27_961_, v_i_951_, v___x_964_);
v_i_951_ = v___x_966_;
v_bs_952_ = v___x_967_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_971_, lean_object* v_i_972_, lean_object* v_bs_973_){
_start:
{
size_t v_sz_boxed_974_; size_t v_i_boxed_975_; lean_object* v_res_976_; 
v_sz_boxed_974_ = lean_unbox_usize(v_sz_971_);
lean_dec(v_sz_971_);
v_i_boxed_975_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_974_, v_i_boxed_975_, v_bs_973_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object* v___x_977_, lean_object* v___x_978_, lean_object* v_a_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_20333__overap_985_; lean_object* v___x_986_; 
v___x_20333__overap_985_ = l_instInhabitedOfMonad___redArg(v___x_977_, v___x_978_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
v___x_986_ = lean_apply_5(v___x_20333__overap_985_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, lean_box(0));
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object* v___x_987_, lean_object* v___x_988_, lean_object* v_a_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_987_, v___x_988_, v_a_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec_ref(v_a_989_);
return v_res_995_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l_instMonadEIO___redArg();
return v___x_996_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0);
v___x_998_ = l_StateRefT_x27_instMonad___redArg(v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object* v_acc_1003_, lean_object* v_declInfos_1004_, lean_object* v_k_1005_, lean_object* v_kind_1006_, lean_object* v_x_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
uint8_t v_kind_boxed_1013_; lean_object* v_res_1014_; 
v_kind_boxed_1013_ = lean_unbox(v_kind_1006_);
v_res_1014_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_1003_, v_declInfos_1004_, v_k_1005_, v_kind_boxed_1013_, v_x_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_declInfos_1015_, lean_object* v_k_1016_, uint8_t v_kind_1017_, lean_object* v_acc_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v_toApplicative_1025_; lean_object* v_toFunctor_1026_; lean_object* v_toSeq_1027_; lean_object* v_toSeqLeft_1028_; lean_object* v_toSeqRight_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v_toApplicative_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1091_; 
v___x_1024_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_1025_ = lean_ctor_get(v___x_1024_, 0);
v_toFunctor_1026_ = lean_ctor_get(v_toApplicative_1025_, 0);
v_toSeq_1027_ = lean_ctor_get(v_toApplicative_1025_, 2);
v_toSeqLeft_1028_ = lean_ctor_get(v_toApplicative_1025_, 3);
v_toSeqRight_1029_ = lean_ctor_get(v_toApplicative_1025_, 4);
v___f_1030_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_1031_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_1026_, 2);
v___f_1032_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1032_, 0, v_toFunctor_1026_);
v___f_1033_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1033_, 0, v_toFunctor_1026_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___f_1032_);
lean_ctor_set(v___x_1034_, 1, v___f_1033_);
lean_inc(v_toSeqRight_1029_);
v___f_1035_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1035_, 0, v_toSeqRight_1029_);
lean_inc(v_toSeqLeft_1028_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toSeqLeft_1028_);
lean_inc(v_toSeq_1027_);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toSeq_1027_);
v___x_1038_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1034_);
lean_ctor_set(v___x_1038_, 1, v___f_1030_);
lean_ctor_set(v___x_1038_, 2, v___f_1037_);
lean_ctor_set(v___x_1038_, 3, v___f_1036_);
lean_ctor_set(v___x_1038_, 4, v___f_1035_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___f_1031_);
v___x_1040_ = l_StateRefT_x27_instMonad___redArg(v___x_1039_);
v_toApplicative_1041_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; 
v_unused_1092_ = lean_ctor_get(v___x_1040_, 1);
lean_dec(v_unused_1092_);
v___x_1043_ = v___x_1040_;
v_isShared_1044_ = v_isSharedCheck_1091_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_toApplicative_1041_);
lean_dec(v___x_1040_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1091_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v_toFunctor_1045_; lean_object* v_toSeq_1046_; lean_object* v_toSeqLeft_1047_; lean_object* v_toSeqRight_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1089_; 
v_toFunctor_1045_ = lean_ctor_get(v_toApplicative_1041_, 0);
v_toSeq_1046_ = lean_ctor_get(v_toApplicative_1041_, 2);
v_toSeqLeft_1047_ = lean_ctor_get(v_toApplicative_1041_, 3);
v_toSeqRight_1048_ = lean_ctor_get(v_toApplicative_1041_, 4);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_toApplicative_1041_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v_toApplicative_1041_, 1);
lean_dec(v_unused_1090_);
v___x_1050_ = v_toApplicative_1041_;
v_isShared_1051_ = v_isSharedCheck_1089_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_toSeqRight_1048_);
lean_inc(v_toSeqLeft_1047_);
lean_inc(v_toSeq_1046_);
lean_inc(v_toFunctor_1045_);
lean_dec(v_toApplicative_1041_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1089_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___x_1061_; 
v___f_1052_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_1053_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_1045_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toFunctor_1045_);
v___f_1055_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1055_, 0, v_toFunctor_1045_);
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___f_1054_);
lean_ctor_set(v___x_1056_, 1, v___f_1055_);
v___f_1057_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1057_, 0, v_toSeqRight_1048_);
v___f_1058_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1058_, 0, v_toSeqLeft_1047_);
v___f_1059_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1059_, 0, v_toSeq_1046_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 4, v___f_1057_);
lean_ctor_set(v___x_1050_, 3, v___f_1058_);
lean_ctor_set(v___x_1050_, 2, v___f_1059_);
lean_ctor_set(v___x_1050_, 1, v___f_1052_);
lean_ctor_set(v___x_1050_, 0, v___x_1056_);
v___x_1061_ = v___x_1050_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___f_1052_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v___f_1059_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v___f_1058_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v___f_1057_);
v___x_1061_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1063_; 
if (v_isShared_1044_ == 0)
{
lean_ctor_set(v___x_1043_, 1, v___f_1053_);
lean_ctor_set(v___x_1043_, 0, v___x_1061_);
v___x_1063_ = v___x_1043_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___f_1053_);
v___x_1063_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v___x_1064_ = lean_array_get_size(v_acc_1018_);
v___x_1065_ = lean_array_get_size(v_declInfos_1015_);
v___x_1066_ = lean_nat_dec_lt(v___x_1064_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1067_; 
lean_dec_ref(v___x_1063_);
lean_dec_ref(v_declInfos_1015_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
v___x_1067_ = lean_apply_6(v_k_1016_, v_acc_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
return v___x_1067_;
}
else
{
lean_object* v___x_1068_; uint8_t v___x_1069_; lean_object* v___x_1070_; lean_object* v___f_1071_; lean_object* v___f_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v_snd_1077_; lean_object* v_fst_1078_; lean_object* v_fst_1079_; lean_object* v_snd_1080_; lean_object* v___x_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = 0;
v___x_1070_ = l_Lean_instInhabitedExpr;
v___f_1071_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1071_, 0, v___x_1063_);
lean_closure_set(v___f_1071_, 1, v___x_1070_);
v___f_1072_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1072_, 0, v___f_1071_);
v___x_1073_ = lean_box(v___x_1069_);
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v___f_1072_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1068_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_array_get(v___x_1075_, v_declInfos_1015_, v___x_1064_);
lean_dec_ref_known(v___x_1075_, 2);
v_snd_1077_ = lean_ctor_get(v___x_1076_, 1);
lean_inc(v_snd_1077_);
v_fst_1078_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_fst_1078_);
lean_dec(v___x_1076_);
v_fst_1079_ = lean_ctor_get(v_snd_1077_, 0);
lean_inc(v_fst_1079_);
v_snd_1080_ = lean_ctor_get(v_snd_1077_, 1);
lean_inc(v_snd_1080_);
lean_dec(v_snd_1077_);
v___x_1081_ = lean_box(v_kind_1017_);
lean_inc_ref(v_acc_1018_);
v___f_1082_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1082_, 0, v_acc_1018_);
lean_closure_set(v___f_1082_, 1, v_declInfos_1015_);
lean_closure_set(v___f_1082_, 2, v_k_1016_);
lean_closure_set(v___f_1082_, 3, v___x_1081_);
lean_inc(v___y_1022_);
lean_inc_ref(v___y_1021_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
v___x_1083_ = lean_apply_6(v_snd_1080_, v_acc_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, lean_box(0));
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v___x_1085_ = lean_unbox(v_fst_1079_);
lean_dec(v_fst_1079_);
v___x_1086_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1078_, v___x_1085_, v_a_1084_, v___f_1082_, v_kind_1017_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
return v___x_1086_;
}
else
{
lean_dec_ref(v___f_1082_);
lean_dec(v_fst_1079_);
lean_dec(v_fst_1078_);
return v___x_1083_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(lean_object* v_acc_1093_, lean_object* v_declInfos_1094_, lean_object* v_k_1095_, uint8_t v_kind_1096_, lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = lean_array_push(v_acc_1093_, v_x_1097_);
v___x_1104_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1094_, v_k_1095_, v_kind_1096_, v___x_1103_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object* v_declInfos_1105_, lean_object* v_k_1106_, lean_object* v_kind_1107_, lean_object* v_acc_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
uint8_t v_kind_boxed_1114_; lean_object* v_res_1115_; 
v_kind_boxed_1114_ = lean_unbox(v_kind_1107_);
v_res_1115_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1105_, v_k_1106_, v_kind_boxed_1114_, v_acc_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object* v_declInfos_1118_, lean_object* v_k_1119_, uint8_t v_kind_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_1127_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1118_, v_k_1119_, v_kind_1120_, v___x_1126_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object* v_declInfos_1128_, lean_object* v_k_1129_, lean_object* v_kind_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
uint8_t v_kind_boxed_1136_; lean_object* v_res_1137_; 
v_kind_boxed_1136_ = lean_unbox(v_kind_1130_);
v_res_1137_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_declInfos_1128_, v_k_1129_, v_kind_boxed_1136_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t v_sz_1138_, size_t v_i_1139_, lean_object* v_bs_1140_){
_start:
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_usize_dec_lt(v_i_1139_, v_sz_1138_);
if (v___x_1141_ == 0)
{
return v_bs_1140_;
}
else
{
lean_object* v_v_1142_; lean_object* v_fst_1143_; lean_object* v_snd_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1160_; 
v_v_1142_ = lean_array_uget(v_bs_1140_, v_i_1139_);
v_fst_1143_ = lean_ctor_get(v_v_1142_, 0);
v_snd_1144_ = lean_ctor_get(v_v_1142_, 1);
v_isSharedCheck_1160_ = !lean_is_exclusive(v_v_1142_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1146_ = v_v_1142_;
v_isShared_1147_ = v_isSharedCheck_1160_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_snd_1144_);
lean_inc(v_fst_1143_);
lean_dec(v_v_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1160_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v_bs_x27_1149_; uint8_t v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1148_ = lean_unsigned_to_nat(0u);
v_bs_x27_1149_ = lean_array_uset(v_bs_1140_, v_i_1139_, v___x_1148_);
v___x_1150_ = 0;
v___x_1151_ = lean_box(v___x_1150_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1151_);
v___x_1153_ = v___x_1146_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_snd_1144_);
v___x_1153_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; 
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v_fst_1143_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v___x_1155_ = ((size_t)1ULL);
v___x_1156_ = lean_usize_add(v_i_1139_, v___x_1155_);
v___x_1157_ = lean_array_uset(v_bs_x27_1149_, v_i_1139_, v___x_1154_);
v_i_1139_ = v___x_1156_;
v_bs_1140_ = v___x_1157_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_sz_1161_, lean_object* v_i_1162_, lean_object* v_bs_1163_){
_start:
{
size_t v_sz_boxed_1164_; size_t v_i_boxed_1165_; lean_object* v_res_1166_; 
v_sz_boxed_1164_ = lean_unbox_usize(v_sz_1161_);
lean_dec(v_sz_1161_);
v_i_boxed_1165_ = lean_unbox_usize(v_i_1162_);
lean_dec(v_i_1162_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_1164_, v_i_boxed_1165_, v_bs_1163_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_declInfos_1167_, lean_object* v_k_1168_, uint8_t v_kind_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
size_t v_sz_1175_; size_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v_sz_1175_ = lean_array_size(v_declInfos_1167_);
v___x_1176_ = ((size_t)0ULL);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1175_, v___x_1176_, v_declInfos_1167_);
v___x_1178_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v___x_1177_, v_k_1168_, v_kind_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_declInfos_1179_, lean_object* v_k_1180_, lean_object* v_kind_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v_kind_boxed_1187_; lean_object* v_res_1188_; 
v_kind_boxed_1187_ = lean_unbox(v_kind_1181_);
v_res_1188_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1179_, v_k_1180_, v_kind_boxed_1187_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_declInfos_1189_, lean_object* v_k_1190_, uint8_t v_kind_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
size_t v_sz_1197_; size_t v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v_sz_1197_ = lean_array_size(v_declInfos_1189_);
v___x_1198_ = ((size_t)0ULL);
v___x_1199_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1197_, v___x_1198_, v_declInfos_1189_);
v___x_1200_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_1199_, v_k_1190_, v_kind_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_declInfos_1201_, lean_object* v_k_1202_, lean_object* v_kind_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
uint8_t v_kind_boxed_1209_; lean_object* v_res_1210_; 
v_kind_boxed_1209_ = lean_unbox(v_kind_1203_);
v_res_1210_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1201_, v_k_1202_, v_kind_boxed_1209_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
return v_res_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_1212_, lean_object* v_dummy_1213_, lean_object* v___x_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v_motive_1217_, lean_object* v_zs1_1218_, uint8_t v___x_1219_, uint8_t v___x_1220_, uint8_t v___x_1221_, lean_object* v_v_1222_, lean_object* v___x_1223_, lean_object* v_zs2_1224_, lean_object* v_ctorRet2_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1231_ = l_Lean_mkAppN(v___x_1212_, v_zs2_1224_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
v___x_1232_ = lean_whnf(v_ctorRet2_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v_a_1233_; lean_object* v_nargs_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref_known(v___x_1232_, 1);
v_nargs_1234_ = l_Lean_Expr_getAppNumArgs(v_a_1233_);
lean_inc(v_nargs_1234_);
v___x_1235_ = lean_mk_array(v_nargs_1234_, v_dummy_1213_);
v___x_1236_ = lean_nat_sub(v_nargs_1234_, v___x_1214_);
lean_dec(v_nargs_1234_);
v___x_1237_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1233_, v___x_1235_, v___x_1236_);
v___x_1238_ = lean_array_get_size(v___x_1237_);
v___x_1239_ = l_Array_toSubarray___redArg(v___x_1237_, v___x_1215_, v___x_1238_);
v___x_1240_ = l_Subarray_copy___redArg(v___x_1239_);
v___x_1241_ = lean_array_push(v___x_1240_, v___x_1231_);
v___x_1242_ = l_Array_append___redArg(v___x_1216_, v___x_1241_);
lean_dec_ref(v___x_1241_);
v___x_1243_ = l_Lean_mkAppN(v_motive_1217_, v___x_1242_);
lean_dec_ref(v___x_1242_);
v___x_1244_ = l_Array_append___redArg(v_zs1_1218_, v_zs2_1224_);
v___x_1245_ = l_Lean_Meta_mkForallFVars(v___x_1244_, v___x_1243_, v___x_1219_, v___x_1220_, v___x_1220_, v___x_1221_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec_ref(v___x_1244_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1265_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1265_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1265_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___y_1251_; 
if (lean_obj_tag(v_v_1222_) == 1)
{
lean_object* v_str_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_str_1256_ = lean_ctor_get(v_v_1222_, 1);
lean_inc_ref(v_str_1256_);
lean_dec_ref_known(v_v_1222_, 2);
v___x_1257_ = lean_box(0);
v___x_1258_ = l_Lean_Name_str___override(v___x_1257_, v_str_1256_);
v___y_1251_ = v___x_1258_;
goto v___jp_1250_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec(v_v_1222_);
v___x_1259_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_1260_ = lean_nat_add(v___x_1223_, v___x_1214_);
v___x_1261_ = l_Nat_reprFast(v___x_1260_);
v___x_1262_ = lean_string_append(v___x_1259_, v___x_1261_);
lean_dec_ref(v___x_1261_);
v___x_1263_ = lean_box(0);
v___x_1264_ = l_Lean_Name_str___override(v___x_1263_, v___x_1262_);
v___y_1251_ = v___x_1264_;
goto v___jp_1250_;
}
v___jp_1250_:
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
v___x_1252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___y_1251_);
lean_ctor_set(v___x_1252_, 1, v_a_1246_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1252_);
v___x_1254_ = v___x_1248_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v_v_1222_);
v_a_1266_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1245_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1245_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1281_; 
lean_dec_ref(v___x_1231_);
lean_dec(v_v_1222_);
lean_dec_ref(v_zs1_1218_);
lean_dec_ref(v_motive_1217_);
lean_dec_ref(v___x_1216_);
lean_dec(v___x_1215_);
lean_dec_ref(v_dummy_1213_);
v_a_1274_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1276_ = v___x_1232_;
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1232_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1281_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_a_1274_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1282_ = _args[0];
lean_object* v_dummy_1283_ = _args[1];
lean_object* v___x_1284_ = _args[2];
lean_object* v___x_1285_ = _args[3];
lean_object* v___x_1286_ = _args[4];
lean_object* v_motive_1287_ = _args[5];
lean_object* v_zs1_1288_ = _args[6];
lean_object* v___x_1289_ = _args[7];
lean_object* v___x_1290_ = _args[8];
lean_object* v___x_1291_ = _args[9];
lean_object* v_v_1292_ = _args[10];
lean_object* v___x_1293_ = _args[11];
lean_object* v_zs2_1294_ = _args[12];
lean_object* v_ctorRet2_1295_ = _args[13];
lean_object* v___y_1296_ = _args[14];
lean_object* v___y_1297_ = _args[15];
lean_object* v___y_1298_ = _args[16];
lean_object* v___y_1299_ = _args[17];
lean_object* v___y_1300_ = _args[18];
_start:
{
uint8_t v___x_21888__boxed_1301_; uint8_t v___x_21889__boxed_1302_; uint8_t v___x_21890__boxed_1303_; lean_object* v_res_1304_; 
v___x_21888__boxed_1301_ = lean_unbox(v___x_1289_);
v___x_21889__boxed_1302_ = lean_unbox(v___x_1290_);
v___x_21890__boxed_1303_ = lean_unbox(v___x_1291_);
v_res_1304_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1282_, v_dummy_1283_, v___x_1284_, v___x_1285_, v___x_1286_, v_motive_1287_, v_zs1_1288_, v___x_21888__boxed_1301_, v___x_21889__boxed_1302_, v___x_21890__boxed_1303_, v_v_1292_, v___x_1293_, v_zs2_1294_, v_ctorRet2_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
lean_dec(v___y_1299_);
lean_dec_ref(v___y_1298_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec_ref(v_zs2_1294_);
lean_dec(v___x_1293_);
lean_dec(v___x_1284_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1305_, lean_object* v___x_1306_, lean_object* v___x_1307_, lean_object* v_motive_1308_, uint8_t v___x_1309_, uint8_t v___x_1310_, uint8_t v___x_1311_, lean_object* v_v_1312_, lean_object* v___x_1313_, lean_object* v_a_1314_, lean_object* v_zs1_1315_, lean_object* v_ctorRet1_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_inc_ref(v___x_1305_);
v___x_1322_ = l_Lean_mkAppN(v___x_1305_, v_zs1_1315_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
v___x_1323_ = lean_whnf(v_ctorRet1_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v_dummy_1325_; lean_object* v_nargs_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___f_1337_; lean_object* v___x_1338_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref_known(v___x_1323_, 1);
v_dummy_1325_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1326_ = l_Lean_Expr_getAppNumArgs(v_a_1324_);
lean_inc(v_nargs_1326_);
v___x_1327_ = lean_mk_array(v_nargs_1326_, v_dummy_1325_);
v___x_1328_ = lean_nat_sub(v_nargs_1326_, v___x_1306_);
lean_dec(v_nargs_1326_);
v___x_1329_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1324_, v___x_1327_, v___x_1328_);
v___x_1330_ = lean_array_get_size(v___x_1329_);
lean_inc(v___x_1307_);
v___x_1331_ = l_Array_toSubarray___redArg(v___x_1329_, v___x_1307_, v___x_1330_);
v___x_1332_ = l_Subarray_copy___redArg(v___x_1331_);
v___x_1333_ = lean_array_push(v___x_1332_, v___x_1322_);
v___x_1334_ = lean_box(v___x_1309_);
v___x_1335_ = lean_box(v___x_1310_);
v___x_1336_ = lean_box(v___x_1311_);
v___f_1337_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1337_, 0, v___x_1305_);
lean_closure_set(v___f_1337_, 1, v_dummy_1325_);
lean_closure_set(v___f_1337_, 2, v___x_1306_);
lean_closure_set(v___f_1337_, 3, v___x_1307_);
lean_closure_set(v___f_1337_, 4, v___x_1333_);
lean_closure_set(v___f_1337_, 5, v_motive_1308_);
lean_closure_set(v___f_1337_, 6, v_zs1_1315_);
lean_closure_set(v___f_1337_, 7, v___x_1334_);
lean_closure_set(v___f_1337_, 8, v___x_1335_);
lean_closure_set(v___f_1337_, 9, v___x_1336_);
lean_closure_set(v___f_1337_, 10, v_v_1312_);
lean_closure_set(v___f_1337_, 11, v___x_1313_);
v___x_1338_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1314_, v___f_1337_, v___x_1309_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
return v___x_1338_;
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_dec_ref(v___x_1322_);
lean_dec_ref(v_zs1_1315_);
lean_dec_ref(v_a_1314_);
lean_dec(v___x_1313_);
lean_dec(v_v_1312_);
lean_dec_ref(v_motive_1308_);
lean_dec(v___x_1307_);
lean_dec(v___x_1306_);
lean_dec_ref(v___x_1305_);
v_a_1339_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1323_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1323_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1347_ = _args[0];
lean_object* v___x_1348_ = _args[1];
lean_object* v___x_1349_ = _args[2];
lean_object* v_motive_1350_ = _args[3];
lean_object* v___x_1351_ = _args[4];
lean_object* v___x_1352_ = _args[5];
lean_object* v___x_1353_ = _args[6];
lean_object* v_v_1354_ = _args[7];
lean_object* v___x_1355_ = _args[8];
lean_object* v_a_1356_ = _args[9];
lean_object* v_zs1_1357_ = _args[10];
lean_object* v_ctorRet1_1358_ = _args[11];
lean_object* v___y_1359_ = _args[12];
lean_object* v___y_1360_ = _args[13];
lean_object* v___y_1361_ = _args[14];
lean_object* v___y_1362_ = _args[15];
lean_object* v___y_1363_ = _args[16];
_start:
{
uint8_t v___x_22029__boxed_1364_; uint8_t v___x_22030__boxed_1365_; uint8_t v___x_22031__boxed_1366_; lean_object* v_res_1367_; 
v___x_22029__boxed_1364_ = lean_unbox(v___x_1351_);
v___x_22030__boxed_1365_ = lean_unbox(v___x_1352_);
v___x_22031__boxed_1366_ = lean_unbox(v___x_1353_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1347_, v___x_1348_, v___x_1349_, v_motive_1350_, v___x_22029__boxed_1364_, v___x_22030__boxed_1365_, v___x_22031__boxed_1366_, v_v_1354_, v___x_1355_, v_a_1356_, v_zs1_1357_, v_ctorRet1_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1368_, lean_object* v_params_1369_, lean_object* v___x_1370_, lean_object* v_motive_1371_, size_t v_sz_1372_, size_t v_i_1373_, lean_object* v_bs_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
uint8_t v___x_1380_; 
v___x_1380_ = lean_usize_dec_lt(v_i_1373_, v_sz_1372_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; 
lean_dec_ref(v_motive_1371_);
lean_dec(v___x_1370_);
lean_dec(v_tail_1368_);
v___x_1381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1381_, 0, v_bs_1374_);
return v___x_1381_;
}
else
{
uint8_t v___x_1382_; uint8_t v___x_1383_; lean_object* v___x_1384_; lean_object* v_v_1385_; lean_object* v___x_1386_; lean_object* v_bs_x27_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1382_ = 0;
v___x_1383_ = 1;
v___x_1384_ = lean_unsigned_to_nat(1u);
v_v_1385_ = lean_array_uget(v_bs_1374_, v_i_1373_);
v___x_1386_ = lean_unsigned_to_nat(0u);
v_bs_x27_1387_ = lean_array_uset(v_bs_1374_, v_i_1373_, v___x_1386_);
v___x_1388_ = lean_usize_to_nat(v_i_1373_);
lean_inc(v_tail_1368_);
lean_inc(v_v_1385_);
v___x_1389_ = l_Lean_mkConst(v_v_1385_, v_tail_1368_);
v___x_1390_ = l_Lean_mkAppN(v___x_1389_, v_params_1369_);
lean_inc(v___y_1378_);
lean_inc_ref(v___y_1377_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc_ref(v___x_1390_);
v___x_1391_ = lean_infer_type(v___x_1390_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___f_1396_; lean_object* v___x_1397_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc_n(v_a_1392_, 2);
lean_dec_ref_known(v___x_1391_, 1);
v___x_1393_ = lean_box(v___x_1382_);
v___x_1394_ = lean_box(v___x_1380_);
v___x_1395_ = lean_box(v___x_1383_);
lean_inc_ref(v_motive_1371_);
lean_inc(v___x_1370_);
v___f_1396_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1396_, 0, v___x_1390_);
lean_closure_set(v___f_1396_, 1, v___x_1384_);
lean_closure_set(v___f_1396_, 2, v___x_1370_);
lean_closure_set(v___f_1396_, 3, v_motive_1371_);
lean_closure_set(v___f_1396_, 4, v___x_1393_);
lean_closure_set(v___f_1396_, 5, v___x_1394_);
lean_closure_set(v___f_1396_, 6, v___x_1395_);
lean_closure_set(v___f_1396_, 7, v_v_1385_);
lean_closure_set(v___f_1396_, 8, v___x_1388_);
lean_closure_set(v___f_1396_, 9, v_a_1392_);
v___x_1397_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1392_, v___f_1396_, v___x_1382_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_a_1398_; size_t v___x_1399_; size_t v___x_1400_; lean_object* v___x_1401_; 
v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_a_1398_);
lean_dec_ref_known(v___x_1397_, 1);
v___x_1399_ = ((size_t)1ULL);
v___x_1400_ = lean_usize_add(v_i_1373_, v___x_1399_);
v___x_1401_ = lean_array_uset(v_bs_x27_1387_, v_i_1373_, v_a_1398_);
v_i_1373_ = v___x_1400_;
v_bs_1374_ = v___x_1401_;
goto _start;
}
else
{
lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1410_; 
lean_dec_ref(v_bs_x27_1387_);
lean_dec_ref(v_motive_1371_);
lean_dec(v___x_1370_);
lean_dec(v_tail_1368_);
v_a_1403_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1410_ == 0)
{
v___x_1405_ = v___x_1397_;
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1397_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1410_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1408_; 
if (v_isShared_1406_ == 0)
{
v___x_1408_ = v___x_1405_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v_a_1403_);
v___x_1408_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
return v___x_1408_;
}
}
}
}
else
{
lean_object* v_a_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1418_; 
lean_dec_ref(v___x_1390_);
lean_dec(v___x_1388_);
lean_dec_ref(v_bs_x27_1387_);
lean_dec(v_v_1385_);
lean_dec_ref(v_motive_1371_);
lean_dec(v___x_1370_);
lean_dec(v_tail_1368_);
v_a_1411_ = lean_ctor_get(v___x_1391_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1391_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1413_ = v___x_1391_;
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_a_1411_);
lean_dec(v___x_1391_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1418_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v___x_1416_; 
if (v_isShared_1414_ == 0)
{
v___x_1416_ = v___x_1413_;
goto v_reusejp_1415_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v_a_1411_);
v___x_1416_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1415_;
}
v_reusejp_1415_:
{
return v___x_1416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1419_, lean_object* v_params_1420_, lean_object* v___x_1421_, lean_object* v_motive_1422_, lean_object* v_sz_1423_, lean_object* v_i_1424_, lean_object* v_bs_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
size_t v_sz_boxed_1431_; size_t v_i_boxed_1432_; lean_object* v_res_1433_; 
v_sz_boxed_1431_ = lean_unbox_usize(v_sz_1423_);
lean_dec(v_sz_1423_);
v_i_boxed_1432_ = lean_unbox_usize(v_i_1424_);
lean_dec(v_i_1424_);
v_res_1433_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1419_, v_params_1420_, v___x_1421_, v_motive_1422_, v_sz_boxed_1431_, v_i_boxed_1432_, v_bs_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec_ref(v_params_1420_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1434_, lean_object* v_indName_1435_, lean_object* v_tail_1436_, lean_object* v_params_1437_, lean_object* v_ism1_1438_, lean_object* v_ism2_1439_, lean_object* v___x_1440_, uint8_t v___x_1441_, uint8_t v___x_1442_, uint8_t v___x_1443_, lean_object* v_name_1444_, lean_object* v___x_1445_, lean_object* v_numParams_1446_, lean_object* v_val_1447_, lean_object* v___x_1448_, lean_object* v___x_1449_, lean_object* v_motive_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___f_1460_; size_t v_sz_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1456_ = lean_array_mk(v_ctors_1434_);
v___x_1457_ = lean_box(v___x_1441_);
v___x_1458_ = lean_box(v___x_1442_);
v___x_1459_ = lean_box(v___x_1443_);
lean_inc(v_numParams_1446_);
lean_inc_ref(v___x_1456_);
lean_inc_ref(v_motive_1450_);
lean_inc_ref(v_params_1437_);
lean_inc(v_tail_1436_);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1460_, 0, v_indName_1435_);
lean_closure_set(v___f_1460_, 1, v_tail_1436_);
lean_closure_set(v___f_1460_, 2, v_params_1437_);
lean_closure_set(v___f_1460_, 3, v_ism1_1438_);
lean_closure_set(v___f_1460_, 4, v_ism2_1439_);
lean_closure_set(v___f_1460_, 5, v_motive_1450_);
lean_closure_set(v___f_1460_, 6, v___x_1440_);
lean_closure_set(v___f_1460_, 7, v___x_1457_);
lean_closure_set(v___f_1460_, 8, v___x_1458_);
lean_closure_set(v___f_1460_, 9, v___x_1459_);
lean_closure_set(v___f_1460_, 10, v_name_1444_);
lean_closure_set(v___f_1460_, 11, v___x_1445_);
lean_closure_set(v___f_1460_, 12, v___x_1456_);
lean_closure_set(v___f_1460_, 13, v_numParams_1446_);
lean_closure_set(v___f_1460_, 14, v_val_1447_);
lean_closure_set(v___f_1460_, 15, v___x_1448_);
lean_closure_set(v___f_1460_, 16, v___x_1449_);
v_sz_1461_ = lean_array_size(v___x_1456_);
v___x_1462_ = ((size_t)0ULL);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1436_, v_params_1437_, v_numParams_1446_, v_motive_1450_, v_sz_1461_, v___x_1462_, v___x_1456_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
lean_dec_ref(v_params_1437_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = 0;
v___x_1466_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_a_1464_, v___f_1460_, v___x_1465_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1466_;
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec_ref(v___f_1460_);
v_a_1467_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1463_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1463_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1475_ = _args[0];
lean_object* v_indName_1476_ = _args[1];
lean_object* v_tail_1477_ = _args[2];
lean_object* v_params_1478_ = _args[3];
lean_object* v_ism1_1479_ = _args[4];
lean_object* v_ism2_1480_ = _args[5];
lean_object* v___x_1481_ = _args[6];
lean_object* v___x_1482_ = _args[7];
lean_object* v___x_1483_ = _args[8];
lean_object* v___x_1484_ = _args[9];
lean_object* v_name_1485_ = _args[10];
lean_object* v___x_1486_ = _args[11];
lean_object* v_numParams_1487_ = _args[12];
lean_object* v_val_1488_ = _args[13];
lean_object* v___x_1489_ = _args[14];
lean_object* v___x_1490_ = _args[15];
lean_object* v_motive_1491_ = _args[16];
lean_object* v___y_1492_ = _args[17];
lean_object* v___y_1493_ = _args[18];
lean_object* v___y_1494_ = _args[19];
lean_object* v___y_1495_ = _args[20];
lean_object* v___y_1496_ = _args[21];
_start:
{
uint8_t v___x_22209__boxed_1497_; uint8_t v___x_22210__boxed_1498_; uint8_t v___x_22211__boxed_1499_; lean_object* v_res_1500_; 
v___x_22209__boxed_1497_ = lean_unbox(v___x_1482_);
v___x_22210__boxed_1498_ = lean_unbox(v___x_1483_);
v___x_22211__boxed_1499_ = lean_unbox(v___x_1484_);
v_res_1500_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1475_, v_indName_1476_, v_tail_1477_, v_params_1478_, v_ism1_1479_, v_ism2_1480_, v___x_1481_, v___x_22209__boxed_1497_, v___x_22210__boxed_1498_, v___x_22211__boxed_1499_, v_name_1485_, v___x_1486_, v_numParams_1487_, v_val_1488_, v___x_1489_, v___x_1490_, v_motive_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1504_, lean_object* v_head_1505_, lean_object* v_ctors_1506_, lean_object* v_indName_1507_, lean_object* v_tail_1508_, lean_object* v_params_1509_, lean_object* v_name_1510_, lean_object* v___x_1511_, lean_object* v_numParams_1512_, lean_object* v_val_1513_, lean_object* v___x_1514_, lean_object* v___x_1515_, lean_object* v_ism2_1516_, lean_object* v_x_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; uint8_t v___x_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___f_1531_; lean_object* v___x_1532_; 
lean_inc_ref(v_ism1_1504_);
v___x_1523_ = l_Array_append___redArg(v_ism1_1504_, v_ism2_1516_);
v___x_1524_ = l_Lean_mkSort(v_head_1505_);
v___x_1525_ = 0;
v___x_1526_ = 1;
v___x_1527_ = 1;
v___x_1528_ = lean_box(v___x_1525_);
v___x_1529_ = lean_box(v___x_1526_);
v___x_1530_ = lean_box(v___x_1527_);
lean_inc_ref(v___x_1523_);
v___f_1531_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 22, 16);
lean_closure_set(v___f_1531_, 0, v_ctors_1506_);
lean_closure_set(v___f_1531_, 1, v_indName_1507_);
lean_closure_set(v___f_1531_, 2, v_tail_1508_);
lean_closure_set(v___f_1531_, 3, v_params_1509_);
lean_closure_set(v___f_1531_, 4, v_ism1_1504_);
lean_closure_set(v___f_1531_, 5, v_ism2_1516_);
lean_closure_set(v___f_1531_, 6, v___x_1523_);
lean_closure_set(v___f_1531_, 7, v___x_1528_);
lean_closure_set(v___f_1531_, 8, v___x_1529_);
lean_closure_set(v___f_1531_, 9, v___x_1530_);
lean_closure_set(v___f_1531_, 10, v_name_1510_);
lean_closure_set(v___f_1531_, 11, v___x_1511_);
lean_closure_set(v___f_1531_, 12, v_numParams_1512_);
lean_closure_set(v___f_1531_, 13, v_val_1513_);
lean_closure_set(v___f_1531_, 14, v___x_1514_);
lean_closure_set(v___f_1531_, 15, v___x_1515_);
v___x_1532_ = l_Lean_Meta_mkForallFVars(v___x_1523_, v___x_1524_, v___x_1525_, v___x_1526_, v___x_1526_, v___x_1527_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec_ref(v___x_1523_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; uint8_t v___x_1535_; lean_object* v___x_1536_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref_known(v___x_1532_, 1);
v___x_1534_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1535_ = 0;
v___x_1536_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1534_, v___x_1527_, v_a_1533_, v___f_1531_, v___x_1535_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
return v___x_1536_;
}
else
{
lean_dec_ref(v___f_1531_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1537_ = _args[0];
lean_object* v_head_1538_ = _args[1];
lean_object* v_ctors_1539_ = _args[2];
lean_object* v_indName_1540_ = _args[3];
lean_object* v_tail_1541_ = _args[4];
lean_object* v_params_1542_ = _args[5];
lean_object* v_name_1543_ = _args[6];
lean_object* v___x_1544_ = _args[7];
lean_object* v_numParams_1545_ = _args[8];
lean_object* v_val_1546_ = _args[9];
lean_object* v___x_1547_ = _args[10];
lean_object* v___x_1548_ = _args[11];
lean_object* v_ism2_1549_ = _args[12];
lean_object* v_x_1550_ = _args[13];
lean_object* v___y_1551_ = _args[14];
lean_object* v___y_1552_ = _args[15];
lean_object* v___y_1553_ = _args[16];
lean_object* v___y_1554_ = _args[17];
lean_object* v___y_1555_ = _args[18];
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1537_, v_head_1538_, v_ctors_1539_, v_indName_1540_, v_tail_1541_, v_params_1542_, v_name_1543_, v___x_1544_, v_numParams_1545_, v_val_1546_, v___x_1547_, v___x_1548_, v_ism2_1549_, v_x_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec_ref(v_x_1550_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1557_, lean_object* v_ctors_1558_, lean_object* v_indName_1559_, lean_object* v_tail_1560_, lean_object* v_params_1561_, lean_object* v_name_1562_, lean_object* v___x_1563_, lean_object* v_numParams_1564_, lean_object* v_val_1565_, lean_object* v___x_1566_, lean_object* v___x_1567_, lean_object* v_t_1568_, lean_object* v___x_1569_, lean_object* v_ism1_1570_, lean_object* v_x_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___f_1577_; uint8_t v___x_1578_; lean_object* v___x_1579_; 
v___f_1577_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 19, 12);
lean_closure_set(v___f_1577_, 0, v_ism1_1570_);
lean_closure_set(v___f_1577_, 1, v_head_1557_);
lean_closure_set(v___f_1577_, 2, v_ctors_1558_);
lean_closure_set(v___f_1577_, 3, v_indName_1559_);
lean_closure_set(v___f_1577_, 4, v_tail_1560_);
lean_closure_set(v___f_1577_, 5, v_params_1561_);
lean_closure_set(v___f_1577_, 6, v_name_1562_);
lean_closure_set(v___f_1577_, 7, v___x_1563_);
lean_closure_set(v___f_1577_, 8, v_numParams_1564_);
lean_closure_set(v___f_1577_, 9, v_val_1565_);
lean_closure_set(v___f_1577_, 10, v___x_1566_);
lean_closure_set(v___f_1577_, 11, v___x_1567_);
v___x_1578_ = 0;
v___x_1579_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1568_, v___x_1569_, v___f_1577_, v___x_1578_, v___x_1578_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1580_ = _args[0];
lean_object* v_ctors_1581_ = _args[1];
lean_object* v_indName_1582_ = _args[2];
lean_object* v_tail_1583_ = _args[3];
lean_object* v_params_1584_ = _args[4];
lean_object* v_name_1585_ = _args[5];
lean_object* v___x_1586_ = _args[6];
lean_object* v_numParams_1587_ = _args[7];
lean_object* v_val_1588_ = _args[8];
lean_object* v___x_1589_ = _args[9];
lean_object* v___x_1590_ = _args[10];
lean_object* v_t_1591_ = _args[11];
lean_object* v___x_1592_ = _args[12];
lean_object* v_ism1_1593_ = _args[13];
lean_object* v_x_1594_ = _args[14];
lean_object* v___y_1595_ = _args[15];
lean_object* v___y_1596_ = _args[16];
lean_object* v___y_1597_ = _args[17];
lean_object* v___y_1598_ = _args[18];
lean_object* v___y_1599_ = _args[19];
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1580_, v_ctors_1581_, v_indName_1582_, v_tail_1583_, v_params_1584_, v_name_1585_, v___x_1586_, v_numParams_1587_, v_val_1588_, v___x_1589_, v___x_1590_, v_t_1591_, v___x_1592_, v_ism1_1593_, v_x_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v_x_1594_);
return v_res_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1601_, lean_object* v___x_1602_, lean_object* v_head_1603_, lean_object* v_ctors_1604_, lean_object* v_indName_1605_, lean_object* v_tail_1606_, lean_object* v_params_1607_, lean_object* v_name_1608_, lean_object* v___x_1609_, lean_object* v_numParams_1610_, lean_object* v_val_1611_, lean_object* v___x_1612_, lean_object* v_x_1613_, lean_object* v_t_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___f_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; 
v___x_1620_ = lean_nat_add(v_numIndices_1601_, v___x_1602_);
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_inc_ref(v___x_1621_);
lean_inc_ref(v_t_1614_);
v___f_1622_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 20, 13);
lean_closure_set(v___f_1622_, 0, v_head_1603_);
lean_closure_set(v___f_1622_, 1, v_ctors_1604_);
lean_closure_set(v___f_1622_, 2, v_indName_1605_);
lean_closure_set(v___f_1622_, 3, v_tail_1606_);
lean_closure_set(v___f_1622_, 4, v_params_1607_);
lean_closure_set(v___f_1622_, 5, v_name_1608_);
lean_closure_set(v___f_1622_, 6, v___x_1609_);
lean_closure_set(v___f_1622_, 7, v_numParams_1610_);
lean_closure_set(v___f_1622_, 8, v_val_1611_);
lean_closure_set(v___f_1622_, 9, v___x_1612_);
lean_closure_set(v___f_1622_, 10, v___x_1602_);
lean_closure_set(v___f_1622_, 11, v_t_1614_);
lean_closure_set(v___f_1622_, 12, v___x_1621_);
v___x_1623_ = 0;
v___x_1624_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1614_, v___x_1621_, v___f_1622_, v___x_1623_, v___x_1623_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1625_ = _args[0];
lean_object* v___x_1626_ = _args[1];
lean_object* v_head_1627_ = _args[2];
lean_object* v_ctors_1628_ = _args[3];
lean_object* v_indName_1629_ = _args[4];
lean_object* v_tail_1630_ = _args[5];
lean_object* v_params_1631_ = _args[6];
lean_object* v_name_1632_ = _args[7];
lean_object* v___x_1633_ = _args[8];
lean_object* v_numParams_1634_ = _args[9];
lean_object* v_val_1635_ = _args[10];
lean_object* v___x_1636_ = _args[11];
lean_object* v_x_1637_ = _args[12];
lean_object* v_t_1638_ = _args[13];
lean_object* v___y_1639_ = _args[14];
lean_object* v___y_1640_ = _args[15];
lean_object* v___y_1641_ = _args[16];
lean_object* v___y_1642_ = _args[17];
lean_object* v___y_1643_ = _args[18];
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1625_, v___x_1626_, v_head_1627_, v_ctors_1628_, v_indName_1629_, v_tail_1630_, v_params_1631_, v_name_1632_, v___x_1633_, v_numParams_1634_, v_val_1635_, v___x_1636_, v_x_1637_, v_t_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v_x_1637_);
lean_dec(v_numIndices_1625_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1647_, lean_object* v_head_1648_, lean_object* v_ctors_1649_, lean_object* v_indName_1650_, lean_object* v_tail_1651_, lean_object* v_name_1652_, lean_object* v___x_1653_, lean_object* v_numParams_1654_, lean_object* v_val_1655_, lean_object* v___x_1656_, lean_object* v_params_1657_, lean_object* v_t_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; lean_object* v___f_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; 
v___x_1664_ = lean_unsigned_to_nat(1u);
v___f_1665_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 19, 12);
lean_closure_set(v___f_1665_, 0, v_numIndices_1647_);
lean_closure_set(v___f_1665_, 1, v___x_1664_);
lean_closure_set(v___f_1665_, 2, v_head_1648_);
lean_closure_set(v___f_1665_, 3, v_ctors_1649_);
lean_closure_set(v___f_1665_, 4, v_indName_1650_);
lean_closure_set(v___f_1665_, 5, v_tail_1651_);
lean_closure_set(v___f_1665_, 6, v_params_1657_);
lean_closure_set(v___f_1665_, 7, v_name_1652_);
lean_closure_set(v___f_1665_, 8, v___x_1653_);
lean_closure_set(v___f_1665_, 9, v_numParams_1654_);
lean_closure_set(v___f_1665_, 10, v_val_1655_);
lean_closure_set(v___f_1665_, 11, v___x_1656_);
v___x_1666_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1667_ = 0;
v___x_1668_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1658_, v___x_1666_, v___f_1665_, v___x_1667_, v___x_1667_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1669_ = _args[0];
lean_object* v_head_1670_ = _args[1];
lean_object* v_ctors_1671_ = _args[2];
lean_object* v_indName_1672_ = _args[3];
lean_object* v_tail_1673_ = _args[4];
lean_object* v_name_1674_ = _args[5];
lean_object* v___x_1675_ = _args[6];
lean_object* v_numParams_1676_ = _args[7];
lean_object* v_val_1677_ = _args[8];
lean_object* v___x_1678_ = _args[9];
lean_object* v_params_1679_ = _args[10];
lean_object* v_t_1680_ = _args[11];
lean_object* v___y_1681_ = _args[12];
lean_object* v___y_1682_ = _args[13];
lean_object* v___y_1683_ = _args[14];
lean_object* v___y_1684_ = _args[15];
lean_object* v___y_1685_ = _args[16];
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1669_, v_head_1670_, v_ctors_1671_, v_indName_1672_, v_tail_1673_, v_name_1674_, v___x_1675_, v_numParams_1676_, v_val_1677_, v___x_1678_, v_params_1679_, v_t_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1687_, lean_object* v_declName_1688_, lean_object* v_levelParams_1689_, uint8_t v___x_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; 
lean_inc(v___y_1694_);
lean_inc_ref(v___y_1693_);
lean_inc_ref(v_a_1687_);
v___x_1696_ = lean_infer_type(v_a_1687_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v_a_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1708_; 
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref_known(v___x_1696_, 1);
v___x_1698_ = lean_box(1);
v___x_1699_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1688_, v_levelParams_1689_, v_a_1697_, v_a_1687_, v___x_1698_, v___y_1694_);
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1708_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1702_ = v___x_1699_;
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_a_1700_);
lean_dec(v___x_1699_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1705_; 
if (v_isShared_1703_ == 0)
{
lean_ctor_set_tag(v___x_1702_, 1);
v___x_1705_ = v___x_1702_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_a_1700_);
v___x_1705_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_addDecl(v___x_1705_, v___x_1690_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
return v___x_1706_;
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v_levelParams_1689_);
lean_dec(v_declName_1688_);
lean_dec_ref(v_a_1687_);
v_a_1709_ = lean_ctor_get(v___x_1696_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1696_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1696_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1717_, lean_object* v_declName_1718_, lean_object* v_levelParams_1719_, lean_object* v___x_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v___x_22497__boxed_1726_; lean_object* v_res_1727_; 
v___x_22497__boxed_1726_ = lean_unbox(v___x_1720_);
v_res_1727_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1717_, v_declName_1718_, v_levelParams_1719_, v___x_22497__boxed_1726_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
return v_res_1727_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1728_, lean_object* v_a_1729_){
_start:
{
if (lean_obj_tag(v_a_1728_) == 0)
{
lean_object* v___x_1730_; 
v___x_1730_ = l_List_reverse___redArg(v_a_1729_);
return v___x_1730_;
}
else
{
lean_object* v_head_1731_; lean_object* v_tail_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1741_; 
v_head_1731_ = lean_ctor_get(v_a_1728_, 0);
v_tail_1732_ = lean_ctor_get(v_a_1728_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_a_1728_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1734_ = v_a_1728_;
v_isShared_1735_ = v_isSharedCheck_1741_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_tail_1732_);
lean_inc(v_head_1731_);
lean_dec(v_a_1728_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1741_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = l_Lean_mkLevelParam(v_head_1731_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 1, v_a_1729_);
lean_ctor_set(v___x_1734_, 0, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_a_1729_);
v___x_1738_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
v_a_1728_ = v_tail_1732_;
v_a_1729_ = v___x_1738_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object* v_msgData_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; lean_object* v_env_1749_; uint8_t v___x_1750_; lean_object* v_env_1751_; lean_object* v___x_1752_; lean_object* v_toCold_1753_; lean_object* v_mctx_1754_; lean_object* v_lctx_1755_; lean_object* v_options_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1748_ = lean_st_ref_get(v___y_1746_);
v_env_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc_ref(v_env_1749_);
lean_dec(v___x_1748_);
v___x_1750_ = 0;
v_env_1751_ = l_Lean_Environment_setRecordingDeps(v_env_1749_, v___x_1750_);
v___x_1752_ = lean_st_ref_get(v___y_1744_);
v_toCold_1753_ = lean_ctor_get(v___y_1745_, 0);
v_mctx_1754_ = lean_ctor_get(v___x_1752_, 0);
lean_inc_ref(v_mctx_1754_);
lean_dec(v___x_1752_);
v_lctx_1755_ = lean_ctor_get(v___y_1743_, 2);
v_options_1756_ = lean_ctor_get(v_toCold_1753_, 2);
lean_inc_ref(v_options_1756_);
lean_inc_ref(v_lctx_1755_);
v___x_1757_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1757_, 0, v_env_1751_);
lean_ctor_set(v___x_1757_, 1, v_mctx_1754_);
lean_ctor_set(v___x_1757_, 2, v_lctx_1755_);
lean_ctor_set(v___x_1757_, 3, v_options_1756_);
v___x_1758_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v_msgData_1742_);
v___x_1759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_ref_1773_; lean_object* v___x_1774_; lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1783_; 
v_ref_1773_ = lean_ctor_get(v___y_1770_, 2);
v___x_1774_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1777_ = v___x_1774_;
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1774_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1783_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
lean_inc(v_ref_1773_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v_ref_1773_);
lean_ctor_set(v___x_1779_, 1, v_a_1775_);
if (v_isShared_1778_ == 0)
{
lean_ctor_set_tag(v___x_1777_, 1);
lean_ctor_set(v___x_1777_, 0, v___x_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1791_, lean_object* v_msg_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
lean_object* v_toCold_1798_; lean_object* v_currRecDepth_1799_; lean_object* v_ref_1800_; uint16_t v_optionFlags_1801_; uint8_t v_suppressElabErrors_1802_; uint8_t v_isRecordingDeps_1803_; lean_object* v_ref_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_toCold_1798_ = lean_ctor_get(v___y_1795_, 0);
v_currRecDepth_1799_ = lean_ctor_get(v___y_1795_, 1);
v_ref_1800_ = lean_ctor_get(v___y_1795_, 2);
v_optionFlags_1801_ = lean_ctor_get_uint16(v___y_1795_, sizeof(void*)*3);
v_suppressElabErrors_1802_ = lean_ctor_get_uint8(v___y_1795_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1803_ = lean_ctor_get_uint8(v___y_1795_, sizeof(void*)*3 + 3);
v_ref_1804_ = l_Lean_replaceRef(v_ref_1791_, v_ref_1800_);
lean_inc(v_currRecDepth_1799_);
lean_inc_ref(v_toCold_1798_);
v___x_1805_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1805_, 0, v_toCold_1798_);
lean_ctor_set(v___x_1805_, 1, v_currRecDepth_1799_);
lean_ctor_set(v___x_1805_, 2, v_ref_1804_);
lean_ctor_set_uint16(v___x_1805_, sizeof(void*)*3, v_optionFlags_1801_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*3 + 2, v_suppressElabErrors_1802_);
lean_ctor_set_uint8(v___x_1805_, sizeof(void*)*3 + 3, v_isRecordingDeps_1803_);
v___x_1806_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1792_, v___y_1793_, v___y_1794_, v___x_1805_, v___y_1796_);
lean_dec_ref_known(v___x_1805_, 3);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1807_, lean_object* v_msg_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1807_, v_msg_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v_ref_1807_);
return v_res_1814_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1817_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1818_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1819_ = lean_unsigned_to_nat(0u);
v___x_1820_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
lean_ctor_set(v___x_1820_, 2, v___x_1819_);
lean_ctor_set(v___x_1820_, 3, v___x_1819_);
lean_ctor_set(v___x_1820_, 4, v___x_1818_);
lean_ctor_set(v___x_1820_, 5, v___x_1818_);
lean_ctor_set(v___x_1820_, 6, v___x_1818_);
lean_ctor_set(v___x_1820_, 7, v___x_1818_);
lean_ctor_set(v___x_1820_, 8, v___x_1818_);
lean_ctor_set(v___x_1820_, 9, v___x_1818_);
lean_ctor_set(v___x_1820_, 10, v___x_1818_);
lean_ctor_set(v___x_1820_, 11, v___x_1817_);
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_unsigned_to_nat(32u);
v___x_1822_ = lean_mk_empty_array_with_capacity(v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
return v___x_1823_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
size_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1824_ = ((size_t)5ULL);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_unsigned_to_nat(32u);
v___x_1827_ = lean_mk_empty_array_with_capacity(v___x_1826_);
v___x_1828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1829_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
lean_ctor_set(v___x_1829_, 1, v___x_1827_);
lean_ctor_set(v___x_1829_, 2, v___x_1825_);
lean_ctor_set(v___x_1829_, 3, v___x_1825_);
lean_ctor_set_usize(v___x_1829_, 4, v___x_1824_);
return v___x_1829_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1830_ = lean_box(1);
v___x_1831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1833_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v___x_1831_);
lean_ctor_set(v___x_1833_, 2, v___x_1830_);
return v___x_1833_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5));
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7));
v___x_1839_ = l_Lean_stringToMessageData(v___x_1838_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9));
v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13));
v___x_1848_ = l_Lean_stringToMessageData(v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15));
v___x_1851_ = l_Lean_stringToMessageData(v___x_1850_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17));
v___x_1854_ = l_Lean_stringToMessageData(v___x_1853_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__20(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19));
v___x_1857_ = l_Lean_stringToMessageData(v___x_1856_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__22(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__21));
v___x_1860_ = l_Lean_stringToMessageData(v___x_1859_);
return v___x_1860_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__24(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__23));
v___x_1863_ = l_Lean_stringToMessageData(v___x_1862_);
return v___x_1863_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__26(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__25));
v___x_1866_ = l_Lean_stringToMessageData(v___x_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1867_, lean_object* v_declHint_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v_env_1873_; uint8_t v___x_1874_; 
v___x_1871_ = lean_box(0);
v___x_1872_ = lean_st_ref_get(v___y_1869_);
v_env_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc_ref(v_env_1873_);
lean_dec(v___x_1872_);
v___x_1874_ = l_Lean_Name_isAnonymous(v_declHint_1868_);
if (v___x_1874_ == 0)
{
uint8_t v_isExporting_1875_; 
v_isExporting_1875_ = lean_ctor_get_uint8(v_env_1873_, sizeof(void*)*13);
if (v_isExporting_1875_ == 0)
{
lean_object* v___x_1876_; 
lean_dec_ref(v_env_1873_);
lean_dec(v_declHint_1868_);
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_msg_1867_);
return v___x_1876_;
}
else
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
lean_inc_ref(v_env_1873_);
v___x_1877_ = l_Lean_Environment_setExporting(v_env_1873_, v___x_1874_);
lean_inc(v_declHint_1868_);
lean_inc_ref(v___x_1877_);
v___x_1878_ = l_Lean_Environment_contains(v___x_1877_, v_declHint_1868_, v_isExporting_1875_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
lean_dec_ref(v___x_1877_);
lean_dec_ref(v_env_1873_);
lean_dec(v_declHint_1868_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_msg_1867_);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v_c_1885_; lean_object* v___x_1886_; 
v___x_1880_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1881_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1882_ = l_Lean_Options_empty;
v___x_1883_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1877_);
lean_ctor_set(v___x_1883_, 1, v___x_1880_);
lean_ctor_set(v___x_1883_, 2, v___x_1881_);
lean_ctor_set(v___x_1883_, 3, v___x_1882_);
lean_inc(v_declHint_1868_);
v___x_1884_ = l_Lean_MessageData_ofConstName(v_declHint_1868_, v___x_1874_);
v_c_1885_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1885_, 0, v___x_1883_);
lean_ctor_set(v_c_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1873_, v_declHint_1868_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_dec_ref(v_env_1873_);
lean_dec(v_declHint_1868_);
v___x_1887_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_c_1885_);
v___x_1889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_MessageData_note(v___x_1890_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v_msg_1867_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
return v___x_1893_;
}
else
{
lean_object* v_val_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1950_; 
v_val_1894_ = lean_ctor_get(v___x_1886_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1886_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1896_ = v___x_1886_;
v_isShared_1897_ = v_isSharedCheck_1950_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_val_1894_);
lean_dec(v___x_1886_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1950_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1898_; lean_object* v_modules_1899_; lean_object* v_moduleNames_1900_; lean_object* v_mod_1901_; uint8_t v___y_1903_; uint8_t v___x_1933_; 
v___x_1898_ = l_Lean_Environment_header(v_env_1873_);
lean_dec_ref(v_env_1873_);
v_modules_1899_ = lean_ctor_get(v___x_1898_, 3);
lean_inc_ref(v_modules_1899_);
v_moduleNames_1900_ = lean_ctor_get(v___x_1898_, 4);
lean_inc_ref(v_moduleNames_1900_);
lean_dec_ref(v___x_1898_);
v_mod_1901_ = lean_array_get(v___x_1871_, v_moduleNames_1900_, v_val_1894_);
lean_dec_ref(v_moduleNames_1900_);
v___x_1933_ = l_Lean_isPrivateName(v_declHint_1868_);
lean_dec(v_declHint_1868_);
if (v___x_1933_ == 0)
{
lean_object* v___x_1934_; uint8_t v___x_1935_; 
v___x_1934_ = lean_array_get_size(v_modules_1899_);
v___x_1935_ = lean_nat_dec_lt(v_val_1894_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_dec_ref(v_modules_1899_);
lean_dec(v_val_1894_);
v___y_1903_ = v___x_1933_;
goto v___jp_1902_;
}
else
{
lean_object* v___x_1936_; lean_object* v_toImport_1937_; uint8_t v_isExported_1938_; 
v___x_1936_ = lean_array_fget(v_modules_1899_, v_val_1894_);
lean_dec(v_val_1894_);
lean_dec_ref(v_modules_1899_);
v_toImport_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc_ref(v_toImport_1937_);
lean_dec(v___x_1936_);
v_isExported_1938_ = lean_ctor_get_uint8(v_toImport_1937_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1937_);
v___y_1903_ = v_isExported_1938_;
goto v___jp_1902_;
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec_ref(v_modules_1899_);
lean_del_object(v___x_1896_);
lean_dec(v_val_1894_);
v___x_1939_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v_c_1885_);
v___x_1941_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__24);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = l_Lean_MessageData_ofName(v_mod_1901_);
v___x_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
v___x_1945_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__26);
v___x_1946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1944_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = l_Lean_MessageData_note(v___x_1946_);
v___x_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1948_, 0, v_msg_1867_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
return v___x_1949_;
}
v___jp_1902_:
{
if (v___y_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1904_);
lean_ctor_set(v___x_1905_, 1, v_c_1885_);
v___x_1906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Lean_MessageData_ofName(v_mod_1901_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = l_Lean_MessageData_note(v___x_1911_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v_msg_1867_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1913_);
v___x_1915_ = v___x_1896_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1917_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
lean_ctor_set(v___x_1918_, 1, v_c_1885_);
v___x_1919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_MessageData_ofName(v_mod_1901_);
lean_inc_ref(v___x_1921_);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__20);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v___x_1921_);
v___x_1926_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__22);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = l_Lean_MessageData_note(v___x_1927_);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v_msg_1867_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set_tag(v___x_1896_, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1929_);
v___x_1931_ = v___x_1896_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1951_; 
lean_dec_ref(v_env_1873_);
lean_dec(v_declHint_1868_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_msg_1867_);
return v___x_1951_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1952_, lean_object* v_declHint_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1952_, v_declHint_1953_, v___y_1954_);
lean_dec(v___y_1954_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1957_, lean_object* v_declHint_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1974_; 
v___x_1964_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1957_, v_declHint_1958_, v___y_1962_);
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_1974_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1974_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v___x_1969_ = l_Lean_unknownIdentifierMessageTag;
v___x_1970_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v_a_1965_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1970_);
v___x_1972_ = v___x_1967_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1975_, lean_object* v_declHint_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1975_, v_declHint_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1983_, lean_object* v_msg_1984_, lean_object* v_declHint_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1991_; lean_object* v_a_1992_; lean_object* v___x_1993_; 
v___x_1991_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1984_, v_declHint_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1991_);
v___x_1993_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1983_, v_a_1992_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1994_, lean_object* v_msg_1995_, lean_object* v_declHint_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1994_, v_msg_1995_, v_declHint_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v_ref_1994_);
return v_res_2002_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2004_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_2005_ = l_Lean_stringToMessageData(v___x_2004_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_2008_ = l_Lean_stringToMessageData(v___x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_2009_, lean_object* v_constName_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___x_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2016_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_2017_ = 0;
lean_inc(v_constName_2010_);
v___x_2018_ = l_Lean_MessageData_ofConstName(v_constName_2010_, v___x_2017_);
v___x_2019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2016_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
v___x_2020_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2019_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2009_, v___x_2021_, v_constName_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_2023_, lean_object* v_constName_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2023_, v_constName_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v_ref_2023_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_ref_2037_; lean_object* v___x_2038_; 
v_ref_2037_ = lean_ctor_get(v___y_2034_, 2);
v___x_2038_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2037_, v_constName_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; lean_object* v_env_2053_; uint8_t v___x_2054_; lean_object* v___x_2055_; 
v___x_2052_ = lean_st_ref_get(v___y_2050_);
v_env_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc_ref(v_env_2053_);
lean_dec(v___x_2052_);
v___x_2054_ = 0;
lean_inc(v_constName_2046_);
v___x_2055_ = l_Lean_Environment_findConstVal_x3f(v_env_2053_, v_constName_2046_, v___x_2054_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
return v___x_2056_;
}
else
{
lean_object* v_val_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_constName_2046_);
v_val_2057_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2055_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_val_2057_);
lean_dec(v___x_2055_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 0);
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_val_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2072_, uint8_t v_s_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; lean_object* v_env_2078_; lean_object* v_nextMacroScope_2079_; lean_object* v_ngen_2080_; lean_object* v_auxDeclNGen_2081_; lean_object* v_traceState_2082_; lean_object* v_recordedDeps_2083_; lean_object* v_messages_2084_; lean_object* v_infoState_2085_; lean_object* v_snapshotTasks_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2115_; 
v___x_2077_ = lean_st_ref_take(v___y_2075_);
v_env_2078_ = lean_ctor_get(v___x_2077_, 0);
v_nextMacroScope_2079_ = lean_ctor_get(v___x_2077_, 1);
v_ngen_2080_ = lean_ctor_get(v___x_2077_, 2);
v_auxDeclNGen_2081_ = lean_ctor_get(v___x_2077_, 3);
v_traceState_2082_ = lean_ctor_get(v___x_2077_, 4);
v_recordedDeps_2083_ = lean_ctor_get(v___x_2077_, 6);
v_messages_2084_ = lean_ctor_get(v___x_2077_, 7);
v_infoState_2085_ = lean_ctor_get(v___x_2077_, 8);
v_snapshotTasks_2086_ = lean_ctor_get(v___x_2077_, 9);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v___x_2077_, 5);
lean_dec(v_unused_2116_);
v___x_2088_ = v___x_2077_;
v_isShared_2089_ = v_isSharedCheck_2115_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_snapshotTasks_2086_);
lean_inc(v_infoState_2085_);
lean_inc(v_messages_2084_);
lean_inc(v_recordedDeps_2083_);
lean_inc(v_traceState_2082_);
lean_inc(v_auxDeclNGen_2081_);
lean_inc(v_ngen_2080_);
lean_inc(v_nextMacroScope_2079_);
lean_inc(v_env_2078_);
lean_dec(v___x_2077_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2115_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2090_ = 0;
v___x_2091_ = lean_box(0);
v___x_2092_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2078_, v_declName_2072_, v_s_2073_, v___x_2090_, v___x_2091_);
v___x_2093_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 5, v___x_2093_);
lean_ctor_set(v___x_2088_, 0, v___x_2092_);
v___x_2095_ = v___x_2088_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_nextMacroScope_2079_);
lean_ctor_set(v_reuseFailAlloc_2114_, 2, v_ngen_2080_);
lean_ctor_set(v_reuseFailAlloc_2114_, 3, v_auxDeclNGen_2081_);
lean_ctor_set(v_reuseFailAlloc_2114_, 4, v_traceState_2082_);
lean_ctor_set(v_reuseFailAlloc_2114_, 5, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2114_, 6, v_recordedDeps_2083_);
lean_ctor_set(v_reuseFailAlloc_2114_, 7, v_messages_2084_);
lean_ctor_set(v_reuseFailAlloc_2114_, 8, v_infoState_2085_);
lean_ctor_set(v_reuseFailAlloc_2114_, 9, v_snapshotTasks_2086_);
v___x_2095_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_mctx_2098_; lean_object* v_zetaDeltaFVarIds_2099_; lean_object* v_postponed_2100_; lean_object* v_diag_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2112_; 
v___x_2096_ = lean_st_ref_put(v___y_2075_, v___x_2095_);
v___x_2097_ = lean_st_ref_take(v___y_2074_);
v_mctx_2098_ = lean_ctor_get(v___x_2097_, 0);
v_zetaDeltaFVarIds_2099_ = lean_ctor_get(v___x_2097_, 2);
v_postponed_2100_ = lean_ctor_get(v___x_2097_, 3);
v_diag_2101_ = lean_ctor_get(v___x_2097_, 4);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2112_ == 0)
{
lean_object* v_unused_2113_; 
v_unused_2113_ = lean_ctor_get(v___x_2097_, 1);
lean_dec(v_unused_2113_);
v___x_2103_ = v___x_2097_;
v_isShared_2104_ = v_isSharedCheck_2112_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_diag_2101_);
lean_inc(v_postponed_2100_);
lean_inc(v_zetaDeltaFVarIds_2099_);
lean_inc(v_mctx_2098_);
lean_dec(v___x_2097_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2112_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2108_; 
v___x_2105_ = lean_box(0);
v___x_2106_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 1, v___x_2106_);
v___x_2108_ = v___x_2103_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_mctx_2098_);
lean_ctor_set(v_reuseFailAlloc_2111_, 1, v___x_2106_);
lean_ctor_set(v_reuseFailAlloc_2111_, 2, v_zetaDeltaFVarIds_2099_);
lean_ctor_set(v_reuseFailAlloc_2111_, 3, v_postponed_2100_);
lean_ctor_set(v_reuseFailAlloc_2111_, 4, v_diag_2101_);
v___x_2108_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = lean_st_ref_put(v___y_2074_, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2105_);
return v___x_2110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2117_, lean_object* v_s_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
uint8_t v_s_boxed_2122_; lean_object* v_res_2123_; 
v_s_boxed_2122_ = lean_unbox(v_s_2118_);
v_res_2123_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2117_, v_s_boxed_2122_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
uint8_t v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = 0;
v___x_2131_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2124_, v___x_2130_, v___y_2126_, v___y_2128_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2138_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2141_ = l_Lean_stringToMessageData(v___x_2140_);
return v___x_2141_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
return v___x_2144_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2148_, lean_object* v_declName_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2155_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2156_ = l_Lean_MessageData_ofName(v_attrName_2148_);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2155_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = 0;
v___x_2161_ = l_Lean_MessageData_ofConstName(v_declName_2149_, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2159_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2164_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2166_, lean_object* v_declName_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2166_, v_declName_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0(lean_object* v_addEntryFn_2174_, lean_object* v_decl_2175_, lean_object* v_s_2176_){
_start:
{
lean_object* v_importedEntries_2177_; lean_object* v_state_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2186_; 
v_importedEntries_2177_ = lean_ctor_get(v_s_2176_, 0);
v_state_2178_ = lean_ctor_get(v_s_2176_, 1);
v_isSharedCheck_2186_ = !lean_is_exclusive(v_s_2176_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2180_ = v_s_2176_;
v_isShared_2181_ = v_isSharedCheck_2186_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_state_2178_);
lean_inc(v_importedEntries_2177_);
lean_dec(v_s_2176_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2186_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v_state_2182_; lean_object* v___x_2184_; 
v_state_2182_ = lean_apply_2(v_addEntryFn_2174_, v_state_2178_, v_decl_2175_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 1, v_state_2182_);
v___x_2184_ = v___x_2180_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_importedEntries_2177_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_state_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2189_ = l_Lean_stringToMessageData(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2191_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2193_, lean_object* v_declName_2194_, lean_object* v_asyncPrefix_x3f_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___y_2202_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2195_) == 0)
{
lean_object* v___x_2215_; 
v___x_2215_ = l_Lean_MessageData_nil;
v___y_2202_ = v___x_2215_;
goto v___jp_2201_;
}
else
{
lean_object* v_val_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v_val_2216_ = lean_ctor_get(v_asyncPrefix_x3f_2195_, 0);
lean_inc(v_val_2216_);
lean_dec_ref_known(v_asyncPrefix_x3f_2195_, 1);
v___x_2217_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2218_ = l_Lean_MessageData_ofName(v_val_2216_);
v___x_2219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2217_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2219_);
lean_ctor_set(v___x_2221_, 1, v___x_2220_);
v___y_2202_ = v___x_2221_;
goto v___jp_2201_;
}
v___jp_2201_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2203_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2204_ = l_Lean_MessageData_ofName(v_attrName_2193_);
v___x_2205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = 0;
v___x_2209_ = l_Lean_MessageData_ofConstName(v_declName_2194_, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2207_);
lean_ctor_set(v___x_2210_, 1, v___x_2209_);
v___x_2211_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2210_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v___y_2202_);
v___x_2214_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2213_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2222_, lean_object* v_declName_2223_, lean_object* v_asyncPrefix_x3f_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2222_, v_declName_2223_, v_asyncPrefix_x3f_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2231_, lean_object* v_decl_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___x_2293_; lean_object* v_env_2294_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___x_2309_; 
v___x_2293_ = lean_st_ref_get(v___y_2236_);
v_env_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc_ref(v_env_2294_);
lean_dec(v___x_2293_);
v___x_2309_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2294_, v_decl_2232_);
if (lean_obj_tag(v___x_2309_) == 0)
{
v___y_2296_ = v___y_2233_;
v___y_2297_ = v___y_2234_;
v___y_2298_ = v___y_2235_;
v___y_2299_ = v___y_2236_;
goto v___jp_2295_;
}
else
{
lean_object* v_attr_2310_; lean_object* v_toAttributeImplCore_2311_; lean_object* v_name_2312_; lean_object* v___x_2313_; 
lean_dec_ref_known(v___x_2309_, 1);
lean_dec_ref(v_env_2294_);
v_attr_2310_ = lean_ctor_get(v_attr_2231_, 0);
lean_inc_ref(v_attr_2310_);
lean_dec_ref(v_attr_2231_);
v_toAttributeImplCore_2311_ = lean_ctor_get(v_attr_2310_, 0);
lean_inc_ref(v_toAttributeImplCore_2311_);
lean_dec_ref(v_attr_2310_);
v_name_2312_ = lean_ctor_get(v_toAttributeImplCore_2311_, 1);
lean_inc(v_name_2312_);
lean_dec_ref(v_toAttributeImplCore_2311_);
v___x_2313_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2312_, v_decl_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
return v___x_2313_;
}
v___jp_2238_:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v_mctx_2254_; lean_object* v_zetaDeltaFVarIds_2255_; lean_object* v_postponed_2256_; lean_object* v_diag_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2268_; 
v___x_2250_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
v___x_2251_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2251_, 0, v___y_2249_);
lean_ctor_set(v___x_2251_, 1, v___y_2248_);
lean_ctor_set(v___x_2251_, 2, v___y_2247_);
lean_ctor_set(v___x_2251_, 3, v___y_2239_);
lean_ctor_set(v___x_2251_, 4, v___y_2244_);
lean_ctor_set(v___x_2251_, 5, v___x_2250_);
lean_ctor_set(v___x_2251_, 6, v___y_2241_);
lean_ctor_set(v___x_2251_, 7, v___y_2246_);
lean_ctor_set(v___x_2251_, 8, v___y_2242_);
lean_ctor_set(v___x_2251_, 9, v___y_2240_);
v___x_2252_ = lean_st_ref_put(v___y_2243_, v___x_2251_);
v___x_2253_ = lean_st_ref_take(v___y_2245_);
v_mctx_2254_ = lean_ctor_get(v___x_2253_, 0);
v_zetaDeltaFVarIds_2255_ = lean_ctor_get(v___x_2253_, 2);
v_postponed_2256_ = lean_ctor_get(v___x_2253_, 3);
v_diag_2257_ = lean_ctor_get(v___x_2253_, 4);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2268_ == 0)
{
lean_object* v_unused_2269_; 
v_unused_2269_ = lean_ctor_get(v___x_2253_, 1);
lean_dec(v_unused_2269_);
v___x_2259_ = v___x_2253_;
v_isShared_2260_ = v_isSharedCheck_2268_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_diag_2257_);
lean_inc(v_postponed_2256_);
lean_inc(v_zetaDeltaFVarIds_2255_);
lean_inc(v_mctx_2254_);
lean_dec(v___x_2253_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2268_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v___x_2262_);
v___x_2264_ = v___x_2259_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_mctx_2254_);
lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2267_, 2, v_zetaDeltaFVarIds_2255_);
lean_ctor_set(v_reuseFailAlloc_2267_, 3, v_postponed_2256_);
lean_ctor_set(v_reuseFailAlloc_2267_, 4, v_diag_2257_);
v___x_2264_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = lean_st_ref_put(v___y_2245_, v___x_2264_);
v___x_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2261_);
return v___x_2266_;
}
}
}
v___jp_2270_:
{
lean_object* v___x_2273_; lean_object* v_ext_2274_; lean_object* v_toEnvExtension_2275_; lean_object* v_env_2276_; lean_object* v_nextMacroScope_2277_; lean_object* v_ngen_2278_; lean_object* v_auxDeclNGen_2279_; lean_object* v_traceState_2280_; lean_object* v_recordedDeps_2281_; lean_object* v_messages_2282_; lean_object* v_infoState_2283_; lean_object* v_snapshotTasks_2284_; lean_object* v_addEntryFn_2285_; lean_object* v_asyncMode_2286_; uint8_t v_logWrites_2287_; lean_object* v___f_2288_; uint8_t v___x_2289_; 
v___x_2273_ = lean_st_ref_take(v___y_2272_);
v_ext_2274_ = lean_ctor_get(v_attr_2231_, 1);
lean_inc_ref(v_ext_2274_);
lean_dec_ref(v_attr_2231_);
v_toEnvExtension_2275_ = lean_ctor_get(v_ext_2274_, 0);
lean_inc_ref(v_toEnvExtension_2275_);
v_env_2276_ = lean_ctor_get(v___x_2273_, 0);
lean_inc_ref(v_env_2276_);
v_nextMacroScope_2277_ = lean_ctor_get(v___x_2273_, 1);
lean_inc(v_nextMacroScope_2277_);
v_ngen_2278_ = lean_ctor_get(v___x_2273_, 2);
lean_inc_ref(v_ngen_2278_);
v_auxDeclNGen_2279_ = lean_ctor_get(v___x_2273_, 3);
lean_inc_ref(v_auxDeclNGen_2279_);
v_traceState_2280_ = lean_ctor_get(v___x_2273_, 4);
lean_inc_ref(v_traceState_2280_);
v_recordedDeps_2281_ = lean_ctor_get(v___x_2273_, 6);
lean_inc_ref(v_recordedDeps_2281_);
v_messages_2282_ = lean_ctor_get(v___x_2273_, 7);
lean_inc_ref(v_messages_2282_);
v_infoState_2283_ = lean_ctor_get(v___x_2273_, 8);
lean_inc_ref(v_infoState_2283_);
v_snapshotTasks_2284_ = lean_ctor_get(v___x_2273_, 9);
lean_inc_ref(v_snapshotTasks_2284_);
lean_dec(v___x_2273_);
v_addEntryFn_2285_ = lean_ctor_get(v_ext_2274_, 3);
lean_inc(v_addEntryFn_2285_);
lean_dec_ref(v_ext_2274_);
v_asyncMode_2286_ = lean_ctor_get(v_toEnvExtension_2275_, 2);
lean_inc(v_asyncMode_2286_);
v_logWrites_2287_ = lean_ctor_get_uint8(v_toEnvExtension_2275_, sizeof(void*)*6);
lean_inc(v_decl_2232_);
v___f_2288_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0), 3, 2);
lean_closure_set(v___f_2288_, 0, v_addEntryFn_2285_);
lean_closure_set(v___f_2288_, 1, v_decl_2232_);
v___x_2289_ = 1;
if (v_logWrites_2287_ == 0)
{
lean_object* v___x_2290_; 
v___x_2290_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2275_, v_env_2276_, v___f_2288_, v_asyncMode_2286_, v_decl_2232_, v___x_2289_);
lean_dec(v_asyncMode_2286_);
v___y_2239_ = v_auxDeclNGen_2279_;
v___y_2240_ = v_snapshotTasks_2284_;
v___y_2241_ = v_recordedDeps_2281_;
v___y_2242_ = v_infoState_2283_;
v___y_2243_ = v___y_2272_;
v___y_2244_ = v_traceState_2280_;
v___y_2245_ = v___y_2271_;
v___y_2246_ = v_messages_2282_;
v___y_2247_ = v_ngen_2278_;
v___y_2248_ = v_nextMacroScope_2277_;
v___y_2249_ = v___x_2290_;
goto v___jp_2238_;
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_inc_ref(v_toEnvExtension_2275_);
v___x_2291_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2275_, v_env_2276_);
lean_dec_ref(v_env_2276_);
v___x_2292_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2275_, v___x_2291_, v___f_2288_, v_asyncMode_2286_, v_decl_2232_, v___x_2289_);
lean_dec(v_asyncMode_2286_);
v___y_2239_ = v_auxDeclNGen_2279_;
v___y_2240_ = v_snapshotTasks_2284_;
v___y_2241_ = v_recordedDeps_2281_;
v___y_2242_ = v_infoState_2283_;
v___y_2243_ = v___y_2272_;
v___y_2244_ = v_traceState_2280_;
v___y_2245_ = v___y_2271_;
v___y_2246_ = v_messages_2282_;
v___y_2247_ = v_ngen_2278_;
v___y_2248_ = v_nextMacroScope_2277_;
v___y_2249_ = v___x_2292_;
goto v___jp_2238_;
}
}
v___jp_2295_:
{
lean_object* v_ext_2300_; lean_object* v_toEnvExtension_2301_; lean_object* v_attr_2302_; lean_object* v_asyncMode_2303_; uint8_t v___x_2304_; 
v_ext_2300_ = lean_ctor_get(v_attr_2231_, 1);
v_toEnvExtension_2301_ = lean_ctor_get(v_ext_2300_, 0);
v_attr_2302_ = lean_ctor_get(v_attr_2231_, 0);
v_asyncMode_2303_ = lean_ctor_get(v_toEnvExtension_2301_, 2);
lean_inc(v_decl_2232_);
lean_inc_ref(v_env_2294_);
v___x_2304_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2294_, v_decl_2232_, v_asyncMode_2303_);
if (v___x_2304_ == 0)
{
lean_object* v_toAttributeImplCore_2305_; lean_object* v_name_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
lean_inc_ref(v_attr_2302_);
lean_dec_ref(v_attr_2231_);
v_toAttributeImplCore_2305_ = lean_ctor_get(v_attr_2302_, 0);
lean_inc_ref(v_toAttributeImplCore_2305_);
lean_dec_ref(v_attr_2302_);
v_name_2306_ = lean_ctor_get(v_toAttributeImplCore_2305_, 1);
lean_inc(v_name_2306_);
lean_dec_ref(v_toAttributeImplCore_2305_);
v___x_2307_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2294_);
v___x_2308_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2306_, v_decl_2232_, v___x_2307_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2308_;
}
else
{
lean_dec_ref(v_env_2294_);
v___y_2271_ = v___y_2297_;
v___y_2272_ = v___y_2299_;
goto v___jp_2270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2314_, lean_object* v_decl_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2314_, v_decl_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v___x_2328_; lean_object* v_env_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; 
v___x_2328_ = lean_st_ref_get(v___y_2326_);
v_env_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc_ref(v_env_2329_);
lean_dec(v___x_2328_);
v___x_2330_ = 0;
lean_inc(v_constName_2322_);
v___x_2331_ = l_Lean_Environment_find_x3f(v_env_2329_, v_constName_2322_, v___x_2330_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
return v___x_2332_;
}
else
{
lean_object* v_val_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v_constName_2322_);
v_val_2333_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2331_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_val_2333_);
lean_dec(v___x_2331_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set_tag(v___x_2335_, 0);
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_val_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2347_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2351_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2352_ = lean_unsigned_to_nat(58u);
v___x_2353_ = lean_unsigned_to_nat(33u);
v___x_2354_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2355_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2356_ = l_mkPanicMessageWithDecl(v___x_2355_, v___x_2354_, v___x_2353_, v___x_2352_, v___x_2351_);
return v___x_2356_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2358_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2359_ = lean_unsigned_to_nat(60u);
v___x_2360_ = lean_unsigned_to_nat(30u);
v___x_2361_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2362_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2363_ = l_mkPanicMessageWithDecl(v___x_2362_, v___x_2361_, v___x_2360_, v___x_2359_, v___x_2358_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2364_, lean_object* v_indName_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_){
_start:
{
lean_object* v___x_2371_; 
lean_inc(v_indName_2365_);
v___x_2371_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_a_2372_);
lean_dec_ref_known(v___x_2371_, 1);
if (lean_obj_tag(v_a_2372_) == 5)
{
lean_object* v_val_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2563_; 
v_val_2373_ = lean_ctor_get(v_a_2372_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_a_2372_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2375_ = v_a_2372_;
v_isShared_2376_ = v_isSharedCheck_2563_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_val_2373_);
lean_dec(v_a_2372_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2563_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
lean_inc(v_indName_2365_);
v___x_2377_ = l_Lean_mkCasesOnName(v_indName_2365_);
lean_inc(v___x_2377_);
v___x_2378_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2377_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_object* v_a_2379_; lean_object* v_name_2380_; lean_object* v_levelParams_2381_; lean_object* v_type_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
lean_inc(v_a_2379_);
lean_dec_ref_known(v___x_2378_, 1);
v_name_2380_ = lean_ctor_get(v_a_2379_, 0);
lean_inc(v_name_2380_);
v_levelParams_2381_ = lean_ctor_get(v_a_2379_, 1);
lean_inc_n(v_levelParams_2381_, 2);
v_type_2382_ = lean_ctor_get(v_a_2379_, 2);
lean_inc_ref(v_type_2382_);
lean_dec(v_a_2379_);
v___x_2383_ = lean_box(0);
v___x_2384_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2381_, v___x_2383_);
if (lean_obj_tag(v___x_2384_) == 1)
{
lean_object* v_head_2385_; lean_object* v_tail_2386_; lean_object* v_numParams_2387_; lean_object* v_numIndices_2388_; lean_object* v_ctors_2389_; lean_object* v___f_2390_; lean_object* v___x_2392_; 
v_head_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_head_2385_);
v_tail_2386_ = lean_ctor_get(v___x_2384_, 1);
lean_inc(v_tail_2386_);
v_numParams_2387_ = lean_ctor_get(v_val_2373_, 1);
lean_inc_n(v_numParams_2387_, 2);
v_numIndices_2388_ = lean_ctor_get(v_val_2373_, 2);
lean_inc(v_numIndices_2388_);
v_ctors_2389_ = lean_ctor_get(v_val_2373_, 4);
lean_inc(v_ctors_2389_);
v___f_2390_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2390_, 0, v_numIndices_2388_);
lean_closure_set(v___f_2390_, 1, v_head_2385_);
lean_closure_set(v___f_2390_, 2, v_ctors_2389_);
lean_closure_set(v___f_2390_, 3, v_indName_2365_);
lean_closure_set(v___f_2390_, 4, v_tail_2386_);
lean_closure_set(v___f_2390_, 5, v_name_2380_);
lean_closure_set(v___f_2390_, 6, v___x_2384_);
lean_closure_set(v___f_2390_, 7, v_numParams_2387_);
lean_closure_set(v___f_2390_, 8, v_val_2373_);
lean_closure_set(v___f_2390_, 9, v___x_2377_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set_tag(v___x_2375_, 1);
lean_ctor_set(v___x_2375_, 0, v_numParams_2387_);
v___x_2392_ = v___x_2375_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_numParams_2387_);
v___x_2392_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
uint8_t v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = 0;
v___x_2394_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2382_, v___x_2392_, v___f_2390_, v___x_2393_, v___x_2393_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2396_; lean_object* v___f_2397_; uint8_t v___y_2399_; uint8_t v___x_2542_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
v___x_2396_ = lean_box(v___x_2393_);
lean_inc(v_declName_2364_);
v___f_2397_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2397_, 0, v_a_2395_);
lean_closure_set(v___f_2397_, 1, v_declName_2364_);
lean_closure_set(v___f_2397_, 2, v_levelParams_2381_);
lean_closure_set(v___f_2397_, 3, v___x_2396_);
v___x_2542_ = l_Lean_isPrivateName(v_declName_2364_);
if (v___x_2542_ == 0)
{
uint8_t v___x_2543_; 
v___x_2543_ = 1;
v___y_2399_ = v___x_2543_;
goto v___jp_2398_;
}
else
{
v___y_2399_ = v___x_2393_;
goto v___jp_2398_;
}
v___jp_2398_:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2397_, v___y_2399_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v___x_2401_; lean_object* v_env_2402_; lean_object* v_nextMacroScope_2403_; lean_object* v_ngen_2404_; lean_object* v_auxDeclNGen_2405_; lean_object* v_traceState_2406_; lean_object* v_recordedDeps_2407_; lean_object* v_messages_2408_; lean_object* v_infoState_2409_; lean_object* v_snapshotTasks_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2540_; 
lean_dec_ref_known(v___x_2400_, 1);
v___x_2401_ = lean_st_ref_take(v_a_2369_);
v_env_2402_ = lean_ctor_get(v___x_2401_, 0);
v_nextMacroScope_2403_ = lean_ctor_get(v___x_2401_, 1);
v_ngen_2404_ = lean_ctor_get(v___x_2401_, 2);
v_auxDeclNGen_2405_ = lean_ctor_get(v___x_2401_, 3);
v_traceState_2406_ = lean_ctor_get(v___x_2401_, 4);
v_recordedDeps_2407_ = lean_ctor_get(v___x_2401_, 6);
v_messages_2408_ = lean_ctor_get(v___x_2401_, 7);
v_infoState_2409_ = lean_ctor_get(v___x_2401_, 8);
v_snapshotTasks_2410_ = lean_ctor_get(v___x_2401_, 9);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2401_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; 
v_unused_2541_ = lean_ctor_get(v___x_2401_, 5);
lean_dec(v_unused_2541_);
v___x_2412_ = v___x_2401_;
v_isShared_2413_ = v_isSharedCheck_2540_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_snapshotTasks_2410_);
lean_inc(v_infoState_2409_);
lean_inc(v_messages_2408_);
lean_inc(v_recordedDeps_2407_);
lean_inc(v_traceState_2406_);
lean_inc(v_auxDeclNGen_2405_);
lean_inc(v_ngen_2404_);
lean_inc(v_nextMacroScope_2403_);
lean_inc(v_env_2402_);
lean_dec(v___x_2401_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2540_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2417_; 
lean_inc(v_declName_2364_);
v___x_2414_ = l_Lean_Meta_markMatcherLike(v_env_2402_, v_declName_2364_);
v___x_2415_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 5, v___x_2415_);
lean_ctor_set(v___x_2412_, 0, v___x_2414_);
v___x_2417_ = v___x_2412_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_nextMacroScope_2403_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_ngen_2404_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_auxDeclNGen_2405_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v_traceState_2406_);
lean_ctor_set(v_reuseFailAlloc_2539_, 5, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2539_, 6, v_recordedDeps_2407_);
lean_ctor_set(v_reuseFailAlloc_2539_, 7, v_messages_2408_);
lean_ctor_set(v_reuseFailAlloc_2539_, 8, v_infoState_2409_);
lean_ctor_set(v_reuseFailAlloc_2539_, 9, v_snapshotTasks_2410_);
v___x_2417_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_mctx_2420_; lean_object* v_zetaDeltaFVarIds_2421_; lean_object* v_postponed_2422_; lean_object* v_diag_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2537_; 
v___x_2418_ = lean_st_ref_put(v_a_2369_, v___x_2417_);
v___x_2419_ = lean_st_ref_take(v_a_2367_);
v_mctx_2420_ = lean_ctor_get(v___x_2419_, 0);
v_zetaDeltaFVarIds_2421_ = lean_ctor_get(v___x_2419_, 2);
v_postponed_2422_ = lean_ctor_get(v___x_2419_, 3);
v_diag_2423_ = lean_ctor_get(v___x_2419_, 4);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; 
v_unused_2538_ = lean_ctor_get(v___x_2419_, 1);
lean_dec(v_unused_2538_);
v___x_2425_ = v___x_2419_;
v_isShared_2426_ = v_isSharedCheck_2537_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_diag_2423_);
lean_inc(v_postponed_2422_);
lean_inc(v_zetaDeltaFVarIds_2421_);
lean_inc(v_mctx_2420_);
lean_dec(v___x_2419_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2537_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
v___x_2427_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 1, v___x_2427_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_mctx_2420_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2536_, 2, v_zetaDeltaFVarIds_2421_);
lean_ctor_set(v_reuseFailAlloc_2536_, 3, v_postponed_2422_);
lean_ctor_set(v_reuseFailAlloc_2536_, 4, v_diag_2423_);
v___x_2429_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_env_2432_; lean_object* v_nextMacroScope_2433_; lean_object* v_ngen_2434_; lean_object* v_auxDeclNGen_2435_; lean_object* v_traceState_2436_; lean_object* v_recordedDeps_2437_; lean_object* v_messages_2438_; lean_object* v_infoState_2439_; lean_object* v_snapshotTasks_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2534_; 
v___x_2430_ = lean_st_ref_put(v_a_2367_, v___x_2429_);
v___x_2431_ = lean_st_ref_take(v_a_2369_);
v_env_2432_ = lean_ctor_get(v___x_2431_, 0);
v_nextMacroScope_2433_ = lean_ctor_get(v___x_2431_, 1);
v_ngen_2434_ = lean_ctor_get(v___x_2431_, 2);
v_auxDeclNGen_2435_ = lean_ctor_get(v___x_2431_, 3);
v_traceState_2436_ = lean_ctor_get(v___x_2431_, 4);
v_recordedDeps_2437_ = lean_ctor_get(v___x_2431_, 6);
v_messages_2438_ = lean_ctor_get(v___x_2431_, 7);
v_infoState_2439_ = lean_ctor_get(v___x_2431_, 8);
v_snapshotTasks_2440_ = lean_ctor_get(v___x_2431_, 9);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2431_, 5);
lean_dec(v_unused_2535_);
v___x_2442_ = v___x_2431_;
v_isShared_2443_ = v_isSharedCheck_2534_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snapshotTasks_2440_);
lean_inc(v_infoState_2439_);
lean_inc(v_messages_2438_);
lean_inc(v_recordedDeps_2437_);
lean_inc(v_traceState_2436_);
lean_inc(v_auxDeclNGen_2435_);
lean_inc(v_ngen_2434_);
lean_inc(v_nextMacroScope_2433_);
lean_inc(v_env_2432_);
lean_dec(v___x_2431_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2534_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_inc(v_declName_2364_);
v___x_2444_ = l_Lean_markAuxRecursor(v_env_2432_, v_declName_2364_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 5, v___x_2415_);
lean_ctor_set(v___x_2442_, 0, v___x_2444_);
v___x_2446_ = v___x_2442_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_nextMacroScope_2433_);
lean_ctor_set(v_reuseFailAlloc_2533_, 2, v_ngen_2434_);
lean_ctor_set(v_reuseFailAlloc_2533_, 3, v_auxDeclNGen_2435_);
lean_ctor_set(v_reuseFailAlloc_2533_, 4, v_traceState_2436_);
lean_ctor_set(v_reuseFailAlloc_2533_, 5, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2533_, 6, v_recordedDeps_2437_);
lean_ctor_set(v_reuseFailAlloc_2533_, 7, v_messages_2438_);
lean_ctor_set(v_reuseFailAlloc_2533_, 8, v_infoState_2439_);
lean_ctor_set(v_reuseFailAlloc_2533_, 9, v_snapshotTasks_2440_);
v___x_2446_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v_mctx_2449_; lean_object* v_zetaDeltaFVarIds_2450_; lean_object* v_postponed_2451_; lean_object* v_diag_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2531_; 
v___x_2447_ = lean_st_ref_put(v_a_2369_, v___x_2446_);
v___x_2448_ = lean_st_ref_take(v_a_2367_);
v_mctx_2449_ = lean_ctor_get(v___x_2448_, 0);
v_zetaDeltaFVarIds_2450_ = lean_ctor_get(v___x_2448_, 2);
v_postponed_2451_ = lean_ctor_get(v___x_2448_, 3);
v_diag_2452_ = lean_ctor_get(v___x_2448_, 4);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; 
v_unused_2532_ = lean_ctor_get(v___x_2448_, 1);
lean_dec(v_unused_2532_);
v___x_2454_ = v___x_2448_;
v_isShared_2455_ = v_isSharedCheck_2531_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_diag_2452_);
lean_inc(v_postponed_2451_);
lean_inc(v_zetaDeltaFVarIds_2450_);
lean_inc(v_mctx_2449_);
lean_dec(v___x_2448_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2531_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 1, v___x_2427_);
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_mctx_2449_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_zetaDeltaFVarIds_2450_);
lean_ctor_set(v_reuseFailAlloc_2530_, 3, v_postponed_2451_);
lean_ctor_set(v_reuseFailAlloc_2530_, 4, v_diag_2452_);
v___x_2457_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_env_2460_; lean_object* v_nextMacroScope_2461_; lean_object* v_ngen_2462_; lean_object* v_auxDeclNGen_2463_; lean_object* v_traceState_2464_; lean_object* v_recordedDeps_2465_; lean_object* v_messages_2466_; lean_object* v_infoState_2467_; lean_object* v_snapshotTasks_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2528_; 
v___x_2458_ = lean_st_ref_put(v_a_2367_, v___x_2457_);
v___x_2459_ = lean_st_ref_take(v_a_2369_);
v_env_2460_ = lean_ctor_get(v___x_2459_, 0);
v_nextMacroScope_2461_ = lean_ctor_get(v___x_2459_, 1);
v_ngen_2462_ = lean_ctor_get(v___x_2459_, 2);
v_auxDeclNGen_2463_ = lean_ctor_get(v___x_2459_, 3);
v_traceState_2464_ = lean_ctor_get(v___x_2459_, 4);
v_recordedDeps_2465_ = lean_ctor_get(v___x_2459_, 6);
v_messages_2466_ = lean_ctor_get(v___x_2459_, 7);
v_infoState_2467_ = lean_ctor_get(v___x_2459_, 8);
v_snapshotTasks_2468_ = lean_ctor_get(v___x_2459_, 9);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v___x_2459_, 5);
lean_dec(v_unused_2529_);
v___x_2470_ = v___x_2459_;
v_isShared_2471_ = v_isSharedCheck_2528_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_snapshotTasks_2468_);
lean_inc(v_infoState_2467_);
lean_inc(v_messages_2466_);
lean_inc(v_recordedDeps_2465_);
lean_inc(v_traceState_2464_);
lean_inc(v_auxDeclNGen_2463_);
lean_inc(v_ngen_2462_);
lean_inc(v_nextMacroScope_2461_);
lean_inc(v_env_2460_);
lean_dec(v___x_2459_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2528_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_inc(v_declName_2364_);
v___x_2472_ = l_Lean_Meta_addToCompletionBlackList(v_env_2460_, v_declName_2364_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 5, v___x_2415_);
lean_ctor_set(v___x_2470_, 0, v___x_2472_);
v___x_2474_ = v___x_2470_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v_nextMacroScope_2461_);
lean_ctor_set(v_reuseFailAlloc_2527_, 2, v_ngen_2462_);
lean_ctor_set(v_reuseFailAlloc_2527_, 3, v_auxDeclNGen_2463_);
lean_ctor_set(v_reuseFailAlloc_2527_, 4, v_traceState_2464_);
lean_ctor_set(v_reuseFailAlloc_2527_, 5, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2527_, 6, v_recordedDeps_2465_);
lean_ctor_set(v_reuseFailAlloc_2527_, 7, v_messages_2466_);
lean_ctor_set(v_reuseFailAlloc_2527_, 8, v_infoState_2467_);
lean_ctor_set(v_reuseFailAlloc_2527_, 9, v_snapshotTasks_2468_);
v___x_2474_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v_mctx_2477_; lean_object* v_zetaDeltaFVarIds_2478_; lean_object* v_postponed_2479_; lean_object* v_diag_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2525_; 
v___x_2475_ = lean_st_ref_put(v_a_2369_, v___x_2474_);
v___x_2476_ = lean_st_ref_take(v_a_2367_);
v_mctx_2477_ = lean_ctor_get(v___x_2476_, 0);
v_zetaDeltaFVarIds_2478_ = lean_ctor_get(v___x_2476_, 2);
v_postponed_2479_ = lean_ctor_get(v___x_2476_, 3);
v_diag_2480_ = lean_ctor_get(v___x_2476_, 4);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; 
v_unused_2526_ = lean_ctor_get(v___x_2476_, 1);
lean_dec(v_unused_2526_);
v___x_2482_ = v___x_2476_;
v_isShared_2483_ = v_isSharedCheck_2525_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_diag_2480_);
lean_inc(v_postponed_2479_);
lean_inc(v_zetaDeltaFVarIds_2478_);
lean_inc(v_mctx_2477_);
lean_dec(v___x_2476_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2525_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2427_);
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_mctx_2477_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v_zetaDeltaFVarIds_2478_);
lean_ctor_set(v_reuseFailAlloc_2524_, 3, v_postponed_2479_);
lean_ctor_set(v_reuseFailAlloc_2524_, 4, v_diag_2480_);
v___x_2485_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v_env_2488_; lean_object* v_nextMacroScope_2489_; lean_object* v_ngen_2490_; lean_object* v_auxDeclNGen_2491_; lean_object* v_traceState_2492_; lean_object* v_recordedDeps_2493_; lean_object* v_messages_2494_; lean_object* v_infoState_2495_; lean_object* v_snapshotTasks_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2522_; 
v___x_2486_ = lean_st_ref_put(v_a_2367_, v___x_2485_);
v___x_2487_ = lean_st_ref_take(v_a_2369_);
v_env_2488_ = lean_ctor_get(v___x_2487_, 0);
v_nextMacroScope_2489_ = lean_ctor_get(v___x_2487_, 1);
v_ngen_2490_ = lean_ctor_get(v___x_2487_, 2);
v_auxDeclNGen_2491_ = lean_ctor_get(v___x_2487_, 3);
v_traceState_2492_ = lean_ctor_get(v___x_2487_, 4);
v_recordedDeps_2493_ = lean_ctor_get(v___x_2487_, 6);
v_messages_2494_ = lean_ctor_get(v___x_2487_, 7);
v_infoState_2495_ = lean_ctor_get(v___x_2487_, 8);
v_snapshotTasks_2496_ = lean_ctor_get(v___x_2487_, 9);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2522_ == 0)
{
lean_object* v_unused_2523_; 
v_unused_2523_ = lean_ctor_get(v___x_2487_, 5);
lean_dec(v_unused_2523_);
v___x_2498_ = v___x_2487_;
v_isShared_2499_ = v_isSharedCheck_2522_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_snapshotTasks_2496_);
lean_inc(v_infoState_2495_);
lean_inc(v_messages_2494_);
lean_inc(v_recordedDeps_2493_);
lean_inc(v_traceState_2492_);
lean_inc(v_auxDeclNGen_2491_);
lean_inc(v_ngen_2490_);
lean_inc(v_nextMacroScope_2489_);
lean_inc(v_env_2488_);
lean_dec(v___x_2487_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2522_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2500_; lean_object* v___x_2502_; 
lean_inc(v_declName_2364_);
v___x_2500_ = l_Lean_addProtected(v_env_2488_, v_declName_2364_);
if (v_isShared_2499_ == 0)
{
lean_ctor_set(v___x_2498_, 5, v___x_2415_);
lean_ctor_set(v___x_2498_, 0, v___x_2500_);
v___x_2502_ = v___x_2498_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2500_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_nextMacroScope_2489_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v_ngen_2490_);
lean_ctor_set(v_reuseFailAlloc_2521_, 3, v_auxDeclNGen_2491_);
lean_ctor_set(v_reuseFailAlloc_2521_, 4, v_traceState_2492_);
lean_ctor_set(v_reuseFailAlloc_2521_, 5, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2521_, 6, v_recordedDeps_2493_);
lean_ctor_set(v_reuseFailAlloc_2521_, 7, v_messages_2494_);
lean_ctor_set(v_reuseFailAlloc_2521_, 8, v_infoState_2495_);
lean_ctor_set(v_reuseFailAlloc_2521_, 9, v_snapshotTasks_2496_);
v___x_2502_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v_mctx_2505_; lean_object* v_zetaDeltaFVarIds_2506_; lean_object* v_postponed_2507_; lean_object* v_diag_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2519_; 
v___x_2503_ = lean_st_ref_put(v_a_2369_, v___x_2502_);
v___x_2504_ = lean_st_ref_take(v_a_2367_);
v_mctx_2505_ = lean_ctor_get(v___x_2504_, 0);
v_zetaDeltaFVarIds_2506_ = lean_ctor_get(v___x_2504_, 2);
v_postponed_2507_ = lean_ctor_get(v___x_2504_, 3);
v_diag_2508_ = lean_ctor_get(v___x_2504_, 4);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v___x_2504_, 1);
lean_dec(v_unused_2520_);
v___x_2510_ = v___x_2504_;
v_isShared_2511_ = v_isSharedCheck_2519_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_diag_2508_);
lean_inc(v_postponed_2507_);
lean_inc(v_zetaDeltaFVarIds_2506_);
lean_inc(v_mctx_2505_);
lean_dec(v___x_2504_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2519_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
lean_ctor_set(v___x_2510_, 1, v___x_2427_);
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_mctx_2505_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v___x_2427_);
lean_ctor_set(v_reuseFailAlloc_2518_, 2, v_zetaDeltaFVarIds_2506_);
lean_ctor_set(v_reuseFailAlloc_2518_, 3, v_postponed_2507_);
lean_ctor_set(v_reuseFailAlloc_2518_, 4, v_diag_2508_);
v___x_2513_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = lean_st_ref_put(v_a_2367_, v___x_2513_);
v___x_2515_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2364_);
v___x_2516_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2515_, v_declName_2364_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v___x_2517_; 
lean_dec_ref_known(v___x_2516_, 1);
v___x_2517_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2364_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v___x_2517_;
}
else
{
lean_dec(v_declName_2364_);
return v___x_2516_;
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
}
}
}
}
}
}
else
{
lean_dec(v_declName_2364_);
return v___x_2400_;
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_dec(v_levelParams_2381_);
lean_dec(v_declName_2364_);
v_a_2544_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2394_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2394_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
lean_dec(v___x_2384_);
lean_dec_ref(v_type_2382_);
lean_dec(v_levelParams_2381_);
lean_dec(v_name_2380_);
lean_dec(v___x_2377_);
lean_del_object(v___x_2375_);
lean_dec_ref(v_val_2373_);
lean_dec(v_indName_2365_);
lean_dec(v_declName_2364_);
v___x_2553_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2554_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2553_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v___x_2554_;
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v___x_2377_);
lean_del_object(v___x_2375_);
lean_dec_ref(v_val_2373_);
lean_dec(v_indName_2365_);
lean_dec(v_declName_2364_);
v_a_2555_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2378_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2378_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_a_2372_);
lean_dec(v_indName_2365_);
lean_dec(v_declName_2364_);
v___x_2564_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2565_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2564_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v___x_2565_;
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec(v_indName_2365_);
lean_dec(v_declName_2364_);
v_a_2566_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2371_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2371_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2574_, lean_object* v_indName_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2574_, v_indName_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_);
lean_dec(v_a_2579_);
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2582_, lean_object* v_name_2583_, lean_object* v_type_2584_, lean_object* v_k_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2583_, v_type_2584_, v_k_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2592_, lean_object* v_name_2593_, lean_object* v_type_2594_, lean_object* v_k_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2592_, v_name_2593_, v_type_2594_, v_k_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2602_, lean_object* v_params_2603_, lean_object* v_alts_2604_, lean_object* v___x_2605_, lean_object* v_ism2_2606_, lean_object* v_motive_2607_, lean_object* v_val_2608_, lean_object* v_indName_2609_, lean_object* v___x_2610_, lean_object* v___x_2611_, lean_object* v___x_2612_, lean_object* v_as_2613_, size_t v_sz_2614_, size_t v_i_2615_, lean_object* v_bs_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2602_, v_params_2603_, v_alts_2604_, v___x_2605_, v_ism2_2606_, v_motive_2607_, v_val_2608_, v_indName_2609_, v___x_2610_, v___x_2611_, v___x_2612_, v_sz_2614_, v_i_2615_, v_bs_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2623_ = _args[0];
lean_object* v_params_2624_ = _args[1];
lean_object* v_alts_2625_ = _args[2];
lean_object* v___x_2626_ = _args[3];
lean_object* v_ism2_2627_ = _args[4];
lean_object* v_motive_2628_ = _args[5];
lean_object* v_val_2629_ = _args[6];
lean_object* v_indName_2630_ = _args[7];
lean_object* v___x_2631_ = _args[8];
lean_object* v___x_2632_ = _args[9];
lean_object* v___x_2633_ = _args[10];
lean_object* v_as_2634_ = _args[11];
lean_object* v_sz_2635_ = _args[12];
lean_object* v_i_2636_ = _args[13];
lean_object* v_bs_2637_ = _args[14];
lean_object* v___y_2638_ = _args[15];
lean_object* v___y_2639_ = _args[16];
lean_object* v___y_2640_ = _args[17];
lean_object* v___y_2641_ = _args[18];
lean_object* v___y_2642_ = _args[19];
_start:
{
size_t v_sz_boxed_2643_; size_t v_i_boxed_2644_; lean_object* v_res_2645_; 
v_sz_boxed_2643_ = lean_unbox_usize(v_sz_2635_);
lean_dec(v_sz_2635_);
v_i_boxed_2644_ = lean_unbox_usize(v_i_2636_);
lean_dec(v_i_2636_);
v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2623_, v_params_2624_, v_alts_2625_, v___x_2626_, v_ism2_2627_, v_motive_2628_, v_val_2629_, v_indName_2630_, v___x_2631_, v___x_2632_, v___x_2633_, v_as_2634_, v_sz_boxed_2643_, v_i_boxed_2644_, v_bs_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec_ref(v_as_2634_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2646_, lean_object* v_params_2647_, lean_object* v___x_2648_, lean_object* v_motive_2649_, lean_object* v_as_2650_, size_t v_sz_2651_, size_t v_i_2652_, lean_object* v_bs_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2646_, v_params_2647_, v___x_2648_, v_motive_2649_, v_sz_2651_, v_i_2652_, v_bs_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2660_, lean_object* v_params_2661_, lean_object* v___x_2662_, lean_object* v_motive_2663_, lean_object* v_as_2664_, lean_object* v_sz_2665_, lean_object* v_i_2666_, lean_object* v_bs_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
size_t v_sz_boxed_2673_; size_t v_i_boxed_2674_; lean_object* v_res_2675_; 
v_sz_boxed_2673_ = lean_unbox_usize(v_sz_2665_);
lean_dec(v_sz_2665_);
v_i_boxed_2674_ = lean_unbox_usize(v_i_2666_);
lean_dec(v_i_2666_);
v_res_2675_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2660_, v_params_2661_, v___x_2662_, v_motive_2663_, v_as_2664_, v_sz_boxed_2673_, v_i_boxed_2674_, v_bs_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec_ref(v_as_2664_);
lean_dec_ref(v_params_2661_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2676_, uint8_t v_s_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2676_, v_s_2677_, v___y_2679_, v___y_2681_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2684_, lean_object* v_s_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v_s_boxed_2691_; lean_object* v_res_2692_; 
v_s_boxed_2691_ = lean_unbox(v_s_2685_);
v_res_2692_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2684_, v_s_boxed_2691_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2693_, lean_object* v_constName_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2701_, lean_object* v_constName_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2701_, v_constName_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2709_, lean_object* v_attrName_2710_, lean_object* v_declName_2711_, lean_object* v_asyncPrefix_x3f_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2710_, v_declName_2711_, v_asyncPrefix_x3f_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2719_, lean_object* v_attrName_2720_, lean_object* v_declName_2721_, lean_object* v_asyncPrefix_x3f_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2719_, v_attrName_2720_, v_declName_2721_, v_asyncPrefix_x3f_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2729_, lean_object* v_attrName_2730_, lean_object* v_declName_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2730_, v_declName_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2738_, lean_object* v_attrName_2739_, lean_object* v_declName_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2738_, v_attrName_2739_, v_declName_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2747_, lean_object* v_ref_2748_, lean_object* v_constName_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2748_, v_constName_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2756_, lean_object* v_ref_2757_, lean_object* v_constName_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2756_, v_ref_2757_, v_constName_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v_ref_2757_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2765_, lean_object* v_msg_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2773_, lean_object* v_msg_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2773_, v_msg_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2781_, lean_object* v_ref_2782_, lean_object* v_msg_2783_, lean_object* v_declHint_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2782_, v_msg_2783_, v_declHint_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2791_, lean_object* v_ref_2792_, lean_object* v_msg_2793_, lean_object* v_declHint_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2791_, v_ref_2792_, v_msg_2793_, v_declHint_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v_ref_2792_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2801_, lean_object* v_declHint_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; 
v___x_2808_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2801_, v_declHint_2802_, v___y_2806_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2809_, lean_object* v_declHint_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2809_, v_declHint_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2817_, lean_object* v_ref_2818_, lean_object* v_msg_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2818_, v_msg_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2826_, lean_object* v_ref_2827_, lean_object* v_msg_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2826_, v_ref_2827_, v_msg_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v_ref_2827_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2835_, lean_object* v___y_2836_){
_start:
{
uint8_t v___x_2838_; 
v___x_2838_ = l_Lean_Expr_hasMVar(v_e_2835_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v_e_2835_);
return v___x_2839_;
}
else
{
lean_object* v___x_2840_; lean_object* v_mctx_2841_; lean_object* v___x_2842_; lean_object* v_fst_2843_; lean_object* v_snd_2844_; lean_object* v___x_2845_; lean_object* v_cache_2846_; lean_object* v_zetaDeltaFVarIds_2847_; lean_object* v_postponed_2848_; lean_object* v_diag_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2858_; 
v___x_2840_ = lean_st_ref_get(v___y_2836_);
v_mctx_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc_ref(v_mctx_2841_);
lean_dec(v___x_2840_);
v___x_2842_ = l_Lean_instantiateMVarsCore(v_mctx_2841_, v_e_2835_);
v_fst_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_fst_2843_);
v_snd_2844_ = lean_ctor_get(v___x_2842_, 1);
lean_inc(v_snd_2844_);
lean_dec_ref(v___x_2842_);
v___x_2845_ = lean_st_ref_take(v___y_2836_);
v_cache_2846_ = lean_ctor_get(v___x_2845_, 1);
v_zetaDeltaFVarIds_2847_ = lean_ctor_get(v___x_2845_, 2);
v_postponed_2848_ = lean_ctor_get(v___x_2845_, 3);
v_diag_2849_ = lean_ctor_get(v___x_2845_, 4);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v___x_2845_, 0);
lean_dec(v_unused_2859_);
v___x_2851_ = v___x_2845_;
v_isShared_2852_ = v_isSharedCheck_2858_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_diag_2849_);
lean_inc(v_postponed_2848_);
lean_inc(v_zetaDeltaFVarIds_2847_);
lean_inc(v_cache_2846_);
lean_dec(v___x_2845_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2858_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 0, v_snd_2844_);
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_snd_2844_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_cache_2846_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_zetaDeltaFVarIds_2847_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_postponed_2848_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_diag_2849_);
v___x_2854_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2855_ = lean_st_ref_put(v___y_2836_, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v_fst_2843_);
return v___x_2856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2860_, v___y_2861_);
lean_dec(v___y_2861_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2864_, v___y_2866_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2878_, lean_object* v_info_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v___x_2883_; lean_object* v_env_2884_; lean_object* v_nextMacroScope_2885_; lean_object* v_ngen_2886_; lean_object* v_auxDeclNGen_2887_; lean_object* v_traceState_2888_; lean_object* v_recordedDeps_2889_; lean_object* v_messages_2890_; lean_object* v_infoState_2891_; lean_object* v_snapshotTasks_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2919_; 
v___x_2883_ = lean_st_ref_take(v___y_2881_);
v_env_2884_ = lean_ctor_get(v___x_2883_, 0);
v_nextMacroScope_2885_ = lean_ctor_get(v___x_2883_, 1);
v_ngen_2886_ = lean_ctor_get(v___x_2883_, 2);
v_auxDeclNGen_2887_ = lean_ctor_get(v___x_2883_, 3);
v_traceState_2888_ = lean_ctor_get(v___x_2883_, 4);
v_recordedDeps_2889_ = lean_ctor_get(v___x_2883_, 6);
v_messages_2890_ = lean_ctor_get(v___x_2883_, 7);
v_infoState_2891_ = lean_ctor_get(v___x_2883_, 8);
v_snapshotTasks_2892_ = lean_ctor_get(v___x_2883_, 9);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2883_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2883_, 5);
lean_dec(v_unused_2920_);
v___x_2894_ = v___x_2883_;
v_isShared_2895_ = v_isSharedCheck_2919_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_snapshotTasks_2892_);
lean_inc(v_infoState_2891_);
lean_inc(v_messages_2890_);
lean_inc(v_recordedDeps_2889_);
lean_inc(v_traceState_2888_);
lean_inc(v_auxDeclNGen_2887_);
lean_inc(v_ngen_2886_);
lean_inc(v_nextMacroScope_2885_);
lean_inc(v_env_2884_);
lean_dec(v___x_2883_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2919_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v___x_2896_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2884_, v_matcherName_2878_, v_info_2879_);
v___x_2897_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 5, v___x_2897_);
lean_ctor_set(v___x_2894_, 0, v___x_2896_);
v___x_2899_ = v___x_2894_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_nextMacroScope_2885_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_ngen_2886_);
lean_ctor_set(v_reuseFailAlloc_2918_, 3, v_auxDeclNGen_2887_);
lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_traceState_2888_);
lean_ctor_set(v_reuseFailAlloc_2918_, 5, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2918_, 6, v_recordedDeps_2889_);
lean_ctor_set(v_reuseFailAlloc_2918_, 7, v_messages_2890_);
lean_ctor_set(v_reuseFailAlloc_2918_, 8, v_infoState_2891_);
lean_ctor_set(v_reuseFailAlloc_2918_, 9, v_snapshotTasks_2892_);
v___x_2899_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v_mctx_2902_; lean_object* v_zetaDeltaFVarIds_2903_; lean_object* v_postponed_2904_; lean_object* v_diag_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2916_; 
v___x_2900_ = lean_st_ref_put(v___y_2881_, v___x_2899_);
v___x_2901_ = lean_st_ref_take(v___y_2880_);
v_mctx_2902_ = lean_ctor_get(v___x_2901_, 0);
v_zetaDeltaFVarIds_2903_ = lean_ctor_get(v___x_2901_, 2);
v_postponed_2904_ = lean_ctor_get(v___x_2901_, 3);
v_diag_2905_ = lean_ctor_get(v___x_2901_, 4);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; 
v_unused_2917_ = lean_ctor_get(v___x_2901_, 1);
lean_dec(v_unused_2917_);
v___x_2907_ = v___x_2901_;
v_isShared_2908_ = v_isSharedCheck_2916_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_diag_2905_);
lean_inc(v_postponed_2904_);
lean_inc(v_zetaDeltaFVarIds_2903_);
lean_inc(v_mctx_2902_);
lean_dec(v___x_2901_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2916_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2909_ = lean_box(0);
v___x_2910_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 1, v___x_2910_);
v___x_2912_ = v___x_2907_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_mctx_2902_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2915_, 2, v_zetaDeltaFVarIds_2903_);
lean_ctor_set(v_reuseFailAlloc_2915_, 3, v_postponed_2904_);
lean_ctor_set(v_reuseFailAlloc_2915_, 4, v_diag_2905_);
v___x_2912_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_st_ref_put(v___y_2880_, v___x_2912_);
v___x_2914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2914_, 0, v___x_2909_);
return v___x_2914_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2921_, lean_object* v_info_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2921_, v_info_2922_, v___y_2923_, v___y_2924_);
lean_dec(v___y_2924_);
lean_dec(v___y_2923_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2927_, lean_object* v_info_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2927_, v_info_2928_, v___y_2930_, v___y_2932_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2935_, lean_object* v_info_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2935_, v_info_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2943_, lean_object* v___x_2944_, lean_object* v_newEqs1_2945_, uint8_t v___x_2946_, uint8_t v___x_2947_, uint8_t v___x_2948_, lean_object* v_ism1_x27_2949_, lean_object* v_ism2_x27_2950_, lean_object* v_newRefls1_2951_, lean_object* v_newEqs2_2952_, lean_object* v_newRefls2_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = l_Lean_mkAppN(v_motive_2943_, v___x_2944_);
v___x_2960_ = l_Array_append___redArg(v_newEqs1_2945_, v_newEqs2_2952_);
v___x_2961_ = l_Lean_Meta_mkForallFVars(v___x_2960_, v___x_2959_, v___x_2946_, v___x_2947_, v___x_2947_, v___x_2948_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec_ref(v___x_2960_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v_a_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_a_2962_);
lean_dec_ref_known(v___x_2961_, 1);
v___x_2963_ = l_Array_append___redArg(v_ism1_x27_2949_, v_ism2_x27_2950_);
v___x_2964_ = l_Lean_Meta_mkLambdaFVars(v___x_2963_, v_a_2962_, v___x_2946_, v___x_2947_, v___x_2946_, v___x_2947_, v___x_2948_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec_ref(v___x_2963_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2974_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2967_ = v___x_2964_;
v_isShared_2968_ = v_isSharedCheck_2974_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_a_2965_);
lean_dec(v___x_2964_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2974_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2969_ = l_Array_append___redArg(v_newRefls1_2951_, v_newRefls2_2953_);
v___x_2970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2970_, 0, v_a_2965_);
lean_ctor_set(v___x_2970_, 1, v___x_2969_);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 0, v___x_2970_);
v___x_2972_ = v___x_2967_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_dec_ref(v_newRefls1_2951_);
v_a_2975_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2964_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2964_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v_newRefls1_2951_);
lean_dec_ref(v_ism1_x27_2949_);
v_a_2983_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2961_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2961_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2991_, lean_object* v___x_2992_, lean_object* v_newEqs1_2993_, lean_object* v___x_2994_, lean_object* v___x_2995_, lean_object* v___x_2996_, lean_object* v_ism1_x27_2997_, lean_object* v_ism2_x27_2998_, lean_object* v_newRefls1_2999_, lean_object* v_newEqs2_3000_, lean_object* v_newRefls2_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
uint8_t v___x_14959__boxed_3007_; uint8_t v___x_14960__boxed_3008_; uint8_t v___x_14961__boxed_3009_; lean_object* v_res_3010_; 
v___x_14959__boxed_3007_ = lean_unbox(v___x_2994_);
v___x_14960__boxed_3008_ = lean_unbox(v___x_2995_);
v___x_14961__boxed_3009_ = lean_unbox(v___x_2996_);
v_res_3010_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2991_, v___x_2992_, v_newEqs1_2993_, v___x_14959__boxed_3007_, v___x_14960__boxed_3008_, v___x_14961__boxed_3009_, v_ism1_x27_2997_, v_ism2_x27_2998_, v_newRefls1_2999_, v_newEqs2_3000_, v_newRefls2_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
lean_dec_ref(v_newRefls2_3001_);
lean_dec_ref(v_newEqs2_3000_);
lean_dec_ref(v_ism2_x27_2998_);
lean_dec_ref(v___x_2992_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_3011_, lean_object* v___x_3012_, uint8_t v___x_3013_, uint8_t v___x_3014_, uint8_t v___x_3015_, lean_object* v_ism1_x27_3016_, lean_object* v_ism2_x27_3017_, lean_object* v_is_3018_, lean_object* v___x_3019_, lean_object* v_newEqs1_3020_, lean_object* v_newRefls1_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___f_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3027_ = lean_box(v___x_3013_);
v___x_3028_ = lean_box(v___x_3014_);
v___x_3029_ = lean_box(v___x_3015_);
lean_inc_ref(v_ism2_x27_3017_);
v___f_3030_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3030_, 0, v_motive_3011_);
lean_closure_set(v___f_3030_, 1, v___x_3012_);
lean_closure_set(v___f_3030_, 2, v_newEqs1_3020_);
lean_closure_set(v___f_3030_, 3, v___x_3027_);
lean_closure_set(v___f_3030_, 4, v___x_3028_);
lean_closure_set(v___f_3030_, 5, v___x_3029_);
lean_closure_set(v___f_3030_, 6, v_ism1_x27_3016_);
lean_closure_set(v___f_3030_, 7, v_ism2_x27_3017_);
lean_closure_set(v___f_3030_, 8, v_newRefls1_3021_);
v___x_3031_ = lean_array_push(v_is_3018_, v___x_3019_);
v___x_3032_ = l_Lean_Meta_withNewEqs___redArg(v___x_3031_, v_ism2_x27_3017_, v___f_3030_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_3033_, lean_object* v___x_3034_, lean_object* v___x_3035_, lean_object* v___x_3036_, lean_object* v___x_3037_, lean_object* v_ism1_x27_3038_, lean_object* v_ism2_x27_3039_, lean_object* v_is_3040_, lean_object* v___x_3041_, lean_object* v_newEqs1_3042_, lean_object* v_newRefls1_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
uint8_t v___x_15050__boxed_3049_; uint8_t v___x_15051__boxed_3050_; uint8_t v___x_15052__boxed_3051_; lean_object* v_res_3052_; 
v___x_15050__boxed_3049_ = lean_unbox(v___x_3035_);
v___x_15051__boxed_3050_ = lean_unbox(v___x_3036_);
v___x_15052__boxed_3051_ = lean_unbox(v___x_3037_);
v_res_3052_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_3033_, v___x_3034_, v___x_15050__boxed_3049_, v___x_15051__boxed_3050_, v___x_15052__boxed_3051_, v_ism1_x27_3038_, v_ism2_x27_3039_, v_is_3040_, v___x_3041_, v_newEqs1_3042_, v_newRefls1_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_3053_, uint8_t v___x_3054_, lean_object* v___y_3055_, lean_object* v___y_3056_, lean_object* v___y_3057_, lean_object* v___y_3058_){
_start:
{
lean_object* v___x_3060_; 
v___x_3060_ = l_Lean_addDecl(v___x_3053_, v___x_3054_, v___y_3057_, v___y_3058_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3061_, lean_object* v___x_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
uint8_t v___x_15092__boxed_3068_; lean_object* v_res_3069_; 
v___x_15092__boxed_3068_ = lean_unbox(v___x_3062_);
v_res_3069_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3061_, v___x_15092__boxed_3068_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec(v___y_3066_);
lean_dec_ref(v___y_3065_);
lean_dec(v___y_3064_);
lean_dec_ref(v___y_3063_);
return v_res_3069_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3072_ = l_Lean_stringToMessageData(v___x_3071_);
return v___x_3072_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3075_ = l_Lean_stringToMessageData(v___x_3074_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = lean_box(0);
v___x_3082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3083_ = l_Lean_mkConst(v___x_3082_, v___x_3081_);
return v___x_3083_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3086_ = l_Lean_stringToMessageData(v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3087_, lean_object* v_a_3088_, lean_object* v___x_3089_, lean_object* v_zs1_3090_, lean_object* v_snd_3091_, uint8_t v___x_3092_, uint8_t v___x_3093_, uint8_t v___x_3094_, lean_object* v_alts_3095_, lean_object* v_zs2_3096_, lean_object* v___ctorRet2_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = lean_array_get_borrowed(v___x_3087_, v_a_3088_, v___x_3089_);
lean_inc_ref(v_zs1_3090_);
v___x_3104_ = l_Array_append___redArg(v_zs1_3090_, v_zs2_3096_);
lean_inc(v___x_3103_);
v___x_3105_ = l_Lean_Meta_instantiateForall(v___x_3103_, v___x_3104_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
v___x_3107_ = lean_box(0);
v___x_3108_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3106_, v___x_3107_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3110_ = l_Lean_Expr_mvarId_x21(v_a_3109_);
v___x_3111_ = lean_array_get_size(v_snd_3091_);
v___x_3112_ = lean_box(0);
v___x_3113_ = lean_box(0);
lean_inc_ref(v___y_3100_);
v___x_3114_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3111_, v___x_3110_, v___x_3112_, v___x_3113_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
if (lean_obj_tag(v_a_3115_) == 1)
{
lean_object* v_val_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3163_; 
v_val_3116_ = lean_ctor_get(v_a_3115_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v_a_3115_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3118_ = v_a_3115_;
v_isShared_3119_ = v_isSharedCheck_3163_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_val_3116_);
lean_dec(v_a_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3163_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v_fst_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3161_; 
v_fst_3120_ = lean_ctor_get(v_val_3116_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_val_3116_);
if (v_isSharedCheck_3161_ == 0)
{
lean_object* v_unused_3162_; 
v_unused_3162_ = lean_ctor_get(v_val_3116_, 1);
lean_dec(v_unused_3162_);
v___x_3122_ = v_val_3116_;
v_isShared_3123_ = v_isSharedCheck_3161_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_fst_3120_);
lean_dec(v_val_3116_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3161_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___y_3125_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; 
v___x_3153_ = lean_array_get_borrowed(v___x_3087_, v_alts_3095_, v___x_3089_);
v___x_3154_ = lean_array_get_size(v_zs1_3090_);
lean_dec_ref(v_zs1_3090_);
v___x_3155_ = lean_unsigned_to_nat(0u);
v___x_3156_ = lean_nat_dec_eq(v___x_3154_, v___x_3155_);
if (v___x_3156_ == 0)
{
lean_inc(v___x_3153_);
v___y_3125_ = v___x_3153_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3157_; uint8_t v___x_3158_; 
v___x_3157_ = lean_array_get_size(v_zs2_3096_);
v___x_3158_ = lean_nat_dec_eq(v___x_3157_, v___x_3155_);
if (v___x_3158_ == 0)
{
lean_inc(v___x_3153_);
v___y_3125_ = v___x_3153_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3153_);
v___x_3160_ = l_Lean_Expr_app___override(v___x_3153_, v___x_3159_);
v___y_3125_ = v___x_3160_;
goto v___jp_3124_;
}
}
v___jp_3124_:
{
uint8_t v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = 0;
v___x_3127_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3127_, 0, v___x_3126_);
lean_ctor_set_uint8(v___x_3127_, 1, v___x_3092_);
lean_ctor_set_uint8(v___x_3127_, 2, v___x_3093_);
lean_ctor_set_uint8(v___x_3127_, 3, v___x_3092_);
lean_inc_ref(v___y_3125_);
lean_inc(v_fst_3120_);
v___x_3128_ = l_Lean_MVarId_apply(v_fst_3120_, v___y_3125_, v___x_3127_, v___x_3113_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_a_3129_);
lean_dec_ref_known(v___x_3128_, 1);
if (lean_obj_tag(v_a_3129_) == 0)
{
lean_object* v___x_3130_; 
lean_dec_ref(v___y_3125_);
lean_del_object(v___x_3122_);
lean_dec(v_fst_3120_);
lean_del_object(v___x_3118_);
v___x_3130_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3109_, v___y_3099_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3132_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
lean_inc(v_a_3131_);
lean_dec_ref_known(v___x_3130_, 1);
v___x_3132_ = l_Lean_Meta_mkLambdaFVars(v___x_3104_, v_a_3131_, v___x_3093_, v___x_3092_, v___x_3093_, v___x_3092_, v___x_3094_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
lean_dec_ref(v___x_3104_);
return v___x_3132_;
}
else
{
lean_dec_ref(v___x_3104_);
return v___x_3130_;
}
}
else
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3136_; 
lean_dec(v_a_3129_);
lean_dec(v_a_3109_);
lean_dec_ref(v___x_3104_);
v___x_3133_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3134_ = l_Lean_MessageData_ofExpr(v___y_3125_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set_tag(v___x_3122_, 7);
lean_ctor_set(v___x_3122_, 1, v___x_3134_);
lean_ctor_set(v___x_3122_, 0, v___x_3133_);
v___x_3136_ = v___x_3122_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3144_, 1, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3137_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3136_);
lean_ctor_set(v___x_3138_, 1, v___x_3137_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v_fst_3120_);
v___x_3140_ = v___x_3118_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_fst_3120_);
v___x_3140_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3138_);
lean_ctor_set(v___x_3141_, 1, v___x_3140_);
v___x_3142_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3141_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v___y_3125_);
lean_del_object(v___x_3122_);
lean_dec(v_fst_3120_);
lean_del_object(v___x_3118_);
lean_dec(v_a_3109_);
lean_dec_ref(v___x_3104_);
v_a_3145_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3128_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3128_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
lean_dec(v_a_3115_);
lean_dec(v_a_3109_);
lean_dec_ref(v___x_3104_);
lean_dec_ref(v_zs1_3090_);
v___x_3164_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3165_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3164_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
return v___x_3165_;
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec(v_a_3109_);
lean_dec_ref(v___x_3104_);
lean_dec_ref(v_zs1_3090_);
v_a_3166_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3114_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3114_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
else
{
lean_dec_ref(v___x_3104_);
lean_dec_ref(v_zs1_3090_);
return v___x_3108_;
}
}
else
{
lean_dec_ref(v___x_3104_);
lean_dec_ref(v_zs1_3090_);
return v___x_3105_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3174_, lean_object* v_a_3175_, lean_object* v___x_3176_, lean_object* v_zs1_3177_, lean_object* v_snd_3178_, lean_object* v___x_3179_, lean_object* v___x_3180_, lean_object* v___x_3181_, lean_object* v_alts_3182_, lean_object* v_zs2_3183_, lean_object* v___ctorRet2_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
uint8_t v___x_15152__boxed_3190_; uint8_t v___x_15153__boxed_3191_; uint8_t v___x_15154__boxed_3192_; lean_object* v_res_3193_; 
v___x_15152__boxed_3190_ = lean_unbox(v___x_3179_);
v___x_15153__boxed_3191_ = lean_unbox(v___x_3180_);
v___x_15154__boxed_3192_ = lean_unbox(v___x_3181_);
v_res_3193_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3174_, v_a_3175_, v___x_3176_, v_zs1_3177_, v_snd_3178_, v___x_15152__boxed_3190_, v___x_15153__boxed_3191_, v___x_15154__boxed_3192_, v_alts_3182_, v_zs2_3183_, v___ctorRet2_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec_ref(v___ctorRet2_3184_);
lean_dec_ref(v_zs2_3183_);
lean_dec_ref(v_alts_3182_);
lean_dec_ref(v_snd_3178_);
lean_dec(v___x_3176_);
lean_dec_ref(v_a_3175_);
lean_dec_ref(v___x_3174_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3194_, lean_object* v_a_3195_, lean_object* v___x_3196_, lean_object* v_snd_3197_, uint8_t v___x_3198_, uint8_t v___x_3199_, uint8_t v___x_3200_, lean_object* v_alts_3201_, lean_object* v_a_3202_, lean_object* v_zs1_3203_, lean_object* v___ctorRet1_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___f_3213_; lean_object* v___x_3214_; 
v___x_3210_ = lean_box(v___x_3198_);
v___x_3211_ = lean_box(v___x_3199_);
v___x_3212_ = lean_box(v___x_3200_);
v___f_3213_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3213_, 0, v___x_3194_);
lean_closure_set(v___f_3213_, 1, v_a_3195_);
lean_closure_set(v___f_3213_, 2, v___x_3196_);
lean_closure_set(v___f_3213_, 3, v_zs1_3203_);
lean_closure_set(v___f_3213_, 4, v_snd_3197_);
lean_closure_set(v___f_3213_, 5, v___x_3210_);
lean_closure_set(v___f_3213_, 6, v___x_3211_);
lean_closure_set(v___f_3213_, 7, v___x_3212_);
lean_closure_set(v___f_3213_, 8, v_alts_3201_);
v___x_3214_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3202_, v___f_3213_, v___x_3199_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3215_, lean_object* v_a_3216_, lean_object* v___x_3217_, lean_object* v_snd_3218_, lean_object* v___x_3219_, lean_object* v___x_3220_, lean_object* v___x_3221_, lean_object* v_alts_3222_, lean_object* v_a_3223_, lean_object* v_zs1_3224_, lean_object* v___ctorRet1_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
uint8_t v___x_15351__boxed_3231_; uint8_t v___x_15352__boxed_3232_; uint8_t v___x_15353__boxed_3233_; lean_object* v_res_3234_; 
v___x_15351__boxed_3231_ = lean_unbox(v___x_3219_);
v___x_15352__boxed_3232_ = lean_unbox(v___x_3220_);
v___x_15353__boxed_3233_ = lean_unbox(v___x_3221_);
v_res_3234_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3215_, v_a_3216_, v___x_3217_, v_snd_3218_, v___x_15351__boxed_3231_, v___x_15352__boxed_3232_, v___x_15353__boxed_3233_, v_alts_3222_, v_a_3223_, v_zs1_3224_, v___ctorRet1_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec_ref(v___ctorRet1_3225_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3235_, lean_object* v_params_3236_, lean_object* v_a_3237_, lean_object* v_snd_3238_, lean_object* v_alts_3239_, size_t v_sz_3240_, size_t v_i_3241_, lean_object* v_bs_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
uint8_t v___x_3248_; 
v___x_3248_ = lean_usize_dec_lt(v_i_3241_, v_sz_3240_);
if (v___x_3248_ == 0)
{
lean_object* v___x_3249_; 
lean_dec_ref(v_alts_3239_);
lean_dec_ref(v_snd_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_tail_3235_);
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v_bs_3242_);
return v___x_3249_;
}
else
{
lean_object* v___x_3250_; uint8_t v___x_3251_; uint8_t v___x_3252_; lean_object* v_v_3253_; lean_object* v___x_3254_; lean_object* v_bs_x27_3255_; lean_object* v___y_3257_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3250_ = l_Lean_instInhabitedExpr;
v___x_3251_ = 0;
v___x_3252_ = 1;
v_v_3253_ = lean_array_uget(v_bs_3242_, v_i_3241_);
v___x_3254_ = lean_unsigned_to_nat(0u);
v_bs_x27_3255_ = lean_array_uset(v_bs_3242_, v_i_3241_, v___x_3254_);
v___x_3271_ = lean_usize_to_nat(v_i_3241_);
lean_inc(v_tail_3235_);
v___x_3272_ = l_Lean_mkConst(v_v_3253_, v_tail_3235_);
v___x_3273_ = l_Lean_mkAppN(v___x_3272_, v_params_3236_);
lean_inc(v___y_3246_);
lean_inc_ref(v___y_3245_);
lean_inc(v___y_3244_);
lean_inc_ref(v___y_3243_);
v___x_3274_ = lean_infer_type(v___x_3273_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc_n(v_a_3275_, 2);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = lean_box(v___x_3248_);
v___x_3277_ = lean_box(v___x_3251_);
v___x_3278_ = lean_box(v___x_3252_);
lean_inc_ref(v_alts_3239_);
lean_inc_ref(v_snd_3238_);
lean_inc_ref(v_a_3237_);
v___f_3279_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3279_, 0, v___x_3250_);
lean_closure_set(v___f_3279_, 1, v_a_3237_);
lean_closure_set(v___f_3279_, 2, v___x_3271_);
lean_closure_set(v___f_3279_, 3, v_snd_3238_);
lean_closure_set(v___f_3279_, 4, v___x_3276_);
lean_closure_set(v___f_3279_, 5, v___x_3277_);
lean_closure_set(v___f_3279_, 6, v___x_3278_);
lean_closure_set(v___f_3279_, 7, v_alts_3239_);
lean_closure_set(v___f_3279_, 8, v_a_3275_);
v___x_3280_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3275_, v___f_3279_, v___x_3251_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
v___y_3257_ = v___x_3280_;
goto v___jp_3256_;
}
else
{
lean_dec(v___x_3271_);
v___y_3257_ = v___x_3274_;
goto v___jp_3256_;
}
v___jp_3256_:
{
if (lean_obj_tag(v___y_3257_) == 0)
{
lean_object* v_a_3258_; size_t v___x_3259_; size_t v___x_3260_; lean_object* v___x_3261_; 
v_a_3258_ = lean_ctor_get(v___y_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref_known(v___y_3257_, 1);
v___x_3259_ = ((size_t)1ULL);
v___x_3260_ = lean_usize_add(v_i_3241_, v___x_3259_);
v___x_3261_ = lean_array_uset(v_bs_x27_3255_, v_i_3241_, v_a_3258_);
v_i_3241_ = v___x_3260_;
v_bs_3242_ = v___x_3261_;
goto _start;
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec_ref(v_bs_x27_3255_);
lean_dec_ref(v_alts_3239_);
lean_dec_ref(v_snd_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_tail_3235_);
v_a_3263_ = lean_ctor_get(v___y_3257_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___y_3257_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___y_3257_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___y_3257_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3281_, lean_object* v_params_3282_, lean_object* v_a_3283_, lean_object* v_snd_3284_, lean_object* v_alts_3285_, lean_object* v_sz_3286_, lean_object* v_i_3287_, lean_object* v_bs_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
size_t v_sz_boxed_3294_; size_t v_i_boxed_3295_; lean_object* v_res_3296_; 
v_sz_boxed_3294_ = lean_unbox_usize(v_sz_3286_);
lean_dec(v_sz_3286_);
v_i_boxed_3295_ = lean_unbox_usize(v_i_3287_);
lean_dec(v_i_3287_);
v_res_3296_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3281_, v_params_3282_, v_a_3283_, v_snd_3284_, v_alts_3285_, v_sz_boxed_3294_, v_i_boxed_3295_, v_bs_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec_ref(v_params_3282_);
return v_res_3296_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = lean_box(0);
v___x_3298_ = lean_unsigned_to_nat(16u);
v___x_3299_ = lean_mk_array(v___x_3298_, v___x_3297_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3300_, lean_object* v___x_3301_, uint8_t v___x_3302_, uint8_t v___x_3303_, uint8_t v___x_3304_, lean_object* v_ism1_x27_3305_, lean_object* v_is_3306_, lean_object* v___x_3307_, lean_object* v___x_3308_, lean_object* v___x_3309_, lean_object* v___x_3310_, lean_object* v_params_3311_, lean_object* v___x_3312_, lean_object* v___x_3313_, lean_object* v_heq_3314_, lean_object* v_val_3315_, lean_object* v_tail_3316_, lean_object* v_alts_3317_, size_t v_sz_3318_, size_t v___x_3319_, lean_object* v___x_3320_, lean_object* v___x_3321_, lean_object* v_declName_3322_, lean_object* v_levelParams_3323_, lean_object* v_numIndices_3324_, lean_object* v___x_3325_, lean_object* v___x_3326_, lean_object* v_numParams_3327_, lean_object* v_snd_3328_, lean_object* v_ism2_x27_3329_, lean_object* v_x_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___f_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3336_ = lean_box(v___x_3302_);
v___x_3337_ = lean_box(v___x_3303_);
v___x_3338_ = lean_box(v___x_3304_);
lean_inc_ref(v___x_3307_);
lean_inc_ref_n(v_is_3306_, 2);
lean_inc_ref(v_ism1_x27_3305_);
lean_inc_ref(v_motive_3300_);
v___f_3339_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3339_, 0, v_motive_3300_);
lean_closure_set(v___f_3339_, 1, v___x_3301_);
lean_closure_set(v___f_3339_, 2, v___x_3336_);
lean_closure_set(v___f_3339_, 3, v___x_3337_);
lean_closure_set(v___f_3339_, 4, v___x_3338_);
lean_closure_set(v___f_3339_, 5, v_ism1_x27_3305_);
lean_closure_set(v___f_3339_, 6, v_ism2_x27_3329_);
lean_closure_set(v___f_3339_, 7, v_is_3306_);
lean_closure_set(v___f_3339_, 8, v___x_3307_);
lean_inc_ref(v___x_3308_);
v___x_3340_ = lean_array_push(v_is_3306_, v___x_3308_);
v___x_3341_ = l_Lean_Meta_withNewEqs___redArg(v___x_3340_, v_ism1_x27_3305_, v___f_3339_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v_fst_3343_; lean_object* v_snd_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3445_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v_fst_3343_ = lean_ctor_get(v_a_3342_, 0);
v_snd_3344_ = lean_ctor_get(v_a_3342_, 1);
v_isSharedCheck_3445_ = !lean_is_exclusive(v_a_3342_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3346_ = v_a_3342_;
v_isShared_3347_ = v_isSharedCheck_3445_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_snd_3344_);
lean_inc(v_fst_3343_);
lean_dec(v_a_3342_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3445_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3348_ = l_Lean_mkConst(v___x_3309_, v___x_3310_);
v___x_3349_ = l_Lean_mkAppN(v___x_3348_, v_params_3311_);
v___x_3350_ = l_Lean_Expr_app___override(v___x_3349_, v_fst_3343_);
lean_inc_ref(v_is_3306_);
v___x_3351_ = l_Array_append___redArg(v_is_3306_, v___x_3312_);
v___x_3352_ = l_Array_append___redArg(v___x_3351_, v_is_3306_);
v___x_3353_ = l_Array_append___redArg(v___x_3352_, v___x_3313_);
v___x_3354_ = l_Lean_mkAppN(v___x_3350_, v___x_3353_);
lean_dec_ref(v___x_3353_);
lean_inc_ref(v_heq_3314_);
v___x_3355_ = l_Lean_Expr_app___override(v___x_3354_, v_heq_3314_);
v___x_3356_ = l_Lean_InductiveVal_numCtors(v_val_3315_);
lean_inc_ref(v___x_3355_);
v___x_3357_ = l_Lean_Meta_inferArgumentTypesN(v___x_3356_, v___x_3355_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3357_, 1);
lean_inc_ref(v_alts_3317_);
lean_inc(v_snd_3344_);
v___x_3359_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3316_, v_params_3311_, v_a_3358_, v_snd_3344_, v_alts_3317_, v_sz_3318_, v___x_3319_, v___x_3320_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3361_ = l_Lean_mkAppN(v___x_3355_, v_a_3360_);
lean_dec(v_a_3360_);
v___x_3362_ = l_Lean_mkAppN(v___x_3361_, v_snd_3344_);
lean_dec(v_snd_3344_);
lean_inc_ref(v___x_3321_);
v___x_3363_ = lean_array_push(v___x_3321_, v_motive_3300_);
v___x_3364_ = l_Array_append___redArg(v_params_3311_, v___x_3363_);
lean_dec_ref(v___x_3363_);
v___x_3365_ = l_Array_append___redArg(v___x_3364_, v_is_3306_);
lean_dec_ref(v_is_3306_);
v___x_3366_ = lean_unsigned_to_nat(2u);
v___x_3367_ = lean_mk_empty_array_with_capacity(v___x_3366_);
v___x_3368_ = lean_array_push(v___x_3367_, v___x_3308_);
v___x_3369_ = lean_array_push(v___x_3368_, v___x_3307_);
v___x_3370_ = l_Array_append___redArg(v___x_3365_, v___x_3369_);
lean_dec_ref(v___x_3369_);
v___x_3371_ = lean_array_push(v___x_3321_, v_heq_3314_);
v___x_3372_ = l_Array_append___redArg(v___x_3370_, v___x_3371_);
lean_dec_ref(v___x_3371_);
v___x_3373_ = l_Array_append___redArg(v___x_3372_, v_alts_3317_);
lean_dec_ref(v_alts_3317_);
v___x_3374_ = l_Lean_Meta_mkLambdaFVars(v___x_3373_, v___x_3362_, v___x_3302_, v___x_3303_, v___x_3302_, v___x_3303_, v___x_3304_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
lean_dec_ref(v___x_3373_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3376_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc_n(v_a_3375_, 2);
lean_dec_ref_known(v___x_3374_, 1);
lean_inc(v___y_3334_);
lean_inc_ref(v___y_3333_);
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3331_);
v___x_3376_ = lean_infer_type(v_a_3375_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v_a_3380_; lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3412_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
lean_dec_ref_known(v___x_3376_, 1);
v___x_3378_ = lean_box(1);
lean_inc(v_declName_3322_);
v___x_3379_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3322_, v_levelParams_3323_, v_a_3377_, v_a_3375_, v___x_3378_, v___y_3334_);
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3382_ = v___x_3379_;
v_isShared_3383_ = v_isSharedCheck_3412_;
goto v_resetjp_3381_;
}
else
{
lean_inc(v_a_3380_);
lean_dec(v___x_3379_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3412_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3385_; 
if (v_isShared_3383_ == 0)
{
lean_ctor_set_tag(v___x_3382_, 1);
v___x_3385_ = v___x_3382_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3380_);
v___x_3385_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; lean_object* v___f_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3397_; 
v___x_3386_ = lean_box(v___x_3302_);
lean_inc_ref(v___x_3385_);
v___f_3387_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3387_, 0, v___x_3385_);
lean_closure_set(v___f_3387_, 1, v___x_3386_);
v___x_3388_ = lean_nat_add(v_numIndices_3324_, v___x_3325_);
lean_inc(v___x_3326_);
v___x_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3326_);
v___x_3390_ = lean_box(0);
v___x_3391_ = lean_mk_empty_array_with_capacity(v___x_3325_);
v___x_3392_ = lean_array_push(v___x_3391_, v___x_3390_);
v___x_3393_ = lean_array_push(v___x_3392_, v___x_3390_);
v___x_3394_ = lean_array_push(v___x_3393_, v___x_3390_);
v___x_3395_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 1, v___x_3395_);
lean_ctor_set(v___x_3346_, 0, v___x_3326_);
v___x_3397_ = v___x_3346_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3326_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
lean_object* v___x_3398_; uint8_t v___y_3400_; uint8_t v___x_3409_; 
v___x_3398_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3398_, 0, v_numParams_3327_);
lean_ctor_set(v___x_3398_, 1, v___x_3388_);
lean_ctor_set(v___x_3398_, 2, v_snd_3328_);
lean_ctor_set(v___x_3398_, 3, v___x_3389_);
lean_ctor_set(v___x_3398_, 4, v___x_3394_);
lean_ctor_set(v___x_3398_, 5, v___x_3397_);
v___x_3409_ = l_Lean_isPrivateName(v_declName_3322_);
if (v___x_3409_ == 0)
{
v___y_3400_ = v___x_3303_;
goto v___jp_3399_;
}
else
{
v___y_3400_ = v___x_3302_;
goto v___jp_3399_;
}
v___jp_3399_:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3387_, v___y_3400_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3401_) == 0)
{
lean_object* v___x_3402_; lean_object* v___x_3403_; 
lean_dec_ref_known(v___x_3401_, 1);
v___x_3402_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3322_);
v___x_3403_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3402_, v_declName_3322_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3403_) == 0)
{
lean_object* v___x_3404_; uint8_t v___x_3405_; lean_object* v___x_3406_; 
lean_dec_ref_known(v___x_3403_, 1);
lean_inc_n(v_declName_3322_, 2);
v___x_3404_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3322_, v___x_3398_, v___y_3332_, v___y_3334_);
lean_dec_ref(v___x_3404_);
v___x_3405_ = 0;
v___x_3406_ = l_Lean_Meta_setInlineAttribute(v_declName_3322_, v___x_3405_, v___y_3331_, v___y_3332_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v___x_3407_; 
lean_dec_ref_known(v___x_3406_, 1);
v___x_3407_ = l_Lean_enableRealizationsForConst(v_declName_3322_, v___y_3333_, v___y_3334_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v___x_3408_; 
lean_dec_ref_known(v___x_3407_, 1);
v___x_3408_ = l_Lean_compileDecl(v___x_3385_, v___x_3303_, v___y_3333_, v___y_3334_);
return v___x_3408_;
}
else
{
lean_dec_ref(v___x_3385_);
return v___x_3407_;
}
}
else
{
lean_dec_ref(v___x_3385_);
lean_dec(v_declName_3322_);
return v___x_3406_;
}
}
else
{
lean_dec_ref_known(v___x_3398_, 6);
lean_dec_ref(v___x_3385_);
lean_dec(v_declName_3322_);
return v___x_3403_;
}
}
else
{
lean_dec_ref_known(v___x_3398_, 6);
lean_dec_ref(v___x_3385_);
lean_dec(v_declName_3322_);
return v___x_3401_;
}
}
}
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v_a_3375_);
lean_del_object(v___x_3346_);
lean_dec_ref(v_snd_3328_);
lean_dec(v_numParams_3327_);
lean_dec(v___x_3326_);
lean_dec(v_levelParams_3323_);
lean_dec(v_declName_3322_);
v_a_3413_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3376_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3376_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_del_object(v___x_3346_);
lean_dec_ref(v_snd_3328_);
lean_dec(v_numParams_3327_);
lean_dec(v___x_3326_);
lean_dec(v_levelParams_3323_);
lean_dec(v_declName_3322_);
v_a_3421_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3374_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3374_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec_ref(v_snd_3328_);
lean_dec(v_numParams_3327_);
lean_dec(v___x_3326_);
lean_dec(v_levelParams_3323_);
lean_dec(v_declName_3322_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v_alts_3317_);
lean_dec_ref(v_heq_3314_);
lean_dec_ref(v_params_3311_);
lean_dec_ref(v___x_3308_);
lean_dec_ref(v___x_3307_);
lean_dec_ref(v_is_3306_);
lean_dec_ref(v_motive_3300_);
v_a_3429_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3359_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3359_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec_ref(v___x_3355_);
lean_del_object(v___x_3346_);
lean_dec(v_snd_3344_);
lean_dec_ref(v_snd_3328_);
lean_dec(v_numParams_3327_);
lean_dec(v___x_3326_);
lean_dec(v_levelParams_3323_);
lean_dec(v_declName_3322_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v___x_3320_);
lean_dec_ref(v_alts_3317_);
lean_dec(v_tail_3316_);
lean_dec_ref(v_heq_3314_);
lean_dec_ref(v_params_3311_);
lean_dec_ref(v___x_3308_);
lean_dec_ref(v___x_3307_);
lean_dec_ref(v_is_3306_);
lean_dec_ref(v_motive_3300_);
v_a_3437_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3357_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3357_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
else
{
lean_object* v_a_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3453_; 
lean_dec_ref(v_snd_3328_);
lean_dec(v_numParams_3327_);
lean_dec(v___x_3326_);
lean_dec(v_levelParams_3323_);
lean_dec(v_declName_3322_);
lean_dec_ref(v___x_3321_);
lean_dec_ref(v___x_3320_);
lean_dec_ref(v_alts_3317_);
lean_dec(v_tail_3316_);
lean_dec_ref(v_heq_3314_);
lean_dec_ref(v_params_3311_);
lean_dec(v___x_3310_);
lean_dec(v___x_3309_);
lean_dec_ref(v___x_3308_);
lean_dec_ref(v___x_3307_);
lean_dec_ref(v_is_3306_);
lean_dec_ref(v_motive_3300_);
v_a_3446_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3448_ = v___x_3341_;
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_a_3446_);
lean_dec(v___x_3341_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3453_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3451_; 
if (v_isShared_3449_ == 0)
{
v___x_3451_ = v___x_3448_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3454_ = _args[0];
lean_object* v___x_3455_ = _args[1];
lean_object* v___x_3456_ = _args[2];
lean_object* v___x_3457_ = _args[3];
lean_object* v___x_3458_ = _args[4];
lean_object* v_ism1_x27_3459_ = _args[5];
lean_object* v_is_3460_ = _args[6];
lean_object* v___x_3461_ = _args[7];
lean_object* v___x_3462_ = _args[8];
lean_object* v___x_3463_ = _args[9];
lean_object* v___x_3464_ = _args[10];
lean_object* v_params_3465_ = _args[11];
lean_object* v___x_3466_ = _args[12];
lean_object* v___x_3467_ = _args[13];
lean_object* v_heq_3468_ = _args[14];
lean_object* v_val_3469_ = _args[15];
lean_object* v_tail_3470_ = _args[16];
lean_object* v_alts_3471_ = _args[17];
lean_object* v_sz_3472_ = _args[18];
lean_object* v___x_3473_ = _args[19];
lean_object* v___x_3474_ = _args[20];
lean_object* v___x_3475_ = _args[21];
lean_object* v_declName_3476_ = _args[22];
lean_object* v_levelParams_3477_ = _args[23];
lean_object* v_numIndices_3478_ = _args[24];
lean_object* v___x_3479_ = _args[25];
lean_object* v___x_3480_ = _args[26];
lean_object* v_numParams_3481_ = _args[27];
lean_object* v_snd_3482_ = _args[28];
lean_object* v_ism2_x27_3483_ = _args[29];
lean_object* v_x_3484_ = _args[30];
lean_object* v___y_3485_ = _args[31];
lean_object* v___y_3486_ = _args[32];
lean_object* v___y_3487_ = _args[33];
lean_object* v___y_3488_ = _args[34];
lean_object* v___y_3489_ = _args[35];
_start:
{
uint8_t v___x_15490__boxed_3490_; uint8_t v___x_15491__boxed_3491_; uint8_t v___x_15492__boxed_3492_; size_t v_sz_boxed_3493_; size_t v___x_15501__boxed_3494_; lean_object* v_res_3495_; 
v___x_15490__boxed_3490_ = lean_unbox(v___x_3456_);
v___x_15491__boxed_3491_ = lean_unbox(v___x_3457_);
v___x_15492__boxed_3492_ = lean_unbox(v___x_3458_);
v_sz_boxed_3493_ = lean_unbox_usize(v_sz_3472_);
lean_dec(v_sz_3472_);
v___x_15501__boxed_3494_ = lean_unbox_usize(v___x_3473_);
lean_dec(v___x_3473_);
v_res_3495_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3454_, v___x_3455_, v___x_15490__boxed_3490_, v___x_15491__boxed_3491_, v___x_15492__boxed_3492_, v_ism1_x27_3459_, v_is_3460_, v___x_3461_, v___x_3462_, v___x_3463_, v___x_3464_, v_params_3465_, v___x_3466_, v___x_3467_, v_heq_3468_, v_val_3469_, v_tail_3470_, v_alts_3471_, v_sz_boxed_3493_, v___x_15501__boxed_3494_, v___x_3474_, v___x_3475_, v_declName_3476_, v_levelParams_3477_, v_numIndices_3478_, v___x_3479_, v___x_3480_, v_numParams_3481_, v_snd_3482_, v_ism2_x27_3483_, v_x_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v_x_3484_);
lean_dec(v___x_3479_);
lean_dec(v_numIndices_3478_);
lean_dec_ref(v_val_3469_);
lean_dec_ref(v___x_3467_);
lean_dec_ref(v___x_3466_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3496_, lean_object* v___x_3497_, uint8_t v___x_3498_, uint8_t v___x_3499_, uint8_t v___x_3500_, lean_object* v_is_3501_, lean_object* v___x_3502_, lean_object* v___x_3503_, lean_object* v___x_3504_, lean_object* v___x_3505_, lean_object* v_params_3506_, lean_object* v___x_3507_, lean_object* v___x_3508_, lean_object* v_heq_3509_, lean_object* v_val_3510_, lean_object* v_tail_3511_, lean_object* v_alts_3512_, size_t v_sz_3513_, size_t v___x_3514_, lean_object* v___x_3515_, lean_object* v___x_3516_, lean_object* v_declName_3517_, lean_object* v_levelParams_3518_, lean_object* v_numIndices_3519_, lean_object* v___x_3520_, lean_object* v___x_3521_, lean_object* v_numParams_3522_, lean_object* v_snd_3523_, lean_object* v___x_3524_, lean_object* v___x_3525_, lean_object* v_ism1_x27_3526_, lean_object* v_x_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_){
_start:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___f_3538_; lean_object* v___x_3539_; 
v___x_3533_ = lean_box(v___x_3498_);
v___x_3534_ = lean_box(v___x_3499_);
v___x_3535_ = lean_box(v___x_3500_);
v___x_3536_ = lean_box_usize(v_sz_3513_);
v___x_3537_ = lean_box_usize(v___x_3514_);
v___f_3538_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3538_, 0, v_motive_3496_);
lean_closure_set(v___f_3538_, 1, v___x_3497_);
lean_closure_set(v___f_3538_, 2, v___x_3533_);
lean_closure_set(v___f_3538_, 3, v___x_3534_);
lean_closure_set(v___f_3538_, 4, v___x_3535_);
lean_closure_set(v___f_3538_, 5, v_ism1_x27_3526_);
lean_closure_set(v___f_3538_, 6, v_is_3501_);
lean_closure_set(v___f_3538_, 7, v___x_3502_);
lean_closure_set(v___f_3538_, 8, v___x_3503_);
lean_closure_set(v___f_3538_, 9, v___x_3504_);
lean_closure_set(v___f_3538_, 10, v___x_3505_);
lean_closure_set(v___f_3538_, 11, v_params_3506_);
lean_closure_set(v___f_3538_, 12, v___x_3507_);
lean_closure_set(v___f_3538_, 13, v___x_3508_);
lean_closure_set(v___f_3538_, 14, v_heq_3509_);
lean_closure_set(v___f_3538_, 15, v_val_3510_);
lean_closure_set(v___f_3538_, 16, v_tail_3511_);
lean_closure_set(v___f_3538_, 17, v_alts_3512_);
lean_closure_set(v___f_3538_, 18, v___x_3536_);
lean_closure_set(v___f_3538_, 19, v___x_3537_);
lean_closure_set(v___f_3538_, 20, v___x_3515_);
lean_closure_set(v___f_3538_, 21, v___x_3516_);
lean_closure_set(v___f_3538_, 22, v_declName_3517_);
lean_closure_set(v___f_3538_, 23, v_levelParams_3518_);
lean_closure_set(v___f_3538_, 24, v_numIndices_3519_);
lean_closure_set(v___f_3538_, 25, v___x_3520_);
lean_closure_set(v___f_3538_, 26, v___x_3521_);
lean_closure_set(v___f_3538_, 27, v_numParams_3522_);
lean_closure_set(v___f_3538_, 28, v_snd_3523_);
v___x_3539_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3524_, v___x_3525_, v___f_3538_, v___x_3498_, v___x_3498_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
return v___x_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3540_ = _args[0];
lean_object* v___x_3541_ = _args[1];
lean_object* v___x_3542_ = _args[2];
lean_object* v___x_3543_ = _args[3];
lean_object* v___x_3544_ = _args[4];
lean_object* v_is_3545_ = _args[5];
lean_object* v___x_3546_ = _args[6];
lean_object* v___x_3547_ = _args[7];
lean_object* v___x_3548_ = _args[8];
lean_object* v___x_3549_ = _args[9];
lean_object* v_params_3550_ = _args[10];
lean_object* v___x_3551_ = _args[11];
lean_object* v___x_3552_ = _args[12];
lean_object* v_heq_3553_ = _args[13];
lean_object* v_val_3554_ = _args[14];
lean_object* v_tail_3555_ = _args[15];
lean_object* v_alts_3556_ = _args[16];
lean_object* v_sz_3557_ = _args[17];
lean_object* v___x_3558_ = _args[18];
lean_object* v___x_3559_ = _args[19];
lean_object* v___x_3560_ = _args[20];
lean_object* v_declName_3561_ = _args[21];
lean_object* v_levelParams_3562_ = _args[22];
lean_object* v_numIndices_3563_ = _args[23];
lean_object* v___x_3564_ = _args[24];
lean_object* v___x_3565_ = _args[25];
lean_object* v_numParams_3566_ = _args[26];
lean_object* v_snd_3567_ = _args[27];
lean_object* v___x_3568_ = _args[28];
lean_object* v___x_3569_ = _args[29];
lean_object* v_ism1_x27_3570_ = _args[30];
lean_object* v_x_3571_ = _args[31];
lean_object* v___y_3572_ = _args[32];
lean_object* v___y_3573_ = _args[33];
lean_object* v___y_3574_ = _args[34];
lean_object* v___y_3575_ = _args[35];
lean_object* v___y_3576_ = _args[36];
_start:
{
uint8_t v___x_15812__boxed_3577_; uint8_t v___x_15813__boxed_3578_; uint8_t v___x_15814__boxed_3579_; size_t v_sz_boxed_3580_; size_t v___x_15823__boxed_3581_; lean_object* v_res_3582_; 
v___x_15812__boxed_3577_ = lean_unbox(v___x_3542_);
v___x_15813__boxed_3578_ = lean_unbox(v___x_3543_);
v___x_15814__boxed_3579_ = lean_unbox(v___x_3544_);
v_sz_boxed_3580_ = lean_unbox_usize(v_sz_3557_);
lean_dec(v_sz_3557_);
v___x_15823__boxed_3581_ = lean_unbox_usize(v___x_3558_);
lean_dec(v___x_3558_);
v_res_3582_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3540_, v___x_3541_, v___x_15812__boxed_3577_, v___x_15813__boxed_3578_, v___x_15814__boxed_3579_, v_is_3545_, v___x_3546_, v___x_3547_, v___x_3548_, v___x_3549_, v_params_3550_, v___x_3551_, v___x_3552_, v_heq_3553_, v_val_3554_, v_tail_3555_, v_alts_3556_, v_sz_boxed_3580_, v___x_15823__boxed_3581_, v___x_3559_, v___x_3560_, v_declName_3561_, v_levelParams_3562_, v_numIndices_3563_, v___x_3564_, v___x_3565_, v_numParams_3566_, v_snd_3567_, v___x_3568_, v___x_3569_, v_ism1_x27_3570_, v_x_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
lean_dec(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec_ref(v_x_3571_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3583_, lean_object* v___x_3584_, lean_object* v_motive_3585_, lean_object* v___x_3586_, uint8_t v___x_3587_, uint8_t v___x_3588_, uint8_t v___x_3589_, lean_object* v_is_3590_, lean_object* v___x_3591_, lean_object* v___x_3592_, lean_object* v___x_3593_, lean_object* v___x_3594_, lean_object* v_params_3595_, lean_object* v___x_3596_, lean_object* v___x_3597_, lean_object* v_heq_3598_, lean_object* v_val_3599_, lean_object* v_tail_3600_, size_t v_sz_3601_, size_t v___x_3602_, lean_object* v___x_3603_, lean_object* v___x_3604_, lean_object* v_declName_3605_, lean_object* v_levelParams_3606_, lean_object* v___x_3607_, lean_object* v___x_3608_, lean_object* v_numParams_3609_, lean_object* v_snd_3610_, lean_object* v___x_3611_, lean_object* v_alts_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___f_3625_; lean_object* v___x_3626_; 
v___x_3618_ = lean_nat_add(v_numIndices_3583_, v___x_3584_);
v___x_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
v___x_3620_ = lean_box(v___x_3587_);
v___x_3621_ = lean_box(v___x_3588_);
v___x_3622_ = lean_box(v___x_3589_);
v___x_3623_ = lean_box_usize(v_sz_3601_);
v___x_3624_ = lean_box_usize(v___x_3602_);
lean_inc_ref(v___x_3619_);
lean_inc_ref(v___x_3611_);
v___f_3625_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3625_, 0, v_motive_3585_);
lean_closure_set(v___f_3625_, 1, v___x_3586_);
lean_closure_set(v___f_3625_, 2, v___x_3620_);
lean_closure_set(v___f_3625_, 3, v___x_3621_);
lean_closure_set(v___f_3625_, 4, v___x_3622_);
lean_closure_set(v___f_3625_, 5, v_is_3590_);
lean_closure_set(v___f_3625_, 6, v___x_3591_);
lean_closure_set(v___f_3625_, 7, v___x_3592_);
lean_closure_set(v___f_3625_, 8, v___x_3593_);
lean_closure_set(v___f_3625_, 9, v___x_3594_);
lean_closure_set(v___f_3625_, 10, v_params_3595_);
lean_closure_set(v___f_3625_, 11, v___x_3596_);
lean_closure_set(v___f_3625_, 12, v___x_3597_);
lean_closure_set(v___f_3625_, 13, v_heq_3598_);
lean_closure_set(v___f_3625_, 14, v_val_3599_);
lean_closure_set(v___f_3625_, 15, v_tail_3600_);
lean_closure_set(v___f_3625_, 16, v_alts_3612_);
lean_closure_set(v___f_3625_, 17, v___x_3623_);
lean_closure_set(v___f_3625_, 18, v___x_3624_);
lean_closure_set(v___f_3625_, 19, v___x_3603_);
lean_closure_set(v___f_3625_, 20, v___x_3604_);
lean_closure_set(v___f_3625_, 21, v_declName_3605_);
lean_closure_set(v___f_3625_, 22, v_levelParams_3606_);
lean_closure_set(v___f_3625_, 23, v_numIndices_3583_);
lean_closure_set(v___f_3625_, 24, v___x_3607_);
lean_closure_set(v___f_3625_, 25, v___x_3608_);
lean_closure_set(v___f_3625_, 26, v_numParams_3609_);
lean_closure_set(v___f_3625_, 27, v_snd_3610_);
lean_closure_set(v___f_3625_, 28, v___x_3611_);
lean_closure_set(v___f_3625_, 29, v___x_3619_);
v___x_3626_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3611_, v___x_3619_, v___f_3625_, v___x_3587_, v___x_3587_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3627_ = _args[0];
lean_object* v___x_3628_ = _args[1];
lean_object* v_motive_3629_ = _args[2];
lean_object* v___x_3630_ = _args[3];
lean_object* v___x_3631_ = _args[4];
lean_object* v___x_3632_ = _args[5];
lean_object* v___x_3633_ = _args[6];
lean_object* v_is_3634_ = _args[7];
lean_object* v___x_3635_ = _args[8];
lean_object* v___x_3636_ = _args[9];
lean_object* v___x_3637_ = _args[10];
lean_object* v___x_3638_ = _args[11];
lean_object* v_params_3639_ = _args[12];
lean_object* v___x_3640_ = _args[13];
lean_object* v___x_3641_ = _args[14];
lean_object* v_heq_3642_ = _args[15];
lean_object* v_val_3643_ = _args[16];
lean_object* v_tail_3644_ = _args[17];
lean_object* v_sz_3645_ = _args[18];
lean_object* v___x_3646_ = _args[19];
lean_object* v___x_3647_ = _args[20];
lean_object* v___x_3648_ = _args[21];
lean_object* v_declName_3649_ = _args[22];
lean_object* v_levelParams_3650_ = _args[23];
lean_object* v___x_3651_ = _args[24];
lean_object* v___x_3652_ = _args[25];
lean_object* v_numParams_3653_ = _args[26];
lean_object* v_snd_3654_ = _args[27];
lean_object* v___x_3655_ = _args[28];
lean_object* v_alts_3656_ = _args[29];
lean_object* v___y_3657_ = _args[30];
lean_object* v___y_3658_ = _args[31];
lean_object* v___y_3659_ = _args[32];
lean_object* v___y_3660_ = _args[33];
lean_object* v___y_3661_ = _args[34];
_start:
{
uint8_t v___x_15905__boxed_3662_; uint8_t v___x_15906__boxed_3663_; uint8_t v___x_15907__boxed_3664_; size_t v_sz_boxed_3665_; size_t v___x_15916__boxed_3666_; lean_object* v_res_3667_; 
v___x_15905__boxed_3662_ = lean_unbox(v___x_3631_);
v___x_15906__boxed_3663_ = lean_unbox(v___x_3632_);
v___x_15907__boxed_3664_ = lean_unbox(v___x_3633_);
v_sz_boxed_3665_ = lean_unbox_usize(v_sz_3645_);
lean_dec(v_sz_3645_);
v___x_15916__boxed_3666_ = lean_unbox_usize(v___x_3646_);
lean_dec(v___x_3646_);
v_res_3667_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3627_, v___x_3628_, v_motive_3629_, v___x_3630_, v___x_15905__boxed_3662_, v___x_15906__boxed_3663_, v___x_15907__boxed_3664_, v_is_3634_, v___x_3635_, v___x_3636_, v___x_3637_, v___x_3638_, v_params_3639_, v___x_3640_, v___x_3641_, v_heq_3642_, v_val_3643_, v_tail_3644_, v_sz_boxed_3665_, v___x_15916__boxed_3666_, v___x_3647_, v___x_3648_, v_declName_3649_, v_levelParams_3650_, v___x_3651_, v___x_3652_, v_numParams_3653_, v_snd_3654_, v___x_3655_, v_alts_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___x_3628_);
return v_res_3667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3668_, lean_object* v_declInfos_3669_, lean_object* v_k_3670_, lean_object* v_kind_3671_, lean_object* v_x_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
uint8_t v_kind_boxed_3678_; lean_object* v_res_3679_; 
v_kind_boxed_3678_ = lean_unbox(v_kind_3671_);
v_res_3679_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3668_, v_declInfos_3669_, v_k_3670_, v_kind_boxed_3678_, v_x_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3680_, lean_object* v_k_3681_, uint8_t v_kind_3682_, lean_object* v_acc_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v___x_3689_; lean_object* v_toApplicative_3690_; lean_object* v_toFunctor_3691_; lean_object* v_toSeq_3692_; lean_object* v_toSeqLeft_3693_; lean_object* v_toSeqRight_3694_; lean_object* v___f_3695_; lean_object* v___f_3696_; lean_object* v___f_3697_; lean_object* v___f_3698_; lean_object* v___x_3699_; lean_object* v___f_3700_; lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v_toApplicative_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3764_; 
v___x_3689_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3690_ = lean_ctor_get(v___x_3689_, 0);
v_toFunctor_3691_ = lean_ctor_get(v_toApplicative_3690_, 0);
v_toSeq_3692_ = lean_ctor_get(v_toApplicative_3690_, 2);
v_toSeqLeft_3693_ = lean_ctor_get(v_toApplicative_3690_, 3);
v_toSeqRight_3694_ = lean_ctor_get(v_toApplicative_3690_, 4);
v___f_3695_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3696_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3691_, 2);
v___f_3697_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3697_, 0, v_toFunctor_3691_);
v___f_3698_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3698_, 0, v_toFunctor_3691_);
v___x_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___f_3697_);
lean_ctor_set(v___x_3699_, 1, v___f_3698_);
lean_inc(v_toSeqRight_3694_);
v___f_3700_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3700_, 0, v_toSeqRight_3694_);
lean_inc(v_toSeqLeft_3693_);
v___f_3701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3701_, 0, v_toSeqLeft_3693_);
lean_inc(v_toSeq_3692_);
v___f_3702_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3702_, 0, v_toSeq_3692_);
v___x_3703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3699_);
lean_ctor_set(v___x_3703_, 1, v___f_3695_);
lean_ctor_set(v___x_3703_, 2, v___f_3702_);
lean_ctor_set(v___x_3703_, 3, v___f_3701_);
lean_ctor_set(v___x_3703_, 4, v___f_3700_);
v___x_3704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
lean_ctor_set(v___x_3704_, 1, v___f_3696_);
v___x_3705_ = l_StateRefT_x27_instMonad___redArg(v___x_3704_);
v_toApplicative_3706_ = lean_ctor_get(v___x_3705_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3705_);
if (v_isSharedCheck_3764_ == 0)
{
lean_object* v_unused_3765_; 
v_unused_3765_ = lean_ctor_get(v___x_3705_, 1);
lean_dec(v_unused_3765_);
v___x_3708_ = v___x_3705_;
v_isShared_3709_ = v_isSharedCheck_3764_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_toApplicative_3706_);
lean_dec(v___x_3705_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3764_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v_toFunctor_3710_; lean_object* v_toSeq_3711_; lean_object* v_toSeqLeft_3712_; lean_object* v_toSeqRight_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3762_; 
v_toFunctor_3710_ = lean_ctor_get(v_toApplicative_3706_, 0);
v_toSeq_3711_ = lean_ctor_get(v_toApplicative_3706_, 2);
v_toSeqLeft_3712_ = lean_ctor_get(v_toApplicative_3706_, 3);
v_toSeqRight_3713_ = lean_ctor_get(v_toApplicative_3706_, 4);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_toApplicative_3706_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v_toApplicative_3706_, 1);
lean_dec(v_unused_3763_);
v___x_3715_ = v_toApplicative_3706_;
v_isShared_3716_ = v_isSharedCheck_3762_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_toSeqRight_3713_);
lean_inc(v_toSeqLeft_3712_);
lean_inc(v_toSeq_3711_);
lean_inc(v_toFunctor_3710_);
lean_dec(v_toApplicative_3706_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3762_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___f_3717_; lean_object* v___f_3718_; lean_object* v___f_3719_; lean_object* v___f_3720_; lean_object* v___x_3721_; lean_object* v___f_3722_; lean_object* v___f_3723_; lean_object* v___f_3724_; lean_object* v___x_3726_; 
v___f_3717_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3718_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3710_);
v___f_3719_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3719_, 0, v_toFunctor_3710_);
v___f_3720_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3720_, 0, v_toFunctor_3710_);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___f_3719_);
lean_ctor_set(v___x_3721_, 1, v___f_3720_);
v___f_3722_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3722_, 0, v_toSeqRight_3713_);
v___f_3723_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3723_, 0, v_toSeqLeft_3712_);
v___f_3724_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3724_, 0, v_toSeq_3711_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 4, v___f_3722_);
lean_ctor_set(v___x_3715_, 3, v___f_3723_);
lean_ctor_set(v___x_3715_, 2, v___f_3724_);
lean_ctor_set(v___x_3715_, 1, v___f_3717_);
lean_ctor_set(v___x_3715_, 0, v___x_3721_);
v___x_3726_ = v___x_3715_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3761_, 1, v___f_3717_);
lean_ctor_set(v_reuseFailAlloc_3761_, 2, v___f_3724_);
lean_ctor_set(v_reuseFailAlloc_3761_, 3, v___f_3723_);
lean_ctor_set(v_reuseFailAlloc_3761_, 4, v___f_3722_);
v___x_3726_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
lean_object* v___x_3728_; 
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 1, v___f_3718_);
lean_ctor_set(v___x_3708_, 0, v___x_3726_);
v___x_3728_ = v___x_3708_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3726_);
lean_ctor_set(v_reuseFailAlloc_3760_, 1, v___f_3718_);
v___x_3728_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; uint8_t v___x_3731_; 
v___x_3729_ = lean_array_get_size(v_acc_3683_);
v___x_3730_ = lean_array_get_size(v_declInfos_3680_);
v___x_3731_ = lean_nat_dec_lt(v___x_3729_, v___x_3730_);
if (v___x_3731_ == 0)
{
lean_object* v___x_3732_; 
lean_dec_ref(v___x_3728_);
lean_dec_ref(v_declInfos_3680_);
lean_inc(v___y_3687_);
lean_inc_ref(v___y_3686_);
lean_inc(v___y_3685_);
lean_inc_ref(v___y_3684_);
v___x_3732_ = lean_apply_6(v_k_3681_, v_acc_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, lean_box(0));
return v___x_3732_;
}
else
{
lean_object* v___x_3733_; uint8_t v___x_3734_; lean_object* v___x_3735_; lean_object* v___f_3736_; lean_object* v___f_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v_snd_3742_; lean_object* v_fst_3743_; lean_object* v_fst_3744_; lean_object* v_snd_3745_; lean_object* v___x_3746_; lean_object* v___f_3747_; lean_object* v___x_3748_; 
v___x_3733_ = lean_box(0);
v___x_3734_ = 0;
v___x_3735_ = l_Lean_instInhabitedExpr;
v___f_3736_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3736_, 0, v___x_3728_);
lean_closure_set(v___f_3736_, 1, v___x_3735_);
v___f_3737_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3737_, 0, v___f_3736_);
v___x_3738_ = lean_box(v___x_3734_);
v___x_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
lean_ctor_set(v___x_3739_, 1, v___f_3737_);
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3733_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
v___x_3741_ = lean_array_get(v___x_3740_, v_declInfos_3680_, v___x_3729_);
lean_dec_ref_known(v___x_3740_, 2);
v_snd_3742_ = lean_ctor_get(v___x_3741_, 1);
lean_inc(v_snd_3742_);
v_fst_3743_ = lean_ctor_get(v___x_3741_, 0);
lean_inc(v_fst_3743_);
lean_dec(v___x_3741_);
v_fst_3744_ = lean_ctor_get(v_snd_3742_, 0);
lean_inc(v_fst_3744_);
v_snd_3745_ = lean_ctor_get(v_snd_3742_, 1);
lean_inc(v_snd_3745_);
lean_dec(v_snd_3742_);
v___x_3746_ = lean_box(v_kind_3682_);
lean_inc_ref(v_acc_3683_);
v___f_3747_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3747_, 0, v_acc_3683_);
lean_closure_set(v___f_3747_, 1, v_declInfos_3680_);
lean_closure_set(v___f_3747_, 2, v_k_3681_);
lean_closure_set(v___f_3747_, 3, v___x_3746_);
lean_inc(v___y_3687_);
lean_inc_ref(v___y_3686_);
lean_inc(v___y_3685_);
lean_inc_ref(v___y_3684_);
v___x_3748_ = lean_apply_6(v_snd_3745_, v_acc_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, lean_box(0));
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; uint8_t v___x_3750_; lean_object* v___x_3751_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
lean_dec_ref_known(v___x_3748_, 1);
v___x_3750_ = lean_unbox(v_fst_3744_);
lean_dec(v_fst_3744_);
v___x_3751_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3743_, v___x_3750_, v_a_3749_, v___f_3747_, v_kind_3682_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_);
return v___x_3751_;
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_dec_ref(v___f_3747_);
lean_dec(v_fst_3744_);
lean_dec(v_fst_3743_);
v_a_3752_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3748_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3748_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3766_, lean_object* v_declInfos_3767_, lean_object* v_k_3768_, uint8_t v_kind_3769_, lean_object* v_x_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = lean_array_push(v_acc_3766_, v_x_3770_);
v___x_3777_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3767_, v_k_3768_, v_kind_3769_, v___x_3776_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
return v___x_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3778_, lean_object* v_k_3779_, lean_object* v_kind_3780_, lean_object* v_acc_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_){
_start:
{
uint8_t v_kind_boxed_3787_; lean_object* v_res_3788_; 
v_kind_boxed_3787_ = lean_unbox(v_kind_3780_);
v_res_3788_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3778_, v_k_3779_, v_kind_boxed_3787_, v_acc_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
lean_dec(v___y_3785_);
lean_dec_ref(v___y_3784_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3789_, lean_object* v_k_3790_, uint8_t v_kind_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3798_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3789_, v_k_3790_, v_kind_3791_, v___x_3797_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3799_, lean_object* v_k_3800_, lean_object* v_kind_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
uint8_t v_kind_boxed_3807_; lean_object* v_res_3808_; 
v_kind_boxed_3807_ = lean_unbox(v_kind_3801_);
v_res_3808_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3799_, v_k_3800_, v_kind_boxed_3807_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3809_, lean_object* v_k_3810_, uint8_t v_kind_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
size_t v_sz_3817_; size_t v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v_sz_3817_ = lean_array_size(v_declInfos_3809_);
v___x_3818_ = ((size_t)0ULL);
v___x_3819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3817_, v___x_3818_, v_declInfos_3809_);
v___x_3820_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3819_, v_k_3810_, v_kind_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3821_, lean_object* v_k_3822_, lean_object* v_kind_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
uint8_t v_kind_boxed_3829_; lean_object* v_res_3830_; 
v_kind_boxed_3829_ = lean_unbox(v_kind_3823_);
v_res_3830_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3821_, v_k_3822_, v_kind_boxed_3829_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3831_, lean_object* v_k_3832_, uint8_t v_kind_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
size_t v_sz_3839_; size_t v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v_sz_3839_ = lean_array_size(v_declInfos_3831_);
v___x_3840_ = ((size_t)0ULL);
v___x_3841_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3839_, v___x_3840_, v_declInfos_3831_);
v___x_3842_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3841_, v_k_3832_, v_kind_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
return v___x_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3843_, lean_object* v_k_3844_, lean_object* v_kind_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
uint8_t v_kind_boxed_3851_; lean_object* v_res_3852_; 
v_kind_boxed_3851_ = lean_unbox(v_kind_3845_);
v_res_3852_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3843_, v_k_3844_, v_kind_boxed_3851_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
return v_res_3852_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3855_ = lean_box(0);
v___x_3856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3857_ = l_Lean_mkConst(v___x_3856_, v___x_3855_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3858_, lean_object* v_v_3859_, lean_object* v___x_3860_, lean_object* v___x_3861_, lean_object* v___x_3862_, lean_object* v_motive_3863_, uint8_t v___x_3864_, uint8_t v___x_3865_, uint8_t v___x_3866_, lean_object* v_zs12_3867_, lean_object* v_is_3868_, lean_object* v_fields1_3869_, lean_object* v_fields2_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v_e_3886_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
lean_inc_ref(v___x_3862_);
v___x_3896_ = l_Lean_mkAppN(v___x_3862_, v_fields1_3869_);
v___x_3897_ = l_Lean_mkAppN(v___x_3862_, v_fields2_3870_);
lean_inc(v___x_3860_);
v___x_3898_ = l_Lean_mkNatLit(v___x_3860_);
v___x_3899_ = l_Lean_Meta_mkEqRefl(v___x_3898_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref_known(v___x_3899_, 1);
v___x_3901_ = lean_unsigned_to_nat(3u);
v___x_3902_ = lean_mk_empty_array_with_capacity(v___x_3901_);
v___x_3903_ = lean_array_push(v___x_3902_, v___x_3896_);
v___x_3904_ = lean_array_push(v___x_3903_, v___x_3897_);
v___x_3905_ = lean_array_push(v___x_3904_, v_a_3900_);
v___x_3906_ = l_Array_append___redArg(v_is_3868_, v___x_3905_);
lean_dec_ref(v___x_3905_);
v___x_3907_ = l_Lean_mkAppN(v_motive_3863_, v___x_3906_);
lean_dec_ref(v___x_3906_);
v___x_3908_ = l_Lean_Meta_mkForallFVars(v_zs12_3867_, v___x_3907_, v___x_3864_, v___x_3865_, v___x_3865_, v___x_3866_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; uint8_t v___x_3911_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = lean_array_get_size(v_zs12_3867_);
v___x_3911_ = lean_nat_dec_eq(v___x_3910_, v___x_3858_);
if (v___x_3911_ == 0)
{
v_e_3886_ = v_a_3909_;
goto v___jp_3885_;
}
else
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3913_ = l_Lean_mkArrow(v___x_3912_, v_a_3909_, v___y_3873_, v___y_3874_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v_e_3886_ = v_a_3914_;
goto v___jp_3885_;
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec(v___x_3860_);
lean_dec(v_v_3859_);
lean_dec(v___x_3858_);
v_a_3915_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3913_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3913_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v___x_3860_);
lean_dec(v_v_3859_);
lean_dec(v___x_3858_);
v_a_3923_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3908_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3908_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec_ref(v___x_3897_);
lean_dec_ref(v___x_3896_);
lean_dec_ref(v_is_3868_);
lean_dec_ref(v_motive_3863_);
lean_dec(v___x_3860_);
lean_dec(v_v_3859_);
lean_dec(v___x_3858_);
v_a_3931_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3899_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3899_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
v___jp_3876_:
{
lean_object* v___x_3879_; uint8_t v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3879_ = lean_array_get_size(v_zs12_3867_);
v___x_3880_ = lean_nat_dec_eq(v___x_3879_, v___x_3858_);
v___x_3881_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
lean_ctor_set(v___x_3881_, 1, v___x_3858_);
lean_ctor_set_uint8(v___x_3881_, sizeof(void*)*2, v___x_3880_);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___y_3878_);
lean_ctor_set(v___x_3882_, 1, v___y_3877_);
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
lean_ctor_set(v___x_3883_, 1, v___x_3881_);
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
return v___x_3884_;
}
v___jp_3885_:
{
if (lean_obj_tag(v_v_3859_) == 1)
{
lean_object* v_str_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; 
lean_dec(v___x_3860_);
v_str_3887_ = lean_ctor_get(v_v_3859_, 1);
lean_inc_ref(v_str_3887_);
lean_dec_ref_known(v_v_3859_, 2);
v___x_3888_ = lean_box(0);
v___x_3889_ = l_Lean_Name_str___override(v___x_3888_, v_str_3887_);
v___y_3877_ = v_e_3886_;
v___y_3878_ = v___x_3889_;
goto v___jp_3876_;
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_dec(v_v_3859_);
v___x_3890_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3891_ = lean_nat_add(v___x_3860_, v___x_3861_);
lean_dec(v___x_3860_);
v___x_3892_ = l_Nat_reprFast(v___x_3891_);
v___x_3893_ = lean_string_append(v___x_3890_, v___x_3892_);
lean_dec_ref(v___x_3892_);
v___x_3894_ = lean_box(0);
v___x_3895_ = l_Lean_Name_str___override(v___x_3894_, v___x_3893_);
v___y_3877_ = v_e_3886_;
v___y_3878_ = v___x_3895_;
goto v___jp_3876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3939_ = _args[0];
lean_object* v_v_3940_ = _args[1];
lean_object* v___x_3941_ = _args[2];
lean_object* v___x_3942_ = _args[3];
lean_object* v___x_3943_ = _args[4];
lean_object* v_motive_3944_ = _args[5];
lean_object* v___x_3945_ = _args[6];
lean_object* v___x_3946_ = _args[7];
lean_object* v___x_3947_ = _args[8];
lean_object* v_zs12_3948_ = _args[9];
lean_object* v_is_3949_ = _args[10];
lean_object* v_fields1_3950_ = _args[11];
lean_object* v_fields2_3951_ = _args[12];
lean_object* v___y_3952_ = _args[13];
lean_object* v___y_3953_ = _args[14];
lean_object* v___y_3954_ = _args[15];
lean_object* v___y_3955_ = _args[16];
lean_object* v___y_3956_ = _args[17];
_start:
{
uint8_t v___x_16252__boxed_3957_; uint8_t v___x_16253__boxed_3958_; uint8_t v___x_16254__boxed_3959_; lean_object* v_res_3960_; 
v___x_16252__boxed_3957_ = lean_unbox(v___x_3945_);
v___x_16253__boxed_3958_ = lean_unbox(v___x_3946_);
v___x_16254__boxed_3959_ = lean_unbox(v___x_3947_);
v_res_3960_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3939_, v_v_3940_, v___x_3941_, v___x_3942_, v___x_3943_, v_motive_3944_, v___x_16252__boxed_3957_, v___x_16253__boxed_3958_, v___x_16254__boxed_3959_, v_zs12_3948_, v_is_3949_, v_fields1_3950_, v_fields2_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec_ref(v_fields2_3951_);
lean_dec_ref(v_fields1_3950_);
lean_dec_ref(v_zs12_3948_);
lean_dec(v___x_3942_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3961_, lean_object* v_params_3962_, lean_object* v_motive_3963_, size_t v_sz_3964_, size_t v_i_3965_, lean_object* v_bs_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
uint8_t v___x_3972_; 
v___x_3972_ = lean_usize_dec_lt(v_i_3965_, v_sz_3964_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; 
lean_dec_ref(v_motive_3963_);
lean_dec(v_tail_3961_);
v___x_3973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3973_, 0, v_bs_3966_);
return v___x_3973_;
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; uint8_t v___x_3976_; uint8_t v___x_3977_; lean_object* v_v_3978_; lean_object* v_bs_x27_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___f_3986_; lean_object* v___x_3987_; 
v___x_3974_ = lean_unsigned_to_nat(0u);
v___x_3975_ = lean_unsigned_to_nat(1u);
v___x_3976_ = 0;
v___x_3977_ = 1;
v_v_3978_ = lean_array_uget(v_bs_3966_, v_i_3965_);
v_bs_x27_3979_ = lean_array_uset(v_bs_3966_, v_i_3965_, v___x_3974_);
v___x_3980_ = lean_usize_to_nat(v_i_3965_);
lean_inc(v_tail_3961_);
lean_inc(v_v_3978_);
v___x_3981_ = l_Lean_mkConst(v_v_3978_, v_tail_3961_);
v___x_3982_ = l_Lean_mkAppN(v___x_3981_, v_params_3962_);
v___x_3983_ = lean_box(v___x_3976_);
v___x_3984_ = lean_box(v___x_3972_);
v___x_3985_ = lean_box(v___x_3977_);
lean_inc_ref(v_motive_3963_);
lean_inc_ref(v___x_3982_);
v___f_3986_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3986_, 0, v___x_3974_);
lean_closure_set(v___f_3986_, 1, v_v_3978_);
lean_closure_set(v___f_3986_, 2, v___x_3980_);
lean_closure_set(v___f_3986_, 3, v___x_3975_);
lean_closure_set(v___f_3986_, 4, v___x_3982_);
lean_closure_set(v___f_3986_, 5, v_motive_3963_);
lean_closure_set(v___f_3986_, 6, v___x_3983_);
lean_closure_set(v___f_3986_, 7, v___x_3984_);
lean_closure_set(v___f_3986_, 8, v___x_3985_);
v___x_3987_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3982_, v___f_3986_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v_a_3988_; size_t v___x_3989_; size_t v___x_3990_; lean_object* v___x_3991_; 
v_a_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_a_3988_);
lean_dec_ref_known(v___x_3987_, 1);
v___x_3989_ = ((size_t)1ULL);
v___x_3990_ = lean_usize_add(v_i_3965_, v___x_3989_);
v___x_3991_ = lean_array_uset(v_bs_x27_3979_, v_i_3965_, v_a_3988_);
v_i_3965_ = v___x_3990_;
v_bs_3966_ = v___x_3991_;
goto _start;
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_dec_ref(v_bs_x27_3979_);
lean_dec_ref(v_motive_3963_);
lean_dec(v_tail_3961_);
v_a_3993_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3987_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3987_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_4001_, lean_object* v_params_4002_, lean_object* v_motive_4003_, lean_object* v_sz_4004_, lean_object* v_i_4005_, lean_object* v_bs_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
size_t v_sz_boxed_4012_; size_t v_i_boxed_4013_; lean_object* v_res_4014_; 
v_sz_boxed_4012_ = lean_unbox_usize(v_sz_4004_);
lean_dec(v_sz_4004_);
v_i_boxed_4013_ = lean_unbox_usize(v_i_4005_);
lean_dec(v_i_4005_);
v_res_4014_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4001_, v_params_4002_, v_motive_4003_, v_sz_boxed_4012_, v_i_boxed_4013_, v_bs_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec_ref(v_params_4002_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_4017_, lean_object* v_tail_4018_, lean_object* v_params_4019_, lean_object* v_numIndices_4020_, lean_object* v___x_4021_, lean_object* v___x_4022_, uint8_t v___x_4023_, uint8_t v___x_4024_, uint8_t v___x_4025_, lean_object* v_is_4026_, lean_object* v___x_4027_, lean_object* v___x_4028_, lean_object* v___x_4029_, lean_object* v___x_4030_, lean_object* v___x_4031_, lean_object* v___x_4032_, lean_object* v_heq_4033_, lean_object* v_val_4034_, lean_object* v___x_4035_, lean_object* v_declName_4036_, lean_object* v_levelParams_4037_, lean_object* v___x_4038_, lean_object* v___x_4039_, lean_object* v_numParams_4040_, lean_object* v___x_4041_, lean_object* v_motive_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v___x_4048_; size_t v_sz_4049_; size_t v___x_4050_; lean_object* v___x_4051_; 
v___x_4048_ = lean_array_mk(v_ctors_4017_);
v_sz_4049_ = lean_array_size(v___x_4048_);
v___x_4050_ = ((size_t)0ULL);
lean_inc_ref(v___x_4048_);
lean_inc_ref(v_motive_4042_);
lean_inc(v_tail_4018_);
v___x_4051_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4018_, v_params_4019_, v_motive_4042_, v_sz_4049_, v___x_4050_, v___x_4048_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4053_; lean_object* v_fst_4054_; lean_object* v_snd_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___f_4061_; uint8_t v___x_4062_; lean_object* v___x_4063_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc(v_a_4052_);
lean_dec_ref_known(v___x_4051_, 1);
v___x_4053_ = l_Array_unzip___redArg(v_a_4052_);
lean_dec(v_a_4052_);
v_fst_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_fst_4054_);
v_snd_4055_ = lean_ctor_get(v___x_4053_, 1);
lean_inc(v_snd_4055_);
lean_dec_ref(v___x_4053_);
v___x_4056_ = lean_box(v___x_4023_);
v___x_4057_ = lean_box(v___x_4024_);
v___x_4058_ = lean_box(v___x_4025_);
v___x_4059_ = lean_box_usize(v_sz_4049_);
v___x_4060_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4061_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4061_, 0, v_numIndices_4020_);
lean_closure_set(v___f_4061_, 1, v___x_4021_);
lean_closure_set(v___f_4061_, 2, v_motive_4042_);
lean_closure_set(v___f_4061_, 3, v___x_4022_);
lean_closure_set(v___f_4061_, 4, v___x_4056_);
lean_closure_set(v___f_4061_, 5, v___x_4057_);
lean_closure_set(v___f_4061_, 6, v___x_4058_);
lean_closure_set(v___f_4061_, 7, v_is_4026_);
lean_closure_set(v___f_4061_, 8, v___x_4027_);
lean_closure_set(v___f_4061_, 9, v___x_4028_);
lean_closure_set(v___f_4061_, 10, v___x_4029_);
lean_closure_set(v___f_4061_, 11, v___x_4030_);
lean_closure_set(v___f_4061_, 12, v_params_4019_);
lean_closure_set(v___f_4061_, 13, v___x_4031_);
lean_closure_set(v___f_4061_, 14, v___x_4032_);
lean_closure_set(v___f_4061_, 15, v_heq_4033_);
lean_closure_set(v___f_4061_, 16, v_val_4034_);
lean_closure_set(v___f_4061_, 17, v_tail_4018_);
lean_closure_set(v___f_4061_, 18, v___x_4059_);
lean_closure_set(v___f_4061_, 19, v___x_4060_);
lean_closure_set(v___f_4061_, 20, v___x_4048_);
lean_closure_set(v___f_4061_, 21, v___x_4035_);
lean_closure_set(v___f_4061_, 22, v_declName_4036_);
lean_closure_set(v___f_4061_, 23, v_levelParams_4037_);
lean_closure_set(v___f_4061_, 24, v___x_4038_);
lean_closure_set(v___f_4061_, 25, v___x_4039_);
lean_closure_set(v___f_4061_, 26, v_numParams_4040_);
lean_closure_set(v___f_4061_, 27, v_snd_4055_);
lean_closure_set(v___f_4061_, 28, v___x_4041_);
v___x_4062_ = 0;
v___x_4063_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_4054_, v___f_4061_, v___x_4062_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
return v___x_4063_;
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
lean_dec_ref(v___x_4048_);
lean_dec_ref(v_motive_4042_);
lean_dec_ref(v___x_4041_);
lean_dec(v_numParams_4040_);
lean_dec(v___x_4039_);
lean_dec(v___x_4038_);
lean_dec(v_levelParams_4037_);
lean_dec(v_declName_4036_);
lean_dec_ref(v___x_4035_);
lean_dec_ref(v_val_4034_);
lean_dec_ref(v_heq_4033_);
lean_dec_ref(v___x_4032_);
lean_dec_ref(v___x_4031_);
lean_dec(v___x_4030_);
lean_dec(v___x_4029_);
lean_dec_ref(v___x_4028_);
lean_dec_ref(v___x_4027_);
lean_dec_ref(v_is_4026_);
lean_dec_ref(v___x_4022_);
lean_dec(v___x_4021_);
lean_dec(v_numIndices_4020_);
lean_dec_ref(v_params_4019_);
lean_dec(v_tail_4018_);
v_a_4064_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4051_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4051_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4072_ = _args[0];
lean_object* v_tail_4073_ = _args[1];
lean_object* v_params_4074_ = _args[2];
lean_object* v_numIndices_4075_ = _args[3];
lean_object* v___x_4076_ = _args[4];
lean_object* v___x_4077_ = _args[5];
lean_object* v___x_4078_ = _args[6];
lean_object* v___x_4079_ = _args[7];
lean_object* v___x_4080_ = _args[8];
lean_object* v_is_4081_ = _args[9];
lean_object* v___x_4082_ = _args[10];
lean_object* v___x_4083_ = _args[11];
lean_object* v___x_4084_ = _args[12];
lean_object* v___x_4085_ = _args[13];
lean_object* v___x_4086_ = _args[14];
lean_object* v___x_4087_ = _args[15];
lean_object* v_heq_4088_ = _args[16];
lean_object* v_val_4089_ = _args[17];
lean_object* v___x_4090_ = _args[18];
lean_object* v_declName_4091_ = _args[19];
lean_object* v_levelParams_4092_ = _args[20];
lean_object* v___x_4093_ = _args[21];
lean_object* v___x_4094_ = _args[22];
lean_object* v_numParams_4095_ = _args[23];
lean_object* v___x_4096_ = _args[24];
lean_object* v_motive_4097_ = _args[25];
lean_object* v___y_4098_ = _args[26];
lean_object* v___y_4099_ = _args[27];
lean_object* v___y_4100_ = _args[28];
lean_object* v___y_4101_ = _args[29];
lean_object* v___y_4102_ = _args[30];
_start:
{
uint8_t v___x_16489__boxed_4103_; uint8_t v___x_16490__boxed_4104_; uint8_t v___x_16491__boxed_4105_; lean_object* v_res_4106_; 
v___x_16489__boxed_4103_ = lean_unbox(v___x_4078_);
v___x_16490__boxed_4104_ = lean_unbox(v___x_4079_);
v___x_16491__boxed_4105_ = lean_unbox(v___x_4080_);
v_res_4106_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4072_, v_tail_4073_, v_params_4074_, v_numIndices_4075_, v___x_4076_, v___x_4077_, v___x_16489__boxed_4103_, v___x_16490__boxed_4104_, v___x_16491__boxed_4105_, v_is_4081_, v___x_4082_, v___x_4083_, v___x_4084_, v___x_4085_, v___x_4086_, v___x_4087_, v_heq_4088_, v_val_4089_, v___x_4090_, v_declName_4091_, v_levelParams_4092_, v___x_4093_, v___x_4094_, v_numParams_4095_, v___x_4096_, v_motive_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4107_, lean_object* v___x_4108_, lean_object* v_is_4109_, lean_object* v_head_4110_, lean_object* v_ctors_4111_, lean_object* v_tail_4112_, lean_object* v_params_4113_, lean_object* v_numIndices_4114_, lean_object* v___x_4115_, lean_object* v___x_4116_, lean_object* v___x_4117_, lean_object* v___x_4118_, lean_object* v___x_4119_, lean_object* v_val_4120_, lean_object* v___x_4121_, lean_object* v_declName_4122_, lean_object* v_levelParams_4123_, lean_object* v___x_4124_, lean_object* v_numParams_4125_, lean_object* v___x_4126_, lean_object* v_heq_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; uint8_t v___x_4141_; uint8_t v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___f_4146_; lean_object* v___x_4147_; 
v___x_4133_ = lean_unsigned_to_nat(3u);
v___x_4134_ = lean_mk_empty_array_with_capacity(v___x_4133_);
lean_inc_ref(v___x_4107_);
v___x_4135_ = lean_array_push(v___x_4134_, v___x_4107_);
lean_inc_ref(v___x_4108_);
v___x_4136_ = lean_array_push(v___x_4135_, v___x_4108_);
lean_inc_ref(v_heq_4127_);
v___x_4137_ = lean_array_push(v___x_4136_, v_heq_4127_);
lean_inc_ref(v_is_4109_);
v___x_4138_ = l_Array_append___redArg(v_is_4109_, v___x_4137_);
lean_dec_ref(v___x_4137_);
v___x_4139_ = l_Lean_mkSort(v_head_4110_);
v___x_4140_ = 0;
v___x_4141_ = 1;
v___x_4142_ = 1;
v___x_4143_ = lean_box(v___x_4140_);
v___x_4144_ = lean_box(v___x_4141_);
v___x_4145_ = lean_box(v___x_4142_);
lean_inc_ref(v___x_4138_);
v___f_4146_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4146_, 0, v_ctors_4111_);
lean_closure_set(v___f_4146_, 1, v_tail_4112_);
lean_closure_set(v___f_4146_, 2, v_params_4113_);
lean_closure_set(v___f_4146_, 3, v_numIndices_4114_);
lean_closure_set(v___f_4146_, 4, v___x_4115_);
lean_closure_set(v___f_4146_, 5, v___x_4138_);
lean_closure_set(v___f_4146_, 6, v___x_4143_);
lean_closure_set(v___f_4146_, 7, v___x_4144_);
lean_closure_set(v___f_4146_, 8, v___x_4145_);
lean_closure_set(v___f_4146_, 9, v_is_4109_);
lean_closure_set(v___f_4146_, 10, v___x_4108_);
lean_closure_set(v___f_4146_, 11, v___x_4107_);
lean_closure_set(v___f_4146_, 12, v___x_4116_);
lean_closure_set(v___f_4146_, 13, v___x_4117_);
lean_closure_set(v___f_4146_, 14, v___x_4118_);
lean_closure_set(v___f_4146_, 15, v___x_4119_);
lean_closure_set(v___f_4146_, 16, v_heq_4127_);
lean_closure_set(v___f_4146_, 17, v_val_4120_);
lean_closure_set(v___f_4146_, 18, v___x_4121_);
lean_closure_set(v___f_4146_, 19, v_declName_4122_);
lean_closure_set(v___f_4146_, 20, v_levelParams_4123_);
lean_closure_set(v___f_4146_, 21, v___x_4133_);
lean_closure_set(v___f_4146_, 22, v___x_4124_);
lean_closure_set(v___f_4146_, 23, v_numParams_4125_);
lean_closure_set(v___f_4146_, 24, v___x_4126_);
v___x_4147_ = l_Lean_Meta_mkForallFVars(v___x_4138_, v___x_4139_, v___x_4140_, v___x_4141_, v___x_4141_, v___x_4142_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec_ref(v___x_4138_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v___x_4149_; uint8_t v___x_4150_; lean_object* v___x_4151_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4147_, 1);
v___x_4149_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4150_ = 0;
v___x_4151_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4149_, v___x_4142_, v_a_4148_, v___f_4146_, v___x_4150_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
return v___x_4151_;
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
lean_dec_ref(v___f_4146_);
v_a_4152_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4147_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4147_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4160_ = _args[0];
lean_object* v___x_4161_ = _args[1];
lean_object* v_is_4162_ = _args[2];
lean_object* v_head_4163_ = _args[3];
lean_object* v_ctors_4164_ = _args[4];
lean_object* v_tail_4165_ = _args[5];
lean_object* v_params_4166_ = _args[6];
lean_object* v_numIndices_4167_ = _args[7];
lean_object* v___x_4168_ = _args[8];
lean_object* v___x_4169_ = _args[9];
lean_object* v___x_4170_ = _args[10];
lean_object* v___x_4171_ = _args[11];
lean_object* v___x_4172_ = _args[12];
lean_object* v_val_4173_ = _args[13];
lean_object* v___x_4174_ = _args[14];
lean_object* v_declName_4175_ = _args[15];
lean_object* v_levelParams_4176_ = _args[16];
lean_object* v___x_4177_ = _args[17];
lean_object* v_numParams_4178_ = _args[18];
lean_object* v___x_4179_ = _args[19];
lean_object* v_heq_4180_ = _args[20];
lean_object* v___y_4181_ = _args[21];
lean_object* v___y_4182_ = _args[22];
lean_object* v___y_4183_ = _args[23];
lean_object* v___y_4184_ = _args[24];
lean_object* v___y_4185_ = _args[25];
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4160_, v___x_4161_, v_is_4162_, v_head_4163_, v_ctors_4164_, v_tail_4165_, v_params_4166_, v_numIndices_4167_, v___x_4168_, v___x_4169_, v___x_4170_, v___x_4171_, v___x_4172_, v_val_4173_, v___x_4174_, v_declName_4175_, v_levelParams_4176_, v___x_4177_, v_numParams_4178_, v___x_4179_, v_heq_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4187_, lean_object* v_x1_4188_, lean_object* v_indName_4189_, lean_object* v_tail_4190_, lean_object* v_params_4191_, lean_object* v_is_4192_, lean_object* v___x_4193_, lean_object* v_head_4194_, lean_object* v_ctors_4195_, lean_object* v_numIndices_4196_, lean_object* v___x_4197_, lean_object* v___x_4198_, lean_object* v_val_4199_, lean_object* v_declName_4200_, lean_object* v_levelParams_4201_, lean_object* v_numParams_4202_, lean_object* v___x_4203_, lean_object* v_x2_4204_, lean_object* v_x_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___f_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4212_ = lean_array_get_borrowed(v___x_4187_, v_x1_4188_, v___x_4211_);
v___x_4213_ = lean_array_get_borrowed(v___x_4187_, v_x2_4204_, v___x_4211_);
v___x_4214_ = l_Lean_mkCtorIdxName(v_indName_4189_);
lean_inc(v_tail_4190_);
v___x_4215_ = l_Lean_mkConst(v___x_4214_, v_tail_4190_);
lean_inc_ref(v_params_4191_);
v___x_4216_ = l_Array_append___redArg(v_params_4191_, v_is_4192_);
v___x_4217_ = lean_mk_empty_array_with_capacity(v___x_4193_);
lean_inc_n(v___x_4212_, 2);
lean_inc_ref_n(v___x_4217_, 2);
v___x_4218_ = lean_array_push(v___x_4217_, v___x_4212_);
lean_inc_ref(v___x_4216_);
v___x_4219_ = l_Array_append___redArg(v___x_4216_, v___x_4218_);
lean_inc_ref(v___x_4215_);
v___x_4220_ = l_Lean_mkAppN(v___x_4215_, v___x_4219_);
lean_dec_ref(v___x_4219_);
lean_inc_n(v___x_4213_, 2);
v___x_4221_ = lean_array_push(v___x_4217_, v___x_4213_);
lean_inc_ref(v___x_4221_);
v___f_4222_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4222_, 0, v___x_4212_);
lean_closure_set(v___f_4222_, 1, v___x_4213_);
lean_closure_set(v___f_4222_, 2, v_is_4192_);
lean_closure_set(v___f_4222_, 3, v_head_4194_);
lean_closure_set(v___f_4222_, 4, v_ctors_4195_);
lean_closure_set(v___f_4222_, 5, v_tail_4190_);
lean_closure_set(v___f_4222_, 6, v_params_4191_);
lean_closure_set(v___f_4222_, 7, v_numIndices_4196_);
lean_closure_set(v___f_4222_, 8, v___x_4193_);
lean_closure_set(v___f_4222_, 9, v___x_4197_);
lean_closure_set(v___f_4222_, 10, v___x_4198_);
lean_closure_set(v___f_4222_, 11, v___x_4218_);
lean_closure_set(v___f_4222_, 12, v___x_4221_);
lean_closure_set(v___f_4222_, 13, v_val_4199_);
lean_closure_set(v___f_4222_, 14, v___x_4217_);
lean_closure_set(v___f_4222_, 15, v_declName_4200_);
lean_closure_set(v___f_4222_, 16, v_levelParams_4201_);
lean_closure_set(v___f_4222_, 17, v___x_4211_);
lean_closure_set(v___f_4222_, 18, v_numParams_4202_);
lean_closure_set(v___f_4222_, 19, v___x_4203_);
v___x_4223_ = l_Array_append___redArg(v___x_4216_, v___x_4221_);
lean_dec_ref(v___x_4221_);
v___x_4224_ = l_Lean_mkAppN(v___x_4215_, v___x_4223_);
lean_dec_ref(v___x_4223_);
v___x_4225_ = l_Lean_Meta_mkEq(v___x_4220_, v___x_4224_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v___x_4227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4228_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4227_, v_a_4226_, v___f_4222_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4228_;
}
else
{
lean_object* v_a_4229_; lean_object* v___x_4231_; uint8_t v_isShared_4232_; uint8_t v_isSharedCheck_4236_; 
lean_dec_ref(v___f_4222_);
v_a_4229_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4231_ = v___x_4225_;
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
else
{
lean_inc(v_a_4229_);
lean_dec(v___x_4225_);
v___x_4231_ = lean_box(0);
v_isShared_4232_ = v_isSharedCheck_4236_;
goto v_resetjp_4230_;
}
v_resetjp_4230_:
{
lean_object* v___x_4234_; 
if (v_isShared_4232_ == 0)
{
v___x_4234_ = v___x_4231_;
goto v_reusejp_4233_;
}
else
{
lean_object* v_reuseFailAlloc_4235_; 
v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
v___x_4234_ = v_reuseFailAlloc_4235_;
goto v_reusejp_4233_;
}
v_reusejp_4233_:
{
return v___x_4234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4237_ = _args[0];
lean_object* v_x1_4238_ = _args[1];
lean_object* v_indName_4239_ = _args[2];
lean_object* v_tail_4240_ = _args[3];
lean_object* v_params_4241_ = _args[4];
lean_object* v_is_4242_ = _args[5];
lean_object* v___x_4243_ = _args[6];
lean_object* v_head_4244_ = _args[7];
lean_object* v_ctors_4245_ = _args[8];
lean_object* v_numIndices_4246_ = _args[9];
lean_object* v___x_4247_ = _args[10];
lean_object* v___x_4248_ = _args[11];
lean_object* v_val_4249_ = _args[12];
lean_object* v_declName_4250_ = _args[13];
lean_object* v_levelParams_4251_ = _args[14];
lean_object* v_numParams_4252_ = _args[15];
lean_object* v___x_4253_ = _args[16];
lean_object* v_x2_4254_ = _args[17];
lean_object* v_x_4255_ = _args[18];
lean_object* v___y_4256_ = _args[19];
lean_object* v___y_4257_ = _args[20];
lean_object* v___y_4258_ = _args[21];
lean_object* v___y_4259_ = _args[22];
lean_object* v___y_4260_ = _args[23];
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4237_, v_x1_4238_, v_indName_4239_, v_tail_4240_, v_params_4241_, v_is_4242_, v___x_4243_, v_head_4244_, v_ctors_4245_, v_numIndices_4246_, v___x_4247_, v___x_4248_, v_val_4249_, v_declName_4250_, v_levelParams_4251_, v_numParams_4252_, v___x_4253_, v_x2_4254_, v_x_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec_ref(v_x_4255_);
lean_dec_ref(v_x2_4254_);
lean_dec_ref(v_x1_4238_);
lean_dec_ref(v___x_4237_);
return v_res_4261_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4262_, lean_object* v_indName_4263_, lean_object* v_tail_4264_, lean_object* v_params_4265_, lean_object* v_is_4266_, lean_object* v___x_4267_, lean_object* v_head_4268_, lean_object* v_ctors_4269_, lean_object* v_numIndices_4270_, lean_object* v___x_4271_, lean_object* v___x_4272_, lean_object* v_val_4273_, lean_object* v_declName_4274_, lean_object* v_levelParams_4275_, lean_object* v_numParams_4276_, lean_object* v___x_4277_, lean_object* v_t_4278_, lean_object* v___x_4279_, lean_object* v_x1_4280_, lean_object* v_x_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___f_4287_; uint8_t v___x_4288_; lean_object* v___x_4289_; 
v___f_4287_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4287_, 0, v___x_4262_);
lean_closure_set(v___f_4287_, 1, v_x1_4280_);
lean_closure_set(v___f_4287_, 2, v_indName_4263_);
lean_closure_set(v___f_4287_, 3, v_tail_4264_);
lean_closure_set(v___f_4287_, 4, v_params_4265_);
lean_closure_set(v___f_4287_, 5, v_is_4266_);
lean_closure_set(v___f_4287_, 6, v___x_4267_);
lean_closure_set(v___f_4287_, 7, v_head_4268_);
lean_closure_set(v___f_4287_, 8, v_ctors_4269_);
lean_closure_set(v___f_4287_, 9, v_numIndices_4270_);
lean_closure_set(v___f_4287_, 10, v___x_4271_);
lean_closure_set(v___f_4287_, 11, v___x_4272_);
lean_closure_set(v___f_4287_, 12, v_val_4273_);
lean_closure_set(v___f_4287_, 13, v_declName_4274_);
lean_closure_set(v___f_4287_, 14, v_levelParams_4275_);
lean_closure_set(v___f_4287_, 15, v_numParams_4276_);
lean_closure_set(v___f_4287_, 16, v___x_4277_);
v___x_4288_ = 0;
v___x_4289_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4278_, v___x_4279_, v___f_4287_, v___x_4288_, v___x_4288_, v___y_4282_, v___y_4283_, v___y_4284_, v___y_4285_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4290_ = _args[0];
lean_object* v_indName_4291_ = _args[1];
lean_object* v_tail_4292_ = _args[2];
lean_object* v_params_4293_ = _args[3];
lean_object* v_is_4294_ = _args[4];
lean_object* v___x_4295_ = _args[5];
lean_object* v_head_4296_ = _args[6];
lean_object* v_ctors_4297_ = _args[7];
lean_object* v_numIndices_4298_ = _args[8];
lean_object* v___x_4299_ = _args[9];
lean_object* v___x_4300_ = _args[10];
lean_object* v_val_4301_ = _args[11];
lean_object* v_declName_4302_ = _args[12];
lean_object* v_levelParams_4303_ = _args[13];
lean_object* v_numParams_4304_ = _args[14];
lean_object* v___x_4305_ = _args[15];
lean_object* v_t_4306_ = _args[16];
lean_object* v___x_4307_ = _args[17];
lean_object* v_x1_4308_ = _args[18];
lean_object* v_x_4309_ = _args[19];
lean_object* v___y_4310_ = _args[20];
lean_object* v___y_4311_ = _args[21];
lean_object* v___y_4312_ = _args[22];
lean_object* v___y_4313_ = _args[23];
lean_object* v___y_4314_ = _args[24];
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4290_, v_indName_4291_, v_tail_4292_, v_params_4293_, v_is_4294_, v___x_4295_, v_head_4296_, v_ctors_4297_, v_numIndices_4298_, v___x_4299_, v___x_4300_, v_val_4301_, v_declName_4302_, v_levelParams_4303_, v_numParams_4304_, v___x_4305_, v_t_4306_, v___x_4307_, v_x1_4308_, v_x_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec_ref(v_x_4309_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4316_, lean_object* v_indName_4317_, lean_object* v_tail_4318_, lean_object* v_params_4319_, lean_object* v_head_4320_, lean_object* v_ctors_4321_, lean_object* v_numIndices_4322_, lean_object* v___x_4323_, lean_object* v___x_4324_, lean_object* v_val_4325_, lean_object* v_declName_4326_, lean_object* v_levelParams_4327_, lean_object* v_numParams_4328_, lean_object* v___x_4329_, lean_object* v_is_4330_, lean_object* v_t_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___f_4339_; uint8_t v___x_4340_; lean_object* v___x_4341_; 
v___x_4337_ = lean_unsigned_to_nat(1u);
v___x_4338_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4331_);
v___f_4339_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4339_, 0, v___x_4316_);
lean_closure_set(v___f_4339_, 1, v_indName_4317_);
lean_closure_set(v___f_4339_, 2, v_tail_4318_);
lean_closure_set(v___f_4339_, 3, v_params_4319_);
lean_closure_set(v___f_4339_, 4, v_is_4330_);
lean_closure_set(v___f_4339_, 5, v___x_4337_);
lean_closure_set(v___f_4339_, 6, v_head_4320_);
lean_closure_set(v___f_4339_, 7, v_ctors_4321_);
lean_closure_set(v___f_4339_, 8, v_numIndices_4322_);
lean_closure_set(v___f_4339_, 9, v___x_4323_);
lean_closure_set(v___f_4339_, 10, v___x_4324_);
lean_closure_set(v___f_4339_, 11, v_val_4325_);
lean_closure_set(v___f_4339_, 12, v_declName_4326_);
lean_closure_set(v___f_4339_, 13, v_levelParams_4327_);
lean_closure_set(v___f_4339_, 14, v_numParams_4328_);
lean_closure_set(v___f_4339_, 15, v___x_4329_);
lean_closure_set(v___f_4339_, 16, v_t_4331_);
lean_closure_set(v___f_4339_, 17, v___x_4338_);
v___x_4340_ = 0;
v___x_4341_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4331_, v___x_4338_, v___f_4339_, v___x_4340_, v___x_4340_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4342_ = _args[0];
lean_object* v_indName_4343_ = _args[1];
lean_object* v_tail_4344_ = _args[2];
lean_object* v_params_4345_ = _args[3];
lean_object* v_head_4346_ = _args[4];
lean_object* v_ctors_4347_ = _args[5];
lean_object* v_numIndices_4348_ = _args[6];
lean_object* v___x_4349_ = _args[7];
lean_object* v___x_4350_ = _args[8];
lean_object* v_val_4351_ = _args[9];
lean_object* v_declName_4352_ = _args[10];
lean_object* v_levelParams_4353_ = _args[11];
lean_object* v_numParams_4354_ = _args[12];
lean_object* v___x_4355_ = _args[13];
lean_object* v_is_4356_ = _args[14];
lean_object* v_t_4357_ = _args[15];
lean_object* v___y_4358_ = _args[16];
lean_object* v___y_4359_ = _args[17];
lean_object* v___y_4360_ = _args[18];
lean_object* v___y_4361_ = _args[19];
lean_object* v___y_4362_ = _args[20];
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4342_, v_indName_4343_, v_tail_4344_, v_params_4345_, v_head_4346_, v_ctors_4347_, v_numIndices_4348_, v___x_4349_, v___x_4350_, v_val_4351_, v_declName_4352_, v_levelParams_4353_, v_numParams_4354_, v___x_4355_, v_is_4356_, v_t_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4364_, lean_object* v_indName_4365_, lean_object* v_tail_4366_, lean_object* v_head_4367_, lean_object* v_ctors_4368_, lean_object* v_numIndices_4369_, lean_object* v___x_4370_, lean_object* v___x_4371_, lean_object* v_val_4372_, lean_object* v_declName_4373_, lean_object* v_levelParams_4374_, lean_object* v_numParams_4375_, lean_object* v_params_4376_, lean_object* v_t_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; lean_object* v___f_4384_; lean_object* v___x_4385_; uint8_t v___x_4386_; lean_object* v___x_4387_; 
v___x_4383_ = l_Lean_Expr_bindingBody_x21(v_t_4377_);
lean_inc_ref(v___x_4383_);
lean_inc(v_numIndices_4369_);
v___f_4384_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4384_, 0, v___x_4364_);
lean_closure_set(v___f_4384_, 1, v_indName_4365_);
lean_closure_set(v___f_4384_, 2, v_tail_4366_);
lean_closure_set(v___f_4384_, 3, v_params_4376_);
lean_closure_set(v___f_4384_, 4, v_head_4367_);
lean_closure_set(v___f_4384_, 5, v_ctors_4368_);
lean_closure_set(v___f_4384_, 6, v_numIndices_4369_);
lean_closure_set(v___f_4384_, 7, v___x_4370_);
lean_closure_set(v___f_4384_, 8, v___x_4371_);
lean_closure_set(v___f_4384_, 9, v_val_4372_);
lean_closure_set(v___f_4384_, 10, v_declName_4373_);
lean_closure_set(v___f_4384_, 11, v_levelParams_4374_);
lean_closure_set(v___f_4384_, 12, v_numParams_4375_);
lean_closure_set(v___f_4384_, 13, v___x_4383_);
v___x_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4385_, 0, v_numIndices_4369_);
v___x_4386_ = 0;
v___x_4387_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4383_, v___x_4385_, v___f_4384_, v___x_4386_, v___x_4386_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_);
return v___x_4387_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4388_ = _args[0];
lean_object* v_indName_4389_ = _args[1];
lean_object* v_tail_4390_ = _args[2];
lean_object* v_head_4391_ = _args[3];
lean_object* v_ctors_4392_ = _args[4];
lean_object* v_numIndices_4393_ = _args[5];
lean_object* v___x_4394_ = _args[6];
lean_object* v___x_4395_ = _args[7];
lean_object* v_val_4396_ = _args[8];
lean_object* v_declName_4397_ = _args[9];
lean_object* v_levelParams_4398_ = _args[10];
lean_object* v_numParams_4399_ = _args[11];
lean_object* v_params_4400_ = _args[12];
lean_object* v_t_4401_ = _args[13];
lean_object* v___y_4402_ = _args[14];
lean_object* v___y_4403_ = _args[15];
lean_object* v___y_4404_ = _args[16];
lean_object* v___y_4405_ = _args[17];
lean_object* v___y_4406_ = _args[18];
_start:
{
lean_object* v_res_4407_; 
v_res_4407_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4388_, v_indName_4389_, v_tail_4390_, v_head_4391_, v_ctors_4392_, v_numIndices_4393_, v___x_4394_, v___x_4395_, v_val_4396_, v_declName_4397_, v_levelParams_4398_, v_numParams_4399_, v_params_4400_, v_t_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_);
lean_dec(v___y_4405_);
lean_dec_ref(v___y_4404_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec_ref(v_t_4401_);
return v_res_4407_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v___x_4412_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4413_ = lean_unsigned_to_nat(58u);
v___x_4414_ = lean_unsigned_to_nat(142u);
v___x_4415_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4416_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4417_ = l_mkPanicMessageWithDecl(v___x_4416_, v___x_4415_, v___x_4414_, v___x_4413_, v___x_4412_);
return v___x_4417_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4418_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4419_ = lean_unsigned_to_nat(60u);
v___x_4420_ = lean_unsigned_to_nat(136u);
v___x_4421_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4422_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4423_ = l_mkPanicMessageWithDecl(v___x_4422_, v___x_4421_, v___x_4420_, v___x_4419_, v___x_4418_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4424_, lean_object* v_indName_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4431_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_4425_);
v___x_4432_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4433_);
lean_dec_ref_known(v___x_4432_, 1);
if (lean_obj_tag(v_a_4433_) == 5)
{
lean_object* v_val_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; 
v_val_4434_ = lean_ctor_get(v_a_4433_, 0);
lean_inc_ref(v_val_4434_);
lean_dec_ref_known(v_a_4433_, 1);
v___x_4435_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4424_);
v___x_4436_ = l_Lean_Name_append(v_declName_4424_, v___x_4435_);
lean_inc(v_indName_4425_);
lean_inc(v___x_4436_);
v___x_4437_ = l_Lean_mkCasesOnSameCtorHet(v___x_4436_, v_indName_4425_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4469_; 
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4469_ == 0)
{
lean_object* v_unused_4470_; 
v_unused_4470_ = lean_ctor_get(v___x_4437_, 0);
lean_dec(v_unused_4470_);
v___x_4439_ = v___x_4437_;
v_isShared_4440_ = v_isSharedCheck_4469_;
goto v_resetjp_4438_;
}
else
{
lean_dec(v___x_4437_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4469_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4441_; lean_object* v___x_4442_; 
lean_inc(v_indName_4425_);
v___x_4441_ = l_Lean_mkCasesOnName(v_indName_4425_);
v___x_4442_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4441_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v_levelParams_4444_; lean_object* v_type_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref_known(v___x_4442_, 1);
v_levelParams_4444_ = lean_ctor_get(v_a_4443_, 1);
lean_inc_n(v_levelParams_4444_, 2);
v_type_4445_ = lean_ctor_get(v_a_4443_, 2);
lean_inc_ref(v_type_4445_);
lean_dec(v_a_4443_);
v___x_4446_ = lean_box(0);
v___x_4447_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4444_, v___x_4446_);
if (lean_obj_tag(v___x_4447_) == 1)
{
lean_object* v_head_4448_; lean_object* v_tail_4449_; lean_object* v_numParams_4450_; lean_object* v_numIndices_4451_; lean_object* v_ctors_4452_; lean_object* v___f_4453_; lean_object* v___x_4455_; 
v_head_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_head_4448_);
v_tail_4449_ = lean_ctor_get(v___x_4447_, 1);
lean_inc(v_tail_4449_);
v_numParams_4450_ = lean_ctor_get(v_val_4434_, 1);
lean_inc_n(v_numParams_4450_, 2);
v_numIndices_4451_ = lean_ctor_get(v_val_4434_, 2);
lean_inc(v_numIndices_4451_);
v_ctors_4452_ = lean_ctor_get(v_val_4434_, 4);
lean_inc(v_ctors_4452_);
v___f_4453_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4453_, 0, v___x_4431_);
lean_closure_set(v___f_4453_, 1, v_indName_4425_);
lean_closure_set(v___f_4453_, 2, v_tail_4449_);
lean_closure_set(v___f_4453_, 3, v_head_4448_);
lean_closure_set(v___f_4453_, 4, v_ctors_4452_);
lean_closure_set(v___f_4453_, 5, v_numIndices_4451_);
lean_closure_set(v___f_4453_, 6, v___x_4436_);
lean_closure_set(v___f_4453_, 7, v___x_4447_);
lean_closure_set(v___f_4453_, 8, v_val_4434_);
lean_closure_set(v___f_4453_, 9, v_declName_4424_);
lean_closure_set(v___f_4453_, 10, v_levelParams_4444_);
lean_closure_set(v___f_4453_, 11, v_numParams_4450_);
if (v_isShared_4440_ == 0)
{
lean_ctor_set_tag(v___x_4439_, 1);
lean_ctor_set(v___x_4439_, 0, v_numParams_4450_);
v___x_4455_ = v___x_4439_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_numParams_4450_);
v___x_4455_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
uint8_t v___x_4456_; lean_object* v___x_4457_; 
v___x_4456_ = 0;
v___x_4457_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4445_, v___x_4455_, v___f_4453_, v___x_4456_, v___x_4456_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_);
return v___x_4457_;
}
}
else
{
lean_object* v___x_4459_; lean_object* v___x_4460_; 
lean_dec(v___x_4447_);
lean_dec_ref(v_type_4445_);
lean_dec(v_levelParams_4444_);
lean_del_object(v___x_4439_);
lean_dec(v___x_4436_);
lean_dec_ref(v_val_4434_);
lean_dec(v_indName_4425_);
lean_dec(v_declName_4424_);
v___x_4459_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4460_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4459_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_);
return v___x_4460_;
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_del_object(v___x_4439_);
lean_dec(v___x_4436_);
lean_dec_ref(v_val_4434_);
lean_dec(v_indName_4425_);
lean_dec(v_declName_4424_);
v_a_4461_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4442_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4442_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
}
else
{
lean_dec(v___x_4436_);
lean_dec_ref(v_val_4434_);
lean_dec(v_indName_4425_);
lean_dec(v_declName_4424_);
return v___x_4437_;
}
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_dec(v_a_4433_);
lean_dec(v_indName_4425_);
lean_dec(v_declName_4424_);
v___x_4471_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4472_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4471_, v_a_4426_, v_a_4427_, v_a_4428_, v_a_4429_);
return v___x_4472_;
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec(v_indName_4425_);
lean_dec(v_declName_4424_);
v_a_4473_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4432_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4432_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4481_, lean_object* v_indName_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l_Lean_mkCasesOnSameCtor(v_declName_4481_, v_indName_4482_, v_a_4483_, v_a_4484_, v_a_4485_, v_a_4486_);
lean_dec(v_a_4486_);
lean_dec_ref(v_a_4485_);
lean_dec(v_a_4484_);
lean_dec_ref(v_a_4483_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4489_, lean_object* v_params_4490_, lean_object* v_motive_4491_, lean_object* v_as_4492_, size_t v_sz_4493_, size_t v_i_4494_, lean_object* v_bs_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v___x_4501_; 
v___x_4501_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4489_, v_params_4490_, v_motive_4491_, v_sz_4493_, v_i_4494_, v_bs_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4502_, lean_object* v_params_4503_, lean_object* v_motive_4504_, lean_object* v_as_4505_, lean_object* v_sz_4506_, lean_object* v_i_4507_, lean_object* v_bs_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
size_t v_sz_boxed_4514_; size_t v_i_boxed_4515_; lean_object* v_res_4516_; 
v_sz_boxed_4514_ = lean_unbox_usize(v_sz_4506_);
lean_dec(v_sz_4506_);
v_i_boxed_4515_ = lean_unbox_usize(v_i_4507_);
lean_dec(v_i_4507_);
v_res_4516_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4502_, v_params_4503_, v_motive_4504_, v_as_4505_, v_sz_boxed_4514_, v_i_boxed_4515_, v_bs_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec_ref(v_as_4505_);
lean_dec_ref(v_params_4503_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4517_, lean_object* v_params_4518_, lean_object* v_a_4519_, lean_object* v_snd_4520_, lean_object* v_alts_4521_, lean_object* v_as_4522_, size_t v_sz_4523_, size_t v_i_4524_, lean_object* v_bs_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v___x_4531_; 
v___x_4531_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4517_, v_params_4518_, v_a_4519_, v_snd_4520_, v_alts_4521_, v_sz_4523_, v_i_4524_, v_bs_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4532_, lean_object* v_params_4533_, lean_object* v_a_4534_, lean_object* v_snd_4535_, lean_object* v_alts_4536_, lean_object* v_as_4537_, lean_object* v_sz_4538_, lean_object* v_i_4539_, lean_object* v_bs_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_){
_start:
{
size_t v_sz_boxed_4546_; size_t v_i_boxed_4547_; lean_object* v_res_4548_; 
v_sz_boxed_4546_ = lean_unbox_usize(v_sz_4538_);
lean_dec(v_sz_4538_);
v_i_boxed_4547_ = lean_unbox_usize(v_i_4539_);
lean_dec(v_i_4539_);
v_res_4548_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4532_, v_params_4533_, v_a_4534_, v_snd_4535_, v_alts_4536_, v_as_4537_, v_sz_boxed_4546_, v_i_boxed_4547_, v_bs_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec_ref(v_as_4537_);
lean_dec_ref(v_params_4533_);
return v_res_4548_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* initialize_Lean_Elab_App(uint8_t builtin);
lean_object* initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorElim(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SameCtorUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
}
#ifdef __cplusplus
}
#endif
