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
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(lean_object* v_k_1_, lean_object* v_b_2_, lean_object* v_c_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_){
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
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_b_2_ = stack[1].m_obj;
lean_object* v_c_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(v_k_1_, v_b_2_, v_c_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed(lean_object* v_k_11_, lean_object* v_b_12_, lean_object* v_c_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(v_k_11_, v_b_12_, v_c_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_);
lean_dec(v___y_17_);
lean_dec_ref(v___y_16_);
lean_dec(v___y_15_);
lean_dec_ref(v___y_14_);
return v_res_19_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(lean_object* v_type_20_, lean_object* v_k_21_, uint8_t v_cleanupAnnotations_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_){
_start:
{
lean_object* v___f_28_; uint8_t v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_28_, 0, v_k_21_);
v___x_29_ = 0;
v___x_30_ = lean_box(0);
v___x_31_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_29_, v___x_30_, v_type_20_, v___f_28_, v_cleanupAnnotations_22_, v___x_29_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_39_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_39_ == 0)
{
v___x_34_ = v___x_31_;
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_39_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v___x_37_; 
if (v_isShared_35_ == 0)
{
v___x_37_ = v___x_34_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_a_32_);
v___x_37_ = v_reuseFailAlloc_38_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
return v___x_37_;
}
}
}
else
{
lean_object* v_a_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_47_; 
v_a_40_ = lean_ctor_get(v___x_31_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_47_ == 0)
{
v___x_42_ = v___x_31_;
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_a_40_);
lean_dec(v___x_31_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_47_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v___x_45_; 
if (v_isShared_43_ == 0)
{
v___x_45_ = v___x_42_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_a_40_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_20_ = stack[0].m_obj;
lean_object* v_k_21_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_22_ = stack[2].m_num;
lean_object* v___y_23_ = stack[3].m_obj;
lean_object* v___y_24_ = stack[4].m_obj;
lean_object* v___y_25_ = stack[5].m_obj;
lean_object* v___y_26_ = stack[6].m_obj;
lean_object* v_res_48_;
v_res_48_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_type_20_, v_k_21_, v_cleanupAnnotations_22_, v___y_23_, v___y_24_, v___y_25_, v___y_26_);
stack->m_obj
 = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___boxed(lean_object* v_type_49_, lean_object* v_k_50_, lean_object* v_cleanupAnnotations_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_57_; lean_object* v_res_58_; 
v_cleanupAnnotations_boxed_57_ = lean_unbox(v_cleanupAnnotations_51_);
v_res_58_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_type_49_, v_k_50_, v_cleanupAnnotations_boxed_57_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_58_;
}
}
lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(lean_object* v_00_u03b1_59_, lean_object* v_type_60_, lean_object* v_k_61_, uint8_t v_cleanupAnnotations_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_type_60_, v_k_61_, v_cleanupAnnotations_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_60_ = stack[1].m_obj;
lean_object* v_k_61_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_62_ = stack[3].m_num;
lean_object* v___y_63_ = stack[4].m_obj;
lean_object* v___y_64_ = stack[5].m_obj;
lean_object* v___y_65_ = stack[6].m_obj;
lean_object* v___y_66_ = stack[7].m_obj;
lean_object* v_res_69_;
v_res_69_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(lean_box(0), v_type_60_, v_k_61_, v_cleanupAnnotations_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___boxed(lean_object* v_00_u03b1_70_, lean_object* v_type_71_, lean_object* v_k_72_, lean_object* v_cleanupAnnotations_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_79_; lean_object* v_res_80_; 
v_cleanupAnnotations_boxed_79_ = lean_unbox(v_cleanupAnnotations_73_);
v_res_80_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(v_00_u03b1_70_, v_type_71_, v_k_72_, v_cleanupAnnotations_boxed_79_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_80_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(lean_object* v_k_81_, lean_object* v_b_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; 
lean_inc(v___y_86_);
lean_inc_ref(v___y_85_);
lean_inc(v___y_84_);
lean_inc_ref(v___y_83_);
v___x_88_ = lean_apply_6(v_k_81_, v_b_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, lean_box(0));
return v___x_88_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_81_ = stack[0].m_obj;
lean_object* v_b_82_ = stack[1].m_obj;
lean_object* v___y_83_ = stack[2].m_obj;
lean_object* v___y_84_ = stack[3].m_obj;
lean_object* v___y_85_ = stack[4].m_obj;
lean_object* v___y_86_ = stack[5].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(v_k_81_, v_b_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed(lean_object* v_k_90_, lean_object* v_b_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(v_k_90_, v_b_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
lean_dec(v___y_93_);
lean_dec_ref(v___y_92_);
return v_res_97_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(lean_object* v_name_98_, uint8_t v_bi_99_, lean_object* v_type_100_, lean_object* v_k_101_, uint8_t v_kind_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___f_108_; lean_object* v___x_109_; 
v___f_108_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_108_, 0, v_k_101_);
v___x_109_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_98_, v_bi_99_, v_type_100_, v___f_108_, v_kind_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
else
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_125_; 
v_a_118_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_125_ == 0)
{
v___x_120_ = v___x_109_;
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v___x_109_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_125_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_123_; 
if (v_isShared_121_ == 0)
{
v___x_123_ = v___x_120_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_a_118_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_98_ = stack[0].m_obj;
uint8_t v_bi_99_ = stack[1].m_num;
lean_object* v_type_100_ = stack[2].m_obj;
lean_object* v_k_101_ = stack[3].m_obj;
uint8_t v_kind_102_ = stack[4].m_num;
lean_object* v___y_103_ = stack[5].m_obj;
lean_object* v___y_104_ = stack[6].m_obj;
lean_object* v___y_105_ = stack[7].m_obj;
lean_object* v___y_106_ = stack[8].m_obj;
lean_object* v_res_126_;
v_res_126_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_98_, v_bi_99_, v_type_100_, v_k_101_, v_kind_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
stack->m_obj
 = v_res_126_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___boxed(lean_object* v_name_127_, lean_object* v_bi_128_, lean_object* v_type_129_, lean_object* v_k_130_, lean_object* v_kind_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
uint8_t v_bi_boxed_137_; uint8_t v_kind_boxed_138_; lean_object* v_res_139_; 
v_bi_boxed_137_ = lean_unbox(v_bi_128_);
v_kind_boxed_138_ = lean_unbox(v_kind_131_);
v_res_139_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_127_, v_bi_boxed_137_, v_type_129_, v_k_130_, v_kind_boxed_138_, v___y_132_, v___y_133_, v___y_134_, v___y_135_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
return v_res_139_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(lean_object* v_00_u03b1_140_, lean_object* v_name_141_, uint8_t v_bi_142_, lean_object* v_type_143_, lean_object* v_k_144_, uint8_t v_kind_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_141_, v_bi_142_, v_type_143_, v_k_144_, v_kind_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
return v___x_151_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_141_ = stack[1].m_obj;
uint8_t v_bi_142_ = stack[2].m_num;
lean_object* v_type_143_ = stack[3].m_obj;
lean_object* v_k_144_ = stack[4].m_obj;
uint8_t v_kind_145_ = stack[5].m_num;
lean_object* v___y_146_ = stack[6].m_obj;
lean_object* v___y_147_ = stack[7].m_obj;
lean_object* v___y_148_ = stack[8].m_obj;
lean_object* v___y_149_ = stack[9].m_obj;
lean_object* v_res_152_;
v_res_152_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(lean_box(0), v_name_141_, v_bi_142_, v_type_143_, v_k_144_, v_kind_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___boxed(lean_object* v_00_u03b1_153_, lean_object* v_name_154_, lean_object* v_bi_155_, lean_object* v_type_156_, lean_object* v_k_157_, lean_object* v_kind_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
uint8_t v_bi_boxed_164_; uint8_t v_kind_boxed_165_; lean_object* v_res_166_; 
v_bi_boxed_164_ = lean_unbox(v_bi_155_);
v_kind_boxed_165_ = lean_unbox(v_kind_158_);
v_res_166_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(v_00_u03b1_153_, v_name_154_, v_bi_boxed_164_, v_type_156_, v_k_157_, v_kind_boxed_165_, v___y_159_, v___y_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
return v_res_166_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(lean_object* v_type_167_, lean_object* v_maxFVars_x3f_168_, lean_object* v_k_169_, uint8_t v_cleanupAnnotations_170_, uint8_t v_whnfType_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___f_177_; lean_object* v___x_178_; 
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_177_, 0, v_k_169_);
v___x_178_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_167_, v_maxFVars_x3f_168_, v___f_177_, v_cleanupAnnotations_170_, v_whnfType_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_178_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_178_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
else
{
lean_object* v_a_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_194_; 
v_a_187_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_194_ == 0)
{
v___x_189_ = v___x_178_;
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_a_187_);
lean_dec(v___x_178_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_194_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_192_; 
if (v_isShared_190_ == 0)
{
v___x_192_ = v___x_189_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v_a_187_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_167_ = stack[0].m_obj;
lean_object* v_maxFVars_x3f_168_ = stack[1].m_obj;
lean_object* v_k_169_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_170_ = stack[3].m_num;
uint8_t v_whnfType_171_ = stack[4].m_num;
lean_object* v___y_172_ = stack[5].m_obj;
lean_object* v___y_173_ = stack[6].m_obj;
lean_object* v___y_174_ = stack[7].m_obj;
lean_object* v___y_175_ = stack[8].m_obj;
lean_object* v_res_195_;
v_res_195_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_167_, v_maxFVars_x3f_168_, v_k_169_, v_cleanupAnnotations_170_, v_whnfType_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg___boxed(lean_object* v_type_196_, lean_object* v_maxFVars_x3f_197_, lean_object* v_k_198_, lean_object* v_cleanupAnnotations_199_, lean_object* v_whnfType_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_206_; uint8_t v_whnfType_boxed_207_; lean_object* v_res_208_; 
v_cleanupAnnotations_boxed_206_ = lean_unbox(v_cleanupAnnotations_199_);
v_whnfType_boxed_207_ = lean_unbox(v_whnfType_200_);
v_res_208_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_196_, v_maxFVars_x3f_197_, v_k_198_, v_cleanupAnnotations_boxed_206_, v_whnfType_boxed_207_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_208_;
}
}
lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(lean_object* v_00_u03b1_209_, lean_object* v_type_210_, lean_object* v_maxFVars_x3f_211_, lean_object* v_k_212_, uint8_t v_cleanupAnnotations_213_, uint8_t v_whnfType_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_210_, v_maxFVars_x3f_211_, v_k_212_, v_cleanupAnnotations_213_, v_whnfType_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
return v___x_220_;
}
}
LEAN_EXPORT void l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_210_ = stack[1].m_obj;
lean_object* v_maxFVars_x3f_211_ = stack[2].m_obj;
lean_object* v_k_212_ = stack[3].m_obj;
uint8_t v_cleanupAnnotations_213_ = stack[4].m_num;
uint8_t v_whnfType_214_ = stack[5].m_num;
lean_object* v___y_215_ = stack[6].m_obj;
lean_object* v___y_216_ = stack[7].m_obj;
lean_object* v___y_217_ = stack[8].m_obj;
lean_object* v___y_218_ = stack[9].m_obj;
lean_object* v_res_221_;
v_res_221_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(lean_box(0), v_type_210_, v_maxFVars_x3f_211_, v_k_212_, v_cleanupAnnotations_213_, v_whnfType_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
stack->m_obj
 = v_res_221_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___boxed(lean_object* v_00_u03b1_222_, lean_object* v_type_223_, lean_object* v_maxFVars_x3f_224_, lean_object* v_k_225_, lean_object* v_cleanupAnnotations_226_, lean_object* v_whnfType_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_233_; uint8_t v_whnfType_boxed_234_; lean_object* v_res_235_; 
v_cleanupAnnotations_boxed_233_ = lean_unbox(v_cleanupAnnotations_226_);
v_whnfType_boxed_234_ = lean_unbox(v_whnfType_227_);
v_res_235_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(v_00_u03b1_222_, v_type_223_, v_maxFVars_x3f_224_, v_k_225_, v_cleanupAnnotations_boxed_233_, v_whnfType_boxed_234_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
return v_res_235_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(lean_object* v_name_236_, lean_object* v_levelParams_237_, lean_object* v_type_238_, lean_object* v_value_239_, lean_object* v_hints_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; uint8_t v___y_245_; uint8_t v___y_252_; lean_object* v_env_255_; uint8_t v___x_256_; 
v___x_243_ = lean_st_ref_get(v___y_241_);
v_env_255_ = lean_ctor_get(v___x_243_, 0);
lean_inc_ref_n(v_env_255_, 2);
lean_dec(v___x_243_);
v___x_256_ = l_Lean_Environment_hasUnsafe(v_env_255_, v_type_238_);
if (v___x_256_ == 0)
{
uint8_t v___x_257_; 
v___x_257_ = l_Lean_Environment_hasUnsafe(v_env_255_, v_value_239_);
v___y_252_ = v___x_257_;
goto v___jp_251_;
}
else
{
lean_dec_ref(v_env_255_);
v___y_252_ = v___x_256_;
goto v___jp_251_;
}
v___jp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
lean_inc(v_name_236_);
v___x_246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_246_, 0, v_name_236_);
lean_ctor_set(v___x_246_, 1, v_levelParams_237_);
lean_ctor_set(v___x_246_, 2, v_type_238_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_248_, 0, v_name_236_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_249_, 0, v___x_246_);
lean_ctor_set(v___x_249_, 1, v_value_239_);
lean_ctor_set(v___x_249_, 2, v_hints_240_);
lean_ctor_set(v___x_249_, 3, v___x_248_);
lean_ctor_set_uint8(v___x_249_, sizeof(void*)*4, v___y_245_);
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
v___jp_251_:
{
if (v___y_252_ == 0)
{
uint8_t v___x_253_; 
v___x_253_ = 1;
v___y_245_ = v___x_253_;
goto v___jp_244_;
}
else
{
uint8_t v___x_254_; 
v___x_254_ = 0;
v___y_245_ = v___x_254_;
goto v___jp_244_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_236_ = stack[0].m_obj;
lean_object* v_levelParams_237_ = stack[1].m_obj;
lean_object* v_type_238_ = stack[2].m_obj;
lean_object* v_value_239_ = stack[3].m_obj;
lean_object* v_hints_240_ = stack[4].m_obj;
lean_object* v___y_241_ = stack[5].m_obj;
lean_object* v_res_258_;
v_res_258_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_236_, v_levelParams_237_, v_type_238_, v_value_239_, v_hints_240_, v___y_241_);
stack->m_obj
 = v_res_258_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg___boxed(lean_object* v_name_259_, lean_object* v_levelParams_260_, lean_object* v_type_261_, lean_object* v_value_262_, lean_object* v_hints_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_259_, v_levelParams_260_, v_type_261_, v_value_262_, v_hints_263_, v___y_264_);
lean_dec(v___y_264_);
return v_res_266_;
}
}
lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(lean_object* v_name_267_, lean_object* v_levelParams_268_, lean_object* v_type_269_, lean_object* v_value_270_, lean_object* v_hints_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_267_, v_levelParams_268_, v_type_269_, v_value_270_, v_hints_271_, v___y_275_);
return v___x_277_;
}
}
LEAN_EXPORT void l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_267_ = stack[0].m_obj;
lean_object* v_levelParams_268_ = stack[1].m_obj;
lean_object* v_type_269_ = stack[2].m_obj;
lean_object* v_value_270_ = stack[3].m_obj;
lean_object* v_hints_271_ = stack[4].m_obj;
lean_object* v___y_272_ = stack[5].m_obj;
lean_object* v___y_273_ = stack[6].m_obj;
lean_object* v___y_274_ = stack[7].m_obj;
lean_object* v___y_275_ = stack[8].m_obj;
lean_object* v_res_278_;
v_res_278_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(v_name_267_, v_levelParams_268_, v_type_269_, v_value_270_, v_hints_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___boxed(lean_object* v_name_279_, lean_object* v_levelParams_280_, lean_object* v_type_281_, lean_object* v_value_282_, lean_object* v_hints_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(v_name_279_, v_levelParams_280_, v_type_281_, v_value_282_, v_hints_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
return v_res_289_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object* v___y_290_, uint8_t v_isExporting_291_, lean_object* v___x_292_, lean_object* v___y_293_, lean_object* v___x_294_, lean_object* v_a_x3f_295_){
_start:
{
lean_object* v___x_297_; lean_object* v_env_298_; lean_object* v_nextMacroScope_299_; lean_object* v_ngen_300_; lean_object* v_auxDeclNGen_301_; lean_object* v_traceState_302_; lean_object* v_recordedDeps_303_; lean_object* v_messages_304_; lean_object* v_infoState_305_; lean_object* v_snapshotTasks_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_331_; 
v___x_297_ = lean_st_ref_take(v___y_290_);
v_env_298_ = lean_ctor_get(v___x_297_, 0);
v_nextMacroScope_299_ = lean_ctor_get(v___x_297_, 1);
v_ngen_300_ = lean_ctor_get(v___x_297_, 2);
v_auxDeclNGen_301_ = lean_ctor_get(v___x_297_, 3);
v_traceState_302_ = lean_ctor_get(v___x_297_, 4);
v_recordedDeps_303_ = lean_ctor_get(v___x_297_, 6);
v_messages_304_ = lean_ctor_get(v___x_297_, 7);
v_infoState_305_ = lean_ctor_get(v___x_297_, 8);
v_snapshotTasks_306_ = lean_ctor_get(v___x_297_, 9);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v___x_297_, 5);
lean_dec(v_unused_332_);
v___x_308_ = v___x_297_;
v_isShared_309_ = v_isSharedCheck_331_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_snapshotTasks_306_);
lean_inc(v_infoState_305_);
lean_inc(v_messages_304_);
lean_inc(v_recordedDeps_303_);
lean_inc(v_traceState_302_);
lean_inc(v_auxDeclNGen_301_);
lean_inc(v_ngen_300_);
lean_inc(v_nextMacroScope_299_);
lean_inc(v_env_298_);
lean_dec(v___x_297_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_331_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = l_Lean_Environment_setExporting(v_env_298_, v_isExporting_291_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 5, v___x_292_);
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_nextMacroScope_299_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_ngen_300_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_auxDeclNGen_301_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_traceState_302_);
lean_ctor_set(v_reuseFailAlloc_330_, 5, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_330_, 6, v_recordedDeps_303_);
lean_ctor_set(v_reuseFailAlloc_330_, 7, v_messages_304_);
lean_ctor_set(v_reuseFailAlloc_330_, 8, v_infoState_305_);
lean_ctor_set(v_reuseFailAlloc_330_, 9, v_snapshotTasks_306_);
v___x_312_ = v_reuseFailAlloc_330_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_mctx_315_; lean_object* v_zetaDeltaFVarIds_316_; lean_object* v_postponed_317_; lean_object* v_diag_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v___x_313_ = lean_st_ref_put(v___y_290_, v___x_312_);
v___x_314_ = lean_st_ref_take(v___y_293_);
v_mctx_315_ = lean_ctor_get(v___x_314_, 0);
v_zetaDeltaFVarIds_316_ = lean_ctor_get(v___x_314_, 2);
v_postponed_317_ = lean_ctor_get(v___x_314_, 3);
v_diag_318_ = lean_ctor_get(v___x_314_, 4);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v___x_314_, 1);
lean_dec(v_unused_329_);
v___x_320_ = v___x_314_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_diag_318_);
lean_inc(v_postponed_317_);
lean_inc(v_zetaDeltaFVarIds_316_);
lean_inc(v_mctx_315_);
lean_dec(v___x_314_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_box(0);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_294_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_mctx_315_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_294_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_zetaDeltaFVarIds_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_postponed_317_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_diag_318_);
v___x_324_ = v_reuseFailAlloc_327_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_st_ref_put(v___y_293_, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_322_);
return v___x_326_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_290_ = stack[0].m_obj;
uint8_t v_isExporting_291_ = stack[1].m_num;
lean_object* v___x_292_ = stack[2].m_obj;
lean_object* v___y_293_ = stack[3].m_obj;
lean_object* v___x_294_ = stack[4].m_obj;
lean_object* v_a_x3f_295_ = stack[5].m_obj;
lean_object* v_res_333_;
v_res_333_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_290_, v_isExporting_291_, v___x_292_, v___y_293_, v___x_294_, v_a_x3f_295_);
stack->m_obj
 = v_res_333_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object* v___y_334_, lean_object* v_isExporting_335_, lean_object* v___x_336_, lean_object* v___y_337_, lean_object* v___x_338_, lean_object* v_a_x3f_339_, lean_object* v___y_340_){
_start:
{
uint8_t v_isExporting_boxed_341_; lean_object* v_res_342_; 
v_isExporting_boxed_341_ = lean_unbox(v_isExporting_335_);
v_res_342_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_334_, v_isExporting_boxed_341_, v___x_336_, v___y_337_, v___x_338_, v_a_x3f_339_);
lean_dec(v_a_x3f_339_);
lean_dec(v___y_337_);
lean_dec(v___y_334_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_343_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_349_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
lean_ctor_set(v___x_349_, 2, v___x_348_);
lean_ctor_set(v___x_349_, 3, v___x_348_);
lean_ctor_set(v___x_349_, 4, v___x_348_);
lean_ctor_set(v___x_349_, 5, v___x_348_);
return v___x_349_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object* v_x_350_, uint8_t v_isExporting_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; lean_object* v_env_358_; lean_object* v___x_359_; uint8_t v_isModule_360_; 
v___x_357_ = lean_st_ref_get(v___y_355_);
v_env_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc_ref(v_env_358_);
lean_dec(v___x_357_);
v___x_359_ = l_Lean_Environment_header(v_env_358_);
v_isModule_360_ = lean_ctor_get_uint8(v___x_359_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_359_);
if (v_isModule_360_ == 0)
{
lean_object* v___x_361_; 
lean_dec_ref(v_env_358_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
v___x_361_ = lean_apply_5(v_x_350_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, lean_box(0));
return v___x_361_;
}
else
{
uint8_t v_isExporting_362_; 
v_isExporting_362_ = lean_ctor_get_uint8(v_env_358_, sizeof(void*)*13);
lean_dec_ref(v_env_358_);
if (v_isExporting_351_ == 0)
{
if (v_isExporting_362_ == 0)
{
lean_object* v___x_429_; 
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
v___x_429_ = lean_apply_5(v_x_350_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, lean_box(0));
return v___x_429_;
}
else
{
goto v___jp_363_;
}
}
else
{
if (v_isExporting_362_ == 0)
{
goto v___jp_363_;
}
else
{
lean_object* v___x_430_; 
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
v___x_430_ = lean_apply_5(v_x_350_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, lean_box(0));
return v___x_430_;
}
}
v___jp_363_:
{
lean_object* v___x_364_; lean_object* v_env_365_; lean_object* v_nextMacroScope_366_; lean_object* v_ngen_367_; lean_object* v_auxDeclNGen_368_; lean_object* v_traceState_369_; lean_object* v_recordedDeps_370_; lean_object* v_messages_371_; lean_object* v_infoState_372_; lean_object* v_snapshotTasks_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_427_; 
v___x_364_ = lean_st_ref_take(v___y_355_);
v_env_365_ = lean_ctor_get(v___x_364_, 0);
v_nextMacroScope_366_ = lean_ctor_get(v___x_364_, 1);
v_ngen_367_ = lean_ctor_get(v___x_364_, 2);
v_auxDeclNGen_368_ = lean_ctor_get(v___x_364_, 3);
v_traceState_369_ = lean_ctor_get(v___x_364_, 4);
v_recordedDeps_370_ = lean_ctor_get(v___x_364_, 6);
v_messages_371_ = lean_ctor_get(v___x_364_, 7);
v_infoState_372_ = lean_ctor_get(v___x_364_, 8);
v_snapshotTasks_373_ = lean_ctor_get(v___x_364_, 9);
v_isSharedCheck_427_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; 
v_unused_428_ = lean_ctor_get(v___x_364_, 5);
lean_dec(v_unused_428_);
v___x_375_ = v___x_364_;
v_isShared_376_ = v_isSharedCheck_427_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_snapshotTasks_373_);
lean_inc(v_infoState_372_);
lean_inc(v_messages_371_);
lean_inc(v_recordedDeps_370_);
lean_inc(v_traceState_369_);
lean_inc(v_auxDeclNGen_368_);
lean_inc(v_ngen_367_);
lean_inc(v_nextMacroScope_366_);
lean_inc(v_env_365_);
lean_dec(v___x_364_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_427_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_377_ = l_Lean_Environment_setExporting(v_env_365_, v_isExporting_351_);
v___x_378_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 5, v___x_378_);
lean_ctor_set(v___x_375_, 0, v___x_377_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_nextMacroScope_366_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_ngen_367_);
lean_ctor_set(v_reuseFailAlloc_426_, 3, v_auxDeclNGen_368_);
lean_ctor_set(v_reuseFailAlloc_426_, 4, v_traceState_369_);
lean_ctor_set(v_reuseFailAlloc_426_, 5, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_426_, 6, v_recordedDeps_370_);
lean_ctor_set(v_reuseFailAlloc_426_, 7, v_messages_371_);
lean_ctor_set(v_reuseFailAlloc_426_, 8, v_infoState_372_);
lean_ctor_set(v_reuseFailAlloc_426_, 9, v_snapshotTasks_373_);
v___x_380_ = v_reuseFailAlloc_426_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v_mctx_383_; lean_object* v_zetaDeltaFVarIds_384_; lean_object* v_postponed_385_; lean_object* v_diag_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_424_; 
v___x_381_ = lean_st_ref_put(v___y_355_, v___x_380_);
v___x_382_ = lean_st_ref_take(v___y_353_);
v_mctx_383_ = lean_ctor_get(v___x_382_, 0);
v_zetaDeltaFVarIds_384_ = lean_ctor_get(v___x_382_, 2);
v_postponed_385_ = lean_ctor_get(v___x_382_, 3);
v_diag_386_ = lean_ctor_get(v___x_382_, 4);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_382_, 1);
lean_dec(v_unused_425_);
v___x_388_ = v___x_382_;
v_isShared_389_ = v_isSharedCheck_424_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_diag_386_);
lean_inc(v_postponed_385_);
lean_inc(v_zetaDeltaFVarIds_384_);
lean_inc(v_mctx_383_);
lean_dec(v___x_382_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_424_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; lean_object* v___x_392_; 
v___x_390_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_390_);
v___x_392_ = v___x_388_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_mctx_383_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v___x_390_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_zetaDeltaFVarIds_384_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_postponed_385_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_diag_386_);
v___x_392_ = v_reuseFailAlloc_423_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v_r_394_; 
v___x_393_ = lean_st_ref_put(v___y_353_, v___x_392_);
lean_inc(v___y_355_);
lean_inc_ref(v___y_354_);
lean_inc(v___y_353_);
lean_inc_ref(v___y_352_);
v_r_394_ = lean_apply_5(v_x_350_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, lean_box(0));
if (lean_obj_tag(v_r_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_411_; 
v_a_395_ = lean_ctor_get(v_r_394_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v_r_394_);
if (v_isSharedCheck_411_ == 0)
{
v___x_397_ = v_r_394_;
v_isShared_398_ = v_isSharedCheck_411_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v_r_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_411_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
lean_inc(v_a_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 1);
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_410_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
v___x_401_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_355_, v_isExporting_362_, v___x_378_, v___y_353_, v___x_390_, v___x_400_);
lean_dec_ref(v___x_400_);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_401_, 0);
lean_dec(v_unused_409_);
v___x_403_ = v___x_401_;
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
else
{
lean_dec(v___x_401_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_408_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_406_; 
if (v_isShared_404_ == 0)
{
lean_ctor_set(v___x_403_, 0, v_a_395_);
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_395_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_a_412_ = lean_ctor_get(v_r_394_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v_r_394_, 1);
v___x_413_ = lean_box(0);
v___x_414_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_355_, v_isExporting_362_, v___x_378_, v___y_353_, v___x_390_, v___x_413_);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_414_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_414_, 0);
lean_dec(v_unused_422_);
v___x_416_ = v___x_414_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_dec(v___x_414_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set_tag(v___x_416_, 1);
lean_ctor_set(v___x_416_, 0, v_a_412_);
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_412_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
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
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_350_ = stack[0].m_obj;
uint8_t v_isExporting_351_ = stack[1].m_num;
lean_object* v___y_352_ = stack[2].m_obj;
lean_object* v___y_353_ = stack[3].m_obj;
lean_object* v___y_354_ = stack[4].m_obj;
lean_object* v___y_355_ = stack[5].m_obj;
lean_object* v_res_431_;
v_res_431_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_350_, v_isExporting_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
stack->m_obj
 = v_res_431_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_432_, lean_object* v_isExporting_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v_isExporting_boxed_439_; lean_object* v_res_440_; 
v_isExporting_boxed_439_ = lean_unbox(v_isExporting_433_);
v_res_440_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_432_, v_isExporting_boxed_439_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_440_;
}
}
lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_441_, lean_object* v_x_442_, uint8_t v_isExporting_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_442_, v_isExporting_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v___x_449_;
}
}
LEAN_EXPORT void l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_442_ = stack[1].m_obj;
uint8_t v_isExporting_443_ = stack[2].m_num;
lean_object* v___y_444_ = stack[3].m_obj;
lean_object* v___y_445_ = stack[4].m_obj;
lean_object* v___y_446_ = stack[5].m_obj;
lean_object* v___y_447_ = stack[6].m_obj;
lean_object* v_res_450_;
v_res_450_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_box(0), v_x_442_, v_isExporting_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
stack->m_obj
 = v_res_450_;
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_451_, lean_object* v_x_452_, lean_object* v_isExporting_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
uint8_t v_isExporting_boxed_459_; lean_object* v_res_460_; 
v_isExporting_boxed_459_ = lean_unbox(v_isExporting_453_);
v_res_460_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_451_, v_x_452_, v_isExporting_boxed_459_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_460_;
}
}
lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_msg_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___f_468_; lean_object* v___x_15764__overap_469_; lean_object* v___x_470_; 
v___f_468_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15764__overap_469_ = lean_panic_fn_borrowed(v___f_468_, v_msg_462_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
v___x_470_ = lean_apply_5(v___x_15764__overap_469_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, lean_box(0));
return v___x_470_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_462_ = stack[0].m_obj;
lean_object* v___y_463_ = stack[1].m_obj;
lean_object* v___y_464_ = stack[2].m_obj;
lean_object* v___y_465_ = stack[3].m_obj;
lean_object* v___y_466_ = stack[4].m_obj;
lean_object* v_res_471_;
v_res_471_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_msg_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
stack->m_obj
 = v_res_471_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_msg_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_msg_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
return v_res_478_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object* v_name_479_, lean_object* v_type_480_, lean_object* v_k_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
uint8_t v___x_487_; uint8_t v___x_488_; lean_object* v___x_489_; 
v___x_487_ = 0;
v___x_488_ = 0;
v___x_489_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_479_, v___x_487_, v_type_480_, v_k_481_, v___x_488_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
return v___x_489_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_479_ = stack[0].m_obj;
lean_object* v_type_480_ = stack[1].m_obj;
lean_object* v_k_481_ = stack[2].m_obj;
lean_object* v___y_482_ = stack[3].m_obj;
lean_object* v___y_483_ = stack[4].m_obj;
lean_object* v___y_484_ = stack[5].m_obj;
lean_object* v___y_485_ = stack[6].m_obj;
lean_object* v_res_490_;
v_res_490_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_479_, v_type_480_, v_k_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
stack->m_obj
 = v_res_490_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object* v_name_491_, lean_object* v_type_492_, lean_object* v_k_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_491_, v_type_492_, v_k_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
return v_res_499_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object* v___x_500_, lean_object* v_ism2_501_, lean_object* v_motive_502_, uint8_t v___x_503_, uint8_t v___x_504_, uint8_t v___x_505_, lean_object* v_a_506_, lean_object* v___f_507_, lean_object* v_zs1_508_, lean_object* v_val_509_, lean_object* v___x_510_, lean_object* v_indName_511_, lean_object* v_v_512_, lean_object* v___x_513_, lean_object* v_params_514_, lean_object* v___x_515_, lean_object* v_h_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = l_Array_append___redArg(v___x_500_, v_ism2_501_);
v___x_523_ = l_Lean_mkAppN(v_motive_502_, v___x_522_);
lean_dec_ref(v___x_522_);
v___x_524_ = l_Lean_Meta_mkLambdaFVars(v_ism2_501_, v___x_523_, v___x_503_, v___x_504_, v___x_503_, v___x_504_, v___x_505_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; lean_object* v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
lean_dec_ref_known(v___x_524_, 1);
v___x_526_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_506_, v___f_507_, v___x_503_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___y_529_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_532_ = l_Lean_InductiveVal_numCtors(v_val_509_);
v___x_533_ = lean_nat_dec_eq(v___x_532_, v___x_510_);
lean_dec(v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v___x_515_);
v___x_534_ = l_Lean_mkConstructorElimName(v_indName_511_, v_v_512_);
v___x_535_ = l_Lean_mkConst(v___x_534_, v___x_513_);
v___x_536_ = lean_mk_empty_array_with_capacity(v___x_510_);
v___x_537_ = lean_array_push(v___x_536_, v_a_525_);
v___x_538_ = l_Array_append___redArg(v_params_514_, v___x_537_);
lean_dec_ref(v___x_537_);
v___x_539_ = l_Array_append___redArg(v___x_538_, v_ism2_501_);
v___x_540_ = lean_unsigned_to_nat(2u);
v___x_541_ = lean_mk_empty_array_with_capacity(v___x_540_);
lean_inc_ref(v_h_516_);
v___x_542_ = lean_array_push(v___x_541_, v_h_516_);
v___x_543_ = lean_array_push(v___x_542_, v_a_527_);
v___x_544_ = l_Array_append___redArg(v___x_539_, v___x_543_);
lean_dec_ref(v___x_543_);
v___x_545_ = l_Lean_mkAppN(v___x_535_, v___x_544_);
lean_dec_ref(v___x_544_);
v___y_529_ = v___x_545_;
goto v___jp_528_;
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v_v_512_);
v___x_546_ = l_Lean_mkConst(v___x_515_, v___x_513_);
v___x_547_ = lean_mk_empty_array_with_capacity(v___x_510_);
lean_inc_ref(v___x_547_);
v___x_548_ = lean_array_push(v___x_547_, v_a_525_);
v___x_549_ = l_Array_append___redArg(v_params_514_, v___x_548_);
lean_dec_ref(v___x_548_);
v___x_550_ = l_Array_append___redArg(v___x_549_, v_ism2_501_);
v___x_551_ = lean_array_push(v___x_547_, v_a_527_);
v___x_552_ = l_Array_append___redArg(v___x_550_, v___x_551_);
lean_dec_ref(v___x_551_);
v___x_553_ = l_Lean_mkAppN(v___x_546_, v___x_552_);
lean_dec_ref(v___x_552_);
v___y_529_ = v___x_553_;
goto v___jp_528_;
}
v___jp_528_:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = lean_array_push(v_zs1_508_, v_h_516_);
v___x_531_ = l_Lean_Meta_mkLambdaFVars(v___x_530_, v___y_529_, v___x_503_, v___x_504_, v___x_503_, v___x_504_, v___x_505_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec_ref(v___x_530_);
return v___x_531_;
}
}
else
{
lean_dec(v_a_525_);
lean_dec_ref(v_h_516_);
lean_dec(v___x_515_);
lean_dec_ref(v_params_514_);
lean_dec(v___x_513_);
lean_dec(v_v_512_);
lean_dec_ref(v_zs1_508_);
return v___x_526_;
}
}
else
{
lean_dec_ref(v_h_516_);
lean_dec(v___x_515_);
lean_dec_ref(v_params_514_);
lean_dec(v___x_513_);
lean_dec(v_v_512_);
lean_dec_ref(v_zs1_508_);
lean_dec_ref(v___f_507_);
lean_dec_ref(v_a_506_);
return v___x_524_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_500_ = stack[0].m_obj;
lean_object* v_ism2_501_ = stack[1].m_obj;
lean_object* v_motive_502_ = stack[2].m_obj;
uint8_t v___x_503_ = stack[3].m_num;
uint8_t v___x_504_ = stack[4].m_num;
uint8_t v___x_505_ = stack[5].m_num;
lean_object* v_a_506_ = stack[6].m_obj;
lean_object* v___f_507_ = stack[7].m_obj;
lean_object* v_zs1_508_ = stack[8].m_obj;
lean_object* v_val_509_ = stack[9].m_obj;
lean_object* v___x_510_ = stack[10].m_obj;
lean_object* v_indName_511_ = stack[11].m_obj;
lean_object* v_v_512_ = stack[12].m_obj;
lean_object* v___x_513_ = stack[13].m_obj;
lean_object* v_params_514_ = stack[14].m_obj;
lean_object* v___x_515_ = stack[15].m_obj;
lean_object* v_h_516_ = stack[16].m_obj;
lean_object* v___y_517_ = stack[17].m_obj;
lean_object* v___y_518_ = stack[18].m_obj;
lean_object* v___y_519_ = stack[19].m_obj;
lean_object* v___y_520_ = stack[20].m_obj;
lean_object* v_res_554_;
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_500_, v_ism2_501_, v_motive_502_, v___x_503_, v___x_504_, v___x_505_, v_a_506_, v___f_507_, v_zs1_508_, v_val_509_, v___x_510_, v_indName_511_, v_v_512_, v___x_513_, v_params_514_, v___x_515_, v_h_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
stack->m_obj
 = v_res_554_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_555_ = _args[0];
lean_object* v_ism2_556_ = _args[1];
lean_object* v_motive_557_ = _args[2];
lean_object* v___x_558_ = _args[3];
lean_object* v___x_559_ = _args[4];
lean_object* v___x_560_ = _args[5];
lean_object* v_a_561_ = _args[6];
lean_object* v___f_562_ = _args[7];
lean_object* v_zs1_563_ = _args[8];
lean_object* v_val_564_ = _args[9];
lean_object* v___x_565_ = _args[10];
lean_object* v_indName_566_ = _args[11];
lean_object* v_v_567_ = _args[12];
lean_object* v___x_568_ = _args[13];
lean_object* v_params_569_ = _args[14];
lean_object* v___x_570_ = _args[15];
lean_object* v_h_571_ = _args[16];
lean_object* v___y_572_ = _args[17];
lean_object* v___y_573_ = _args[18];
lean_object* v___y_574_ = _args[19];
lean_object* v___y_575_ = _args[20];
lean_object* v___y_576_ = _args[21];
_start:
{
uint8_t v___x_21236__boxed_577_; uint8_t v___x_21237__boxed_578_; uint8_t v___x_21238__boxed_579_; lean_object* v_res_580_; 
v___x_21236__boxed_577_ = lean_unbox(v___x_558_);
v___x_21237__boxed_578_ = lean_unbox(v___x_559_);
v___x_21238__boxed_579_ = lean_unbox(v___x_560_);
v_res_580_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_555_, v_ism2_556_, v_motive_557_, v___x_21236__boxed_577_, v___x_21237__boxed_578_, v___x_21238__boxed_579_, v_a_561_, v___f_562_, v_zs1_563_, v_val_564_, v___x_565_, v_indName_566_, v_v_567_, v___x_568_, v_params_569_, v___x_570_, v_h_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec(v_indName_566_);
lean_dec(v___x_565_);
lean_dec_ref(v_val_564_);
lean_dec_ref(v_ism2_556_);
return v_res_580_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object* v___x_581_, lean_object* v_alts_582_, lean_object* v___x_583_, lean_object* v_zs1_584_, uint8_t v___x_585_, uint8_t v___x_586_, uint8_t v___x_587_, lean_object* v_zs2_588_, lean_object* v_x_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_595_ = lean_array_get_borrowed(v___x_581_, v_alts_582_, v___x_583_);
v___x_596_ = l_Array_append___redArg(v_zs1_584_, v_zs2_588_);
lean_inc(v___x_595_);
v___x_597_ = l_Lean_mkAppN(v___x_595_, v___x_596_);
lean_dec_ref(v___x_596_);
v___x_598_ = l_Lean_Meta_mkLambdaFVars(v_zs2_588_, v___x_597_, v___x_585_, v___x_586_, v___x_585_, v___x_586_, v___x_587_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
return v___x_598_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_581_ = stack[0].m_obj;
lean_object* v_alts_582_ = stack[1].m_obj;
lean_object* v___x_583_ = stack[2].m_obj;
lean_object* v_zs1_584_ = stack[3].m_obj;
uint8_t v___x_585_ = stack[4].m_num;
uint8_t v___x_586_ = stack[5].m_num;
uint8_t v___x_587_ = stack[6].m_num;
lean_object* v_zs2_588_ = stack[7].m_obj;
lean_object* v_x_589_ = stack[8].m_obj;
lean_object* v___y_590_ = stack[9].m_obj;
lean_object* v___y_591_ = stack[10].m_obj;
lean_object* v___y_592_ = stack[11].m_obj;
lean_object* v___y_593_ = stack[12].m_obj;
lean_object* v_res_599_;
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_581_, v_alts_582_, v___x_583_, v_zs1_584_, v___x_585_, v___x_586_, v___x_587_, v_zs2_588_, v_x_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
stack->m_obj
 = v_res_599_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object* v___x_600_, lean_object* v_alts_601_, lean_object* v___x_602_, lean_object* v_zs1_603_, lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v___x_606_, lean_object* v_zs2_607_, lean_object* v_x_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
uint8_t v___x_21410__boxed_614_; uint8_t v___x_21411__boxed_615_; uint8_t v___x_21412__boxed_616_; lean_object* v_res_617_; 
v___x_21410__boxed_614_ = lean_unbox(v___x_604_);
v___x_21411__boxed_615_ = lean_unbox(v___x_605_);
v___x_21412__boxed_616_ = lean_unbox(v___x_606_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_600_, v_alts_601_, v___x_602_, v_zs1_603_, v___x_21410__boxed_614_, v___x_21411__boxed_615_, v___x_21412__boxed_616_, v_zs2_607_, v_x_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec_ref(v_x_608_);
lean_dec_ref(v_zs2_607_);
lean_dec(v___x_602_);
lean_dec_ref(v_alts_601_);
lean_dec_ref(v___x_600_);
return v_res_617_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_618_; lean_object* v_dummy_619_; 
v___x_618_ = lean_box(0);
v_dummy_619_ = l_Lean_Expr_sort___override(v___x_618_);
return v_dummy_619_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_box(0);
v___x_627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4));
v___x_628_ = l_Lean_mkConst(v___x_627_, v___x_626_);
return v___x_628_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object* v___x_629_, lean_object* v_alts_630_, lean_object* v___x_631_, uint8_t v___x_632_, uint8_t v___x_633_, uint8_t v___x_634_, lean_object* v___x_635_, lean_object* v___x_636_, lean_object* v___x_637_, lean_object* v_ism2_638_, lean_object* v_motive_639_, lean_object* v_a_640_, lean_object* v_val_641_, lean_object* v_indName_642_, lean_object* v_v_643_, lean_object* v___x_644_, lean_object* v_params_645_, lean_object* v___x_646_, lean_object* v___x_647_, lean_object* v___x_648_, lean_object* v_zs1_649_, lean_object* v_ctorRet1_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___f_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = lean_box(v___x_632_);
v___x_657_ = lean_box(v___x_633_);
v___x_658_ = lean_box(v___x_634_);
lean_inc_ref(v_zs1_649_);
lean_inc(v___x_631_);
v___f_659_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_659_, 0, v___x_629_);
lean_closure_set(v___f_659_, 1, v_alts_630_);
lean_closure_set(v___f_659_, 2, v___x_631_);
lean_closure_set(v___f_659_, 3, v_zs1_649_);
lean_closure_set(v___f_659_, 4, v___x_656_);
lean_closure_set(v___f_659_, 5, v___x_657_);
lean_closure_set(v___f_659_, 6, v___x_658_);
v___x_660_ = l_Lean_mkAppN(v___x_635_, v_zs1_649_);
lean_inc(v___y_654_);
lean_inc_ref(v___y_653_);
lean_inc(v___y_652_);
lean_inc_ref(v___y_651_);
v___x_661_ = lean_whnf(v_ctorRet1_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; lean_object* v_dummy_663_; lean_object* v_nargs_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___f_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v_dummy_663_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_664_ = l_Lean_Expr_getAppNumArgs(v_a_662_);
lean_inc(v_nargs_664_);
v___x_665_ = lean_mk_array(v_nargs_664_, v_dummy_663_);
v___x_666_ = lean_nat_sub(v_nargs_664_, v___x_636_);
lean_dec(v_nargs_664_);
v___x_667_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_662_, v___x_665_, v___x_666_);
v___x_668_ = lean_array_get_size(v___x_667_);
v___x_669_ = l_Array_toSubarray___redArg(v___x_667_, v___x_637_, v___x_668_);
v___x_670_ = l_Subarray_copy___redArg(v___x_669_);
v___x_671_ = lean_array_push(v___x_670_, v___x_660_);
v___x_672_ = lean_box(v___x_632_);
v___x_673_ = lean_box(v___x_633_);
v___x_674_ = lean_box(v___x_634_);
lean_inc(v___x_636_);
v___f_675_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed), 22, 16);
lean_closure_set(v___f_675_, 0, v___x_671_);
lean_closure_set(v___f_675_, 1, v_ism2_638_);
lean_closure_set(v___f_675_, 2, v_motive_639_);
lean_closure_set(v___f_675_, 3, v___x_672_);
lean_closure_set(v___f_675_, 4, v___x_673_);
lean_closure_set(v___f_675_, 5, v___x_674_);
lean_closure_set(v___f_675_, 6, v_a_640_);
lean_closure_set(v___f_675_, 7, v___f_659_);
lean_closure_set(v___f_675_, 8, v_zs1_649_);
lean_closure_set(v___f_675_, 9, v_val_641_);
lean_closure_set(v___f_675_, 10, v___x_636_);
lean_closure_set(v___f_675_, 11, v_indName_642_);
lean_closure_set(v___f_675_, 12, v_v_643_);
lean_closure_set(v___f_675_, 13, v___x_644_);
lean_closure_set(v___f_675_, 14, v_params_645_);
lean_closure_set(v___f_675_, 15, v___x_646_);
v___x_676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2));
v___x_677_ = l_Lean_Level_ofNat(v___x_636_);
lean_dec(v___x_636_);
v___x_678_ = lean_box(0);
v___x_679_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v___x_680_ = l_Lean_mkConst(v___x_676_, v___x_679_);
v___x_681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
v___x_682_ = l_Lean_mkRawNatLit(v___x_631_);
v___x_683_ = l_Lean_mkApp3(v___x_680_, v___x_681_, v___x_647_, v___x_682_);
v___x_684_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_648_, v___x_683_, v___f_675_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
return v___x_684_;
}
else
{
lean_dec_ref(v___x_660_);
lean_dec_ref(v___f_659_);
lean_dec_ref(v_zs1_649_);
lean_dec(v___x_648_);
lean_dec_ref(v___x_647_);
lean_dec(v___x_646_);
lean_dec_ref(v_params_645_);
lean_dec(v___x_644_);
lean_dec(v_v_643_);
lean_dec(v_indName_642_);
lean_dec_ref(v_val_641_);
lean_dec_ref(v_a_640_);
lean_dec_ref(v_motive_639_);
lean_dec_ref(v_ism2_638_);
lean_dec(v___x_637_);
lean_dec(v___x_636_);
lean_dec(v___x_631_);
return v___x_661_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_629_ = stack[0].m_obj;
lean_object* v_alts_630_ = stack[1].m_obj;
lean_object* v___x_631_ = stack[2].m_obj;
uint8_t v___x_632_ = stack[3].m_num;
uint8_t v___x_633_ = stack[4].m_num;
uint8_t v___x_634_ = stack[5].m_num;
lean_object* v___x_635_ = stack[6].m_obj;
lean_object* v___x_636_ = stack[7].m_obj;
lean_object* v___x_637_ = stack[8].m_obj;
lean_object* v_ism2_638_ = stack[9].m_obj;
lean_object* v_motive_639_ = stack[10].m_obj;
lean_object* v_a_640_ = stack[11].m_obj;
lean_object* v_val_641_ = stack[12].m_obj;
lean_object* v_indName_642_ = stack[13].m_obj;
lean_object* v_v_643_ = stack[14].m_obj;
lean_object* v___x_644_ = stack[15].m_obj;
lean_object* v_params_645_ = stack[16].m_obj;
lean_object* v___x_646_ = stack[17].m_obj;
lean_object* v___x_647_ = stack[18].m_obj;
lean_object* v___x_648_ = stack[19].m_obj;
lean_object* v_zs1_649_ = stack[20].m_obj;
lean_object* v_ctorRet1_650_ = stack[21].m_obj;
lean_object* v___y_651_ = stack[22].m_obj;
lean_object* v___y_652_ = stack[23].m_obj;
lean_object* v___y_653_ = stack[24].m_obj;
lean_object* v___y_654_ = stack[25].m_obj;
lean_object* v_res_685_;
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_629_, v_alts_630_, v___x_631_, v___x_632_, v___x_633_, v___x_634_, v___x_635_, v___x_636_, v___x_637_, v_ism2_638_, v_motive_639_, v_a_640_, v_val_641_, v_indName_642_, v_v_643_, v___x_644_, v_params_645_, v___x_646_, v___x_647_, v___x_648_, v_zs1_649_, v_ctorRet1_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_686_ = _args[0];
lean_object* v_alts_687_ = _args[1];
lean_object* v___x_688_ = _args[2];
lean_object* v___x_689_ = _args[3];
lean_object* v___x_690_ = _args[4];
lean_object* v___x_691_ = _args[5];
lean_object* v___x_692_ = _args[6];
lean_object* v___x_693_ = _args[7];
lean_object* v___x_694_ = _args[8];
lean_object* v_ism2_695_ = _args[9];
lean_object* v_motive_696_ = _args[10];
lean_object* v_a_697_ = _args[11];
lean_object* v_val_698_ = _args[12];
lean_object* v_indName_699_ = _args[13];
lean_object* v_v_700_ = _args[14];
lean_object* v___x_701_ = _args[15];
lean_object* v_params_702_ = _args[16];
lean_object* v___x_703_ = _args[17];
lean_object* v___x_704_ = _args[18];
lean_object* v___x_705_ = _args[19];
lean_object* v_zs1_706_ = _args[20];
lean_object* v_ctorRet1_707_ = _args[21];
lean_object* v___y_708_ = _args[22];
lean_object* v___y_709_ = _args[23];
lean_object* v___y_710_ = _args[24];
lean_object* v___y_711_ = _args[25];
lean_object* v___y_712_ = _args[26];
_start:
{
uint8_t v___x_21497__boxed_713_; uint8_t v___x_21498__boxed_714_; uint8_t v___x_21499__boxed_715_; lean_object* v_res_716_; 
v___x_21497__boxed_713_ = lean_unbox(v___x_689_);
v___x_21498__boxed_714_ = lean_unbox(v___x_690_);
v___x_21499__boxed_715_ = lean_unbox(v___x_691_);
v_res_716_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_686_, v_alts_687_, v___x_688_, v___x_21497__boxed_713_, v___x_21498__boxed_714_, v___x_21499__boxed_715_, v___x_692_, v___x_693_, v___x_694_, v_ism2_695_, v_motive_696_, v_a_697_, v_val_698_, v_indName_699_, v_v_700_, v___x_701_, v_params_702_, v___x_703_, v___x_704_, v___x_705_, v_zs1_706_, v_ctorRet1_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_716_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object* v_tail_720_, lean_object* v_params_721_, lean_object* v_alts_722_, lean_object* v___x_723_, lean_object* v_ism2_724_, lean_object* v_motive_725_, lean_object* v_val_726_, lean_object* v_indName_727_, lean_object* v___x_728_, lean_object* v___x_729_, lean_object* v___x_730_, size_t v_sz_731_, size_t v_i_732_, lean_object* v_bs_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v___x_739_; 
v___x_739_ = lean_usize_dec_lt(v_i_732_, v_sz_731_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v___x_730_);
lean_dec(v___x_729_);
lean_dec(v___x_728_);
lean_dec(v_indName_727_);
lean_dec_ref(v_val_726_);
lean_dec_ref(v_motive_725_);
lean_dec_ref(v_ism2_724_);
lean_dec(v___x_723_);
lean_dec_ref(v_alts_722_);
lean_dec_ref(v_params_721_);
lean_dec(v_tail_720_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_bs_733_);
return v___x_740_;
}
else
{
lean_object* v___x_741_; uint8_t v___x_742_; uint8_t v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_v_746_; lean_object* v___x_747_; lean_object* v_bs_x27_748_; lean_object* v___y_750_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_741_ = l_Lean_instInhabitedExpr;
v___x_742_ = 0;
v___x_743_ = 1;
v___x_744_ = lean_unsigned_to_nat(1u);
v___x_745_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v_v_746_ = lean_array_uget(v_bs_733_, v_i_732_);
v___x_747_ = lean_unsigned_to_nat(0u);
v_bs_x27_748_ = lean_array_uset(v_bs_733_, v_i_732_, v___x_747_);
v___x_764_ = lean_usize_to_nat(v_i_732_);
lean_inc(v_tail_720_);
lean_inc(v_v_746_);
v___x_765_ = l_Lean_mkConst(v_v_746_, v_tail_720_);
v___x_766_ = l_Lean_mkAppN(v___x_765_, v_params_721_);
lean_inc(v___y_737_);
lean_inc_ref(v___y_736_);
lean_inc(v___y_735_);
lean_inc_ref(v___y_734_);
lean_inc_ref(v___x_766_);
v___x_767_ = lean_infer_type(v___x_766_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___f_772_; lean_object* v___x_773_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc_n(v_a_768_, 2);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = lean_box(v___x_742_);
v___x_770_ = lean_box(v___x_739_);
v___x_771_ = lean_box(v___x_743_);
lean_inc_ref(v___x_730_);
lean_inc(v___x_729_);
lean_inc_ref(v_params_721_);
lean_inc(v___x_728_);
lean_inc(v_indName_727_);
lean_inc_ref(v_val_726_);
lean_inc_ref(v_motive_725_);
lean_inc_ref(v_ism2_724_);
lean_inc(v___x_723_);
lean_inc_ref(v_alts_722_);
v___f_772_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed), 27, 20);
lean_closure_set(v___f_772_, 0, v___x_741_);
lean_closure_set(v___f_772_, 1, v_alts_722_);
lean_closure_set(v___f_772_, 2, v___x_764_);
lean_closure_set(v___f_772_, 3, v___x_769_);
lean_closure_set(v___f_772_, 4, v___x_770_);
lean_closure_set(v___f_772_, 5, v___x_771_);
lean_closure_set(v___f_772_, 6, v___x_766_);
lean_closure_set(v___f_772_, 7, v___x_744_);
lean_closure_set(v___f_772_, 8, v___x_723_);
lean_closure_set(v___f_772_, 9, v_ism2_724_);
lean_closure_set(v___f_772_, 10, v_motive_725_);
lean_closure_set(v___f_772_, 11, v_a_768_);
lean_closure_set(v___f_772_, 12, v_val_726_);
lean_closure_set(v___f_772_, 13, v_indName_727_);
lean_closure_set(v___f_772_, 14, v_v_746_);
lean_closure_set(v___f_772_, 15, v___x_728_);
lean_closure_set(v___f_772_, 16, v_params_721_);
lean_closure_set(v___f_772_, 17, v___x_729_);
lean_closure_set(v___f_772_, 18, v___x_730_);
lean_closure_set(v___f_772_, 19, v___x_745_);
v___x_773_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_768_, v___f_772_, v___x_742_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
v___y_750_ = v___x_773_;
goto v___jp_749_;
}
else
{
lean_dec_ref(v___x_766_);
lean_dec(v___x_764_);
lean_dec(v_v_746_);
v___y_750_ = v___x_767_;
goto v___jp_749_;
}
v___jp_749_:
{
if (lean_obj_tag(v___y_750_) == 0)
{
lean_object* v_a_751_; size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v_a_751_ = lean_ctor_get(v___y_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___y_750_, 1);
v___x_752_ = ((size_t)1ULL);
v___x_753_ = lean_usize_add(v_i_732_, v___x_752_);
v___x_754_ = lean_array_uset(v_bs_x27_748_, v_i_732_, v_a_751_);
v_i_732_ = v___x_753_;
v_bs_733_ = v___x_754_;
goto _start;
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec_ref(v_bs_x27_748_);
lean_dec_ref(v___x_730_);
lean_dec(v___x_729_);
lean_dec(v___x_728_);
lean_dec(v_indName_727_);
lean_dec_ref(v_val_726_);
lean_dec_ref(v_motive_725_);
lean_dec_ref(v_ism2_724_);
lean_dec(v___x_723_);
lean_dec_ref(v_alts_722_);
lean_dec_ref(v_params_721_);
lean_dec(v_tail_720_);
v_a_756_ = lean_ctor_get(v___y_750_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___y_750_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___y_750_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___y_750_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_720_ = stack[0].m_obj;
lean_object* v_params_721_ = stack[1].m_obj;
lean_object* v_alts_722_ = stack[2].m_obj;
lean_object* v___x_723_ = stack[3].m_obj;
lean_object* v_ism2_724_ = stack[4].m_obj;
lean_object* v_motive_725_ = stack[5].m_obj;
lean_object* v_val_726_ = stack[6].m_obj;
lean_object* v_indName_727_ = stack[7].m_obj;
lean_object* v___x_728_ = stack[8].m_obj;
lean_object* v___x_729_ = stack[9].m_obj;
lean_object* v___x_730_ = stack[10].m_obj;
size_t v_sz_731_ = stack[11].m_num;
size_t v_i_732_ = stack[12].m_num;
lean_object* v_bs_733_ = stack[13].m_obj;
lean_object* v___y_734_ = stack[14].m_obj;
lean_object* v___y_735_ = stack[15].m_obj;
lean_object* v___y_736_ = stack[16].m_obj;
lean_object* v___y_737_ = stack[17].m_obj;
lean_object* v_res_774_;
v_res_774_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_720_, v_params_721_, v_alts_722_, v___x_723_, v_ism2_724_, v_motive_725_, v_val_726_, v_indName_727_, v___x_728_, v___x_729_, v___x_730_, v_sz_731_, v_i_732_, v_bs_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
stack->m_obj
 = v_res_774_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_tail_775_ = _args[0];
lean_object* v_params_776_ = _args[1];
lean_object* v_alts_777_ = _args[2];
lean_object* v___x_778_ = _args[3];
lean_object* v_ism2_779_ = _args[4];
lean_object* v_motive_780_ = _args[5];
lean_object* v_val_781_ = _args[6];
lean_object* v_indName_782_ = _args[7];
lean_object* v___x_783_ = _args[8];
lean_object* v___x_784_ = _args[9];
lean_object* v___x_785_ = _args[10];
lean_object* v_sz_786_ = _args[11];
lean_object* v_i_787_ = _args[12];
lean_object* v_bs_788_ = _args[13];
lean_object* v___y_789_ = _args[14];
lean_object* v___y_790_ = _args[15];
lean_object* v___y_791_ = _args[16];
lean_object* v___y_792_ = _args[17];
lean_object* v___y_793_ = _args[18];
_start:
{
size_t v_sz_boxed_794_; size_t v_i_boxed_795_; lean_object* v_res_796_; 
v_sz_boxed_794_ = lean_unbox_usize(v_sz_786_);
lean_dec(v_sz_786_);
v_i_boxed_795_ = lean_unbox_usize(v_i_787_);
lean_dec(v_i_787_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_775_, v_params_776_, v_alts_777_, v___x_778_, v_ism2_779_, v_motive_780_, v_val_781_, v_indName_782_, v___x_783_, v___x_784_, v___x_785_, v_sz_boxed_794_, v_i_boxed_795_, v_bs_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
return v_res_796_;
}
}
lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_797_, lean_object* v___x_798_, lean_object* v_a_799_, lean_object* v_ism1_800_, uint8_t v___x_801_, uint8_t v___x_802_, uint8_t v___x_803_, lean_object* v_name_804_, lean_object* v___x_805_, lean_object* v_params_806_, lean_object* v___x_807_, lean_object* v_tail_808_, lean_object* v_alts_809_, lean_object* v_numParams_810_, lean_object* v_ism2_811_, lean_object* v_val_812_, lean_object* v_indName_813_, lean_object* v___x_814_, lean_object* v___x_815_, lean_object* v___x_816_, lean_object* v_heq_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
lean_inc_ref(v_motive_797_);
v___x_823_ = l_Lean_mkAppN(v_motive_797_, v___x_798_);
v___x_824_ = l_Lean_mkArrow(v_a_799_, v___x_823_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_826_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
v___x_826_ = l_Lean_Meta_mkLambdaFVars(v_ism1_800_, v_a_825_, v___x_801_, v___x_802_, v___x_801_, v___x_802_, v___x_803_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; size_t v_sz_832_; size_t v___x_833_; lean_object* v___x_834_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
lean_inc(v___x_805_);
v___x_828_ = l_Lean_mkConst(v_name_804_, v___x_805_);
v___x_829_ = l_Lean_mkAppN(v___x_828_, v_params_806_);
v___x_830_ = l_Lean_Expr_app___override(v___x_829_, v_a_827_);
v___x_831_ = l_Lean_mkAppN(v___x_830_, v_ism1_800_);
v_sz_832_ = lean_array_size(v___x_807_);
v___x_833_ = ((size_t)0ULL);
lean_inc_ref(v_motive_797_);
lean_inc_ref(v_ism2_811_);
lean_inc_ref(v_alts_809_);
lean_inc_ref(v_params_806_);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_808_, v_params_806_, v_alts_809_, v_numParams_810_, v_ism2_811_, v_motive_797_, v_val_812_, v_indName_813_, v___x_805_, v___x_814_, v___x_815_, v_sz_832_, v___x_833_, v___x_807_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref_known(v___x_834_, 1);
v___x_836_ = l_Lean_mkAppN(v___x_831_, v_a_835_);
lean_dec(v_a_835_);
lean_inc_ref(v_heq_817_);
v___x_837_ = l_Lean_Meta_mkEqSymm(v_heq_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v___x_839_ = l_Lean_Expr_app___override(v___x_836_, v_a_838_);
v___x_840_ = lean_mk_empty_array_with_capacity(v___x_816_);
lean_inc_ref(v___x_840_);
v___x_841_ = lean_array_push(v___x_840_, v_motive_797_);
v___x_842_ = l_Array_append___redArg(v_params_806_, v___x_841_);
lean_dec_ref(v___x_841_);
v___x_843_ = l_Array_append___redArg(v___x_842_, v_ism1_800_);
v___x_844_ = l_Array_append___redArg(v___x_843_, v_ism2_811_);
lean_dec_ref(v_ism2_811_);
v___x_845_ = lean_array_push(v___x_840_, v_heq_817_);
v___x_846_ = l_Array_append___redArg(v___x_844_, v___x_845_);
lean_dec_ref(v___x_845_);
v___x_847_ = l_Array_append___redArg(v___x_846_, v_alts_809_);
lean_dec_ref(v_alts_809_);
v___x_848_ = l_Lean_Meta_mkLambdaFVars(v___x_847_, v___x_839_, v___x_801_, v___x_802_, v___x_801_, v___x_802_, v___x_803_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec_ref(v___x_847_);
return v___x_848_;
}
else
{
lean_dec_ref(v___x_836_);
lean_dec_ref(v_heq_817_);
lean_dec_ref(v_ism2_811_);
lean_dec_ref(v_alts_809_);
lean_dec_ref(v_params_806_);
lean_dec_ref(v_motive_797_);
return v___x_837_;
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
lean_dec_ref(v___x_831_);
lean_dec_ref(v_heq_817_);
lean_dec_ref(v_ism2_811_);
lean_dec_ref(v_alts_809_);
lean_dec_ref(v_params_806_);
lean_dec_ref(v_motive_797_);
v_a_849_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_834_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_834_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_dec_ref(v_heq_817_);
lean_dec_ref(v___x_815_);
lean_dec(v___x_814_);
lean_dec(v_indName_813_);
lean_dec_ref(v_val_812_);
lean_dec_ref(v_ism2_811_);
lean_dec(v_numParams_810_);
lean_dec_ref(v_alts_809_);
lean_dec(v_tail_808_);
lean_dec_ref(v___x_807_);
lean_dec_ref(v_params_806_);
lean_dec(v___x_805_);
lean_dec(v_name_804_);
lean_dec_ref(v_motive_797_);
return v___x_826_;
}
}
else
{
lean_dec_ref(v_heq_817_);
lean_dec_ref(v___x_815_);
lean_dec(v___x_814_);
lean_dec(v_indName_813_);
lean_dec_ref(v_val_812_);
lean_dec_ref(v_ism2_811_);
lean_dec(v_numParams_810_);
lean_dec_ref(v_alts_809_);
lean_dec(v_tail_808_);
lean_dec_ref(v___x_807_);
lean_dec_ref(v_params_806_);
lean_dec(v___x_805_);
lean_dec(v_name_804_);
lean_dec_ref(v_motive_797_);
return v___x_824_;
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtorHet___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_motive_797_ = stack[0].m_obj;
lean_object* v___x_798_ = stack[1].m_obj;
lean_object* v_a_799_ = stack[2].m_obj;
lean_object* v_ism1_800_ = stack[3].m_obj;
uint8_t v___x_801_ = stack[4].m_num;
uint8_t v___x_802_ = stack[5].m_num;
uint8_t v___x_803_ = stack[6].m_num;
lean_object* v_name_804_ = stack[7].m_obj;
lean_object* v___x_805_ = stack[8].m_obj;
lean_object* v_params_806_ = stack[9].m_obj;
lean_object* v___x_807_ = stack[10].m_obj;
lean_object* v_tail_808_ = stack[11].m_obj;
lean_object* v_alts_809_ = stack[12].m_obj;
lean_object* v_numParams_810_ = stack[13].m_obj;
lean_object* v_ism2_811_ = stack[14].m_obj;
lean_object* v_val_812_ = stack[15].m_obj;
lean_object* v_indName_813_ = stack[16].m_obj;
lean_object* v___x_814_ = stack[17].m_obj;
lean_object* v___x_815_ = stack[18].m_obj;
lean_object* v___x_816_ = stack[19].m_obj;
lean_object* v_heq_817_ = stack[20].m_obj;
lean_object* v___y_818_ = stack[21].m_obj;
lean_object* v___y_819_ = stack[22].m_obj;
lean_object* v___y_820_ = stack[23].m_obj;
lean_object* v___y_821_ = stack[24].m_obj;
lean_object* v_res_857_;
v_res_857_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_797_, v___x_798_, v_a_799_, v_ism1_800_, v___x_801_, v___x_802_, v___x_803_, v_name_804_, v___x_805_, v_params_806_, v___x_807_, v_tail_808_, v_alts_809_, v_numParams_810_, v_ism2_811_, v_val_812_, v_indName_813_, v___x_814_, v___x_815_, v___x_816_, v_heq_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
stack->m_obj
 = v_res_857_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object** _args){
lean_object* v_motive_858_ = _args[0];
lean_object* v___x_859_ = _args[1];
lean_object* v_a_860_ = _args[2];
lean_object* v_ism1_861_ = _args[3];
lean_object* v___x_862_ = _args[4];
lean_object* v___x_863_ = _args[5];
lean_object* v___x_864_ = _args[6];
lean_object* v_name_865_ = _args[7];
lean_object* v___x_866_ = _args[8];
lean_object* v_params_867_ = _args[9];
lean_object* v___x_868_ = _args[10];
lean_object* v_tail_869_ = _args[11];
lean_object* v_alts_870_ = _args[12];
lean_object* v_numParams_871_ = _args[13];
lean_object* v_ism2_872_ = _args[14];
lean_object* v_val_873_ = _args[15];
lean_object* v_indName_874_ = _args[16];
lean_object* v___x_875_ = _args[17];
lean_object* v___x_876_ = _args[18];
lean_object* v___x_877_ = _args[19];
lean_object* v_heq_878_ = _args[20];
lean_object* v___y_879_ = _args[21];
lean_object* v___y_880_ = _args[22];
lean_object* v___y_881_ = _args[23];
lean_object* v___y_882_ = _args[24];
lean_object* v___y_883_ = _args[25];
_start:
{
uint8_t v___x_21861__boxed_884_; uint8_t v___x_21862__boxed_885_; uint8_t v___x_21863__boxed_886_; lean_object* v_res_887_; 
v___x_21861__boxed_884_ = lean_unbox(v___x_862_);
v___x_21862__boxed_885_ = lean_unbox(v___x_863_);
v___x_21863__boxed_886_ = lean_unbox(v___x_864_);
v_res_887_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_858_, v___x_859_, v_a_860_, v_ism1_861_, v___x_21861__boxed_884_, v___x_21862__boxed_885_, v___x_21863__boxed_886_, v_name_865_, v___x_866_, v_params_867_, v___x_868_, v_tail_869_, v_alts_870_, v_numParams_871_, v_ism2_872_, v_val_873_, v_indName_874_, v___x_875_, v___x_876_, v___x_877_, v_heq_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___x_877_);
lean_dec_ref(v_ism1_861_);
lean_dec_ref(v___x_859_);
return v_res_887_;
}
}
lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_888_, lean_object* v_tail_889_, lean_object* v_params_890_, lean_object* v_ism1_891_, lean_object* v_ism2_892_, lean_object* v_motive_893_, lean_object* v___x_894_, uint8_t v___x_895_, uint8_t v___x_896_, uint8_t v___x_897_, lean_object* v_name_898_, lean_object* v___x_899_, lean_object* v___x_900_, lean_object* v_numParams_901_, lean_object* v_val_902_, lean_object* v___x_903_, lean_object* v___x_904_, lean_object* v_alts_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
lean_inc(v_indName_888_);
v___x_911_ = l_Lean_mkCtorIdxName(v_indName_888_);
lean_inc(v_tail_889_);
v___x_912_ = l_Lean_mkConst(v___x_911_, v_tail_889_);
lean_inc_ref_n(v_params_890_, 2);
v___x_913_ = l_Array_append___redArg(v_params_890_, v_ism1_891_);
lean_inc_ref(v___x_912_);
v___x_914_ = l_Lean_mkAppN(v___x_912_, v___x_913_);
lean_dec_ref(v___x_913_);
v___x_915_ = l_Array_append___redArg(v_params_890_, v_ism2_892_);
v___x_916_ = l_Lean_mkAppN(v___x_912_, v___x_915_);
lean_dec_ref(v___x_915_);
lean_inc_ref(v___x_916_);
lean_inc_ref(v___x_914_);
v___x_917_ = l_Lean_Meta_mkEq(v___x_914_, v___x_916_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v_a_918_; lean_object* v___x_919_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_a_918_);
lean_dec_ref_known(v___x_917_, 1);
lean_inc_ref(v___x_916_);
v___x_919_ = l_Lean_Meta_mkEq(v___x_916_, v___x_914_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___f_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref_known(v___x_919_, 1);
v___x_921_ = lean_box(v___x_895_);
v___x_922_ = lean_box(v___x_896_);
v___x_923_ = lean_box(v___x_897_);
v___f_924_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__0___boxed), 26, 20);
lean_closure_set(v___f_924_, 0, v_motive_893_);
lean_closure_set(v___f_924_, 1, v___x_894_);
lean_closure_set(v___f_924_, 2, v_a_920_);
lean_closure_set(v___f_924_, 3, v_ism1_891_);
lean_closure_set(v___f_924_, 4, v___x_921_);
lean_closure_set(v___f_924_, 5, v___x_922_);
lean_closure_set(v___f_924_, 6, v___x_923_);
lean_closure_set(v___f_924_, 7, v_name_898_);
lean_closure_set(v___f_924_, 8, v___x_899_);
lean_closure_set(v___f_924_, 9, v_params_890_);
lean_closure_set(v___f_924_, 10, v___x_900_);
lean_closure_set(v___f_924_, 11, v_tail_889_);
lean_closure_set(v___f_924_, 12, v_alts_905_);
lean_closure_set(v___f_924_, 13, v_numParams_901_);
lean_closure_set(v___f_924_, 14, v_ism2_892_);
lean_closure_set(v___f_924_, 15, v_val_902_);
lean_closure_set(v___f_924_, 16, v_indName_888_);
lean_closure_set(v___f_924_, 17, v___x_903_);
lean_closure_set(v___f_924_, 18, v___x_916_);
lean_closure_set(v___f_924_, 19, v___x_904_);
v___x_925_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_926_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_925_, v_a_918_, v___f_924_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
return v___x_926_;
}
else
{
lean_dec(v_a_918_);
lean_dec_ref(v___x_916_);
lean_dec_ref(v_alts_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec_ref(v_val_902_);
lean_dec(v_numParams_901_);
lean_dec_ref(v___x_900_);
lean_dec(v___x_899_);
lean_dec(v_name_898_);
lean_dec_ref(v___x_894_);
lean_dec_ref(v_motive_893_);
lean_dec_ref(v_ism2_892_);
lean_dec_ref(v_ism1_891_);
lean_dec_ref(v_params_890_);
lean_dec(v_tail_889_);
lean_dec(v_indName_888_);
return v___x_919_;
}
}
else
{
lean_dec_ref(v___x_916_);
lean_dec_ref(v___x_914_);
lean_dec_ref(v_alts_905_);
lean_dec(v___x_904_);
lean_dec(v___x_903_);
lean_dec_ref(v_val_902_);
lean_dec(v_numParams_901_);
lean_dec_ref(v___x_900_);
lean_dec(v___x_899_);
lean_dec(v_name_898_);
lean_dec_ref(v___x_894_);
lean_dec_ref(v_motive_893_);
lean_dec_ref(v_ism2_892_);
lean_dec_ref(v_ism1_891_);
lean_dec_ref(v_params_890_);
lean_dec(v_tail_889_);
lean_dec(v_indName_888_);
return v___x_917_;
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtorHet___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_indName_888_ = stack[0].m_obj;
lean_object* v_tail_889_ = stack[1].m_obj;
lean_object* v_params_890_ = stack[2].m_obj;
lean_object* v_ism1_891_ = stack[3].m_obj;
lean_object* v_ism2_892_ = stack[4].m_obj;
lean_object* v_motive_893_ = stack[5].m_obj;
lean_object* v___x_894_ = stack[6].m_obj;
uint8_t v___x_895_ = stack[7].m_num;
uint8_t v___x_896_ = stack[8].m_num;
uint8_t v___x_897_ = stack[9].m_num;
lean_object* v_name_898_ = stack[10].m_obj;
lean_object* v___x_899_ = stack[11].m_obj;
lean_object* v___x_900_ = stack[12].m_obj;
lean_object* v_numParams_901_ = stack[13].m_obj;
lean_object* v_val_902_ = stack[14].m_obj;
lean_object* v___x_903_ = stack[15].m_obj;
lean_object* v___x_904_ = stack[16].m_obj;
lean_object* v_alts_905_ = stack[17].m_obj;
lean_object* v___y_906_ = stack[18].m_obj;
lean_object* v___y_907_ = stack[19].m_obj;
lean_object* v___y_908_ = stack[20].m_obj;
lean_object* v___y_909_ = stack[21].m_obj;
lean_object* v_res_927_;
v_res_927_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_888_, v_tail_889_, v_params_890_, v_ism1_891_, v_ism2_892_, v_motive_893_, v___x_894_, v___x_895_, v___x_896_, v___x_897_, v_name_898_, v___x_899_, v___x_900_, v_numParams_901_, v_val_902_, v___x_903_, v___x_904_, v_alts_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
stack->m_obj
 = v_res_927_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object** _args){
lean_object* v_indName_928_ = _args[0];
lean_object* v_tail_929_ = _args[1];
lean_object* v_params_930_ = _args[2];
lean_object* v_ism1_931_ = _args[3];
lean_object* v_ism2_932_ = _args[4];
lean_object* v_motive_933_ = _args[5];
lean_object* v___x_934_ = _args[6];
lean_object* v___x_935_ = _args[7];
lean_object* v___x_936_ = _args[8];
lean_object* v___x_937_ = _args[9];
lean_object* v_name_938_ = _args[10];
lean_object* v___x_939_ = _args[11];
lean_object* v___x_940_ = _args[12];
lean_object* v_numParams_941_ = _args[13];
lean_object* v_val_942_ = _args[14];
lean_object* v___x_943_ = _args[15];
lean_object* v___x_944_ = _args[16];
lean_object* v_alts_945_ = _args[17];
lean_object* v___y_946_ = _args[18];
lean_object* v___y_947_ = _args[19];
lean_object* v___y_948_ = _args[20];
lean_object* v___y_949_ = _args[21];
lean_object* v___y_950_ = _args[22];
_start:
{
uint8_t v___x_22051__boxed_951_; uint8_t v___x_22052__boxed_952_; uint8_t v___x_22053__boxed_953_; lean_object* v_res_954_; 
v___x_22051__boxed_951_ = lean_unbox(v___x_935_);
v___x_22052__boxed_952_ = lean_unbox(v___x_936_);
v___x_22053__boxed_953_ = lean_unbox(v___x_937_);
v_res_954_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_928_, v_tail_929_, v_params_930_, v_ism1_931_, v_ism2_932_, v_motive_933_, v___x_934_, v___x_22051__boxed_951_, v___x_22052__boxed_952_, v___x_22053__boxed_953_, v_name_938_, v___x_939_, v___x_940_, v_numParams_941_, v_val_942_, v___x_943_, v___x_944_, v_alts_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_954_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_955_, lean_object* v_x_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_962_, 0, v_snd_955_);
return v___x_962_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_snd_955_ = stack[0].m_obj;
lean_object* v_x_956_ = stack[1].m_obj;
lean_object* v___y_957_ = stack[2].m_obj;
lean_object* v___y_958_ = stack[3].m_obj;
lean_object* v___y_959_ = stack[4].m_obj;
lean_object* v___y_960_ = stack[5].m_obj;
lean_object* v_res_963_;
v_res_963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_955_, v_x_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
stack->m_obj
 = v_res_963_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_964_, lean_object* v_x_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_964_, v_x_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec_ref(v_x_965_);
return v_res_971_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_972_, size_t v_i_973_, lean_object* v_bs_974_){
_start:
{
uint8_t v___x_975_; 
v___x_975_ = lean_usize_dec_lt(v_i_973_, v_sz_972_);
if (v___x_975_ == 0)
{
return v_bs_974_;
}
else
{
lean_object* v_v_976_; lean_object* v_fst_977_; lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_992_; 
v_v_976_ = lean_array_uget(v_bs_974_, v_i_973_);
v_fst_977_ = lean_ctor_get(v_v_976_, 0);
v_snd_978_ = lean_ctor_get(v_v_976_, 1);
v_isSharedCheck_992_ = !lean_is_exclusive(v_v_976_);
if (v_isSharedCheck_992_ == 0)
{
v___x_980_ = v_v_976_;
v_isShared_981_ = v_isSharedCheck_992_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_inc(v_fst_977_);
lean_dec(v_v_976_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_992_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_982_; lean_object* v_bs_x27_983_; lean_object* v___f_984_; lean_object* v___x_986_; 
v___x_982_ = lean_unsigned_to_nat(0u);
v_bs_x27_983_ = lean_array_uset(v_bs_974_, v_i_973_, v___x_982_);
v___f_984_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_984_, 0, v_snd_978_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___f_984_);
v___x_986_ = v___x_980_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_fst_977_);
lean_ctor_set(v_reuseFailAlloc_991_, 1, v___f_984_);
v___x_986_ = v_reuseFailAlloc_991_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((size_t)1ULL);
v___x_988_ = lean_usize_add(v_i_973_, v___x_987_);
v___x_989_ = lean_array_uset(v_bs_x27_983_, v_i_973_, v___x_986_);
v_i_973_ = v___x_988_;
v_bs_974_ = v___x_989_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_sz_972_ = stack[0].m_num;
size_t v_i_973_ = stack[1].m_num;
lean_object* v_bs_974_ = stack[2].m_obj;
lean_object* v_res_993_;
v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_972_, v_i_973_, v_bs_974_);
stack->m_obj
 = v_res_993_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_994_, lean_object* v_i_995_, lean_object* v_bs_996_){
_start:
{
size_t v_sz_boxed_997_; size_t v_i_boxed_998_; lean_object* v_res_999_; 
v_sz_boxed_997_ = lean_unbox_usize(v_sz_994_);
lean_dec(v_sz_994_);
v_i_boxed_998_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_res_999_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_997_, v_i_boxed_998_, v_bs_996_);
return v_res_999_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object* v___x_1000_, lean_object* v___x_1001_, lean_object* v_a_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___x_20333__overap_1008_; lean_object* v___x_1009_; 
v___x_20333__overap_1008_ = l_instInhabitedOfMonad___redArg(v___x_1000_, v___x_1001_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
v___x_1009_ = lean_apply_5(v___x_20333__overap_1008_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, lean_box(0));
return v___x_1009_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1000_ = stack[0].m_obj;
lean_object* v___x_1001_ = stack[1].m_obj;
lean_object* v_a_1002_ = stack[2].m_obj;
lean_object* v___y_1003_ = stack[3].m_obj;
lean_object* v___y_1004_ = stack[4].m_obj;
lean_object* v___y_1005_ = stack[5].m_obj;
lean_object* v___y_1006_ = stack[6].m_obj;
lean_object* v_res_1010_;
v_res_1010_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_1000_, v___x_1001_, v_a_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
stack->m_obj
 = v_res_1010_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object* v___x_1011_, lean_object* v___x_1012_, lean_object* v_a_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_1011_, v___x_1012_, v_a_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec_ref(v_a_1013_);
return v_res_1019_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_instMonadEIO___redArg();
return v___x_1020_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0);
v___x_1022_ = l_StateRefT_x27_instMonad___redArg(v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object* v_acc_1027_, lean_object* v_declInfos_1028_, lean_object* v_k_1029_, lean_object* v_kind_1030_, lean_object* v_x_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
uint8_t v_kind_boxed_1037_; lean_object* v_res_1038_; 
v_kind_boxed_1037_ = lean_unbox(v_kind_1030_);
v_res_1038_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_1027_, v_declInfos_1028_, v_k_1029_, v_kind_boxed_1037_, v_x_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
return v_res_1038_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_declInfos_1039_, lean_object* v_k_1040_, uint8_t v_kind_1041_, lean_object* v_acc_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_){
_start:
{
lean_object* v___x_1048_; lean_object* v_toApplicative_1049_; lean_object* v_toFunctor_1050_; lean_object* v_toSeq_1051_; lean_object* v_toSeqLeft_1052_; lean_object* v_toSeqRight_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___x_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_toApplicative_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1115_; 
v___x_1048_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_1049_ = lean_ctor_get(v___x_1048_, 0);
v_toFunctor_1050_ = lean_ctor_get(v_toApplicative_1049_, 0);
v_toSeq_1051_ = lean_ctor_get(v_toApplicative_1049_, 2);
v_toSeqLeft_1052_ = lean_ctor_get(v_toApplicative_1049_, 3);
v_toSeqRight_1053_ = lean_ctor_get(v_toApplicative_1049_, 4);
v___f_1054_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_1055_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_1050_, 2);
v___f_1056_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1056_, 0, v_toFunctor_1050_);
v___f_1057_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1057_, 0, v_toFunctor_1050_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___f_1056_);
lean_ctor_set(v___x_1058_, 1, v___f_1057_);
lean_inc(v_toSeqRight_1053_);
v___f_1059_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1059_, 0, v_toSeqRight_1053_);
lean_inc(v_toSeqLeft_1052_);
v___f_1060_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1060_, 0, v_toSeqLeft_1052_);
lean_inc(v_toSeq_1051_);
v___f_1061_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1061_, 0, v_toSeq_1051_);
v___x_1062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1058_);
lean_ctor_set(v___x_1062_, 1, v___f_1054_);
lean_ctor_set(v___x_1062_, 2, v___f_1061_);
lean_ctor_set(v___x_1062_, 3, v___f_1060_);
lean_ctor_set(v___x_1062_, 4, v___f_1059_);
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___f_1055_);
v___x_1064_ = l_StateRefT_x27_instMonad___redArg(v___x_1063_);
v_toApplicative_1065_ = lean_ctor_get(v___x_1064_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1064_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v___x_1064_, 1);
lean_dec(v_unused_1116_);
v___x_1067_ = v___x_1064_;
v_isShared_1068_ = v_isSharedCheck_1115_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_toApplicative_1065_);
lean_dec(v___x_1064_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1115_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_toFunctor_1069_; lean_object* v_toSeq_1070_; lean_object* v_toSeqLeft_1071_; lean_object* v_toSeqRight_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1113_; 
v_toFunctor_1069_ = lean_ctor_get(v_toApplicative_1065_, 0);
v_toSeq_1070_ = lean_ctor_get(v_toApplicative_1065_, 2);
v_toSeqLeft_1071_ = lean_ctor_get(v_toApplicative_1065_, 3);
v_toSeqRight_1072_ = lean_ctor_get(v_toApplicative_1065_, 4);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_toApplicative_1065_);
if (v_isSharedCheck_1113_ == 0)
{
lean_object* v_unused_1114_; 
v_unused_1114_ = lean_ctor_get(v_toApplicative_1065_, 1);
lean_dec(v_unused_1114_);
v___x_1074_ = v_toApplicative_1065_;
v_isShared_1075_ = v_isSharedCheck_1113_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_toSeqRight_1072_);
lean_inc(v_toSeqLeft_1071_);
lean_inc(v_toSeq_1070_);
lean_inc(v_toFunctor_1069_);
lean_dec(v_toApplicative_1065_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1113_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___f_1076_; lean_object* v___f_1077_; lean_object* v___f_1078_; lean_object* v___f_1079_; lean_object* v___x_1080_; lean_object* v___f_1081_; lean_object* v___f_1082_; lean_object* v___f_1083_; lean_object* v___x_1085_; 
v___f_1076_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_1077_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_1069_);
v___f_1078_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1078_, 0, v_toFunctor_1069_);
v___f_1079_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1079_, 0, v_toFunctor_1069_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___f_1078_);
lean_ctor_set(v___x_1080_, 1, v___f_1079_);
v___f_1081_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1081_, 0, v_toSeqRight_1072_);
v___f_1082_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1082_, 0, v_toSeqLeft_1071_);
v___f_1083_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1083_, 0, v_toSeq_1070_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 4, v___f_1081_);
lean_ctor_set(v___x_1074_, 3, v___f_1082_);
lean_ctor_set(v___x_1074_, 2, v___f_1083_);
lean_ctor_set(v___x_1074_, 1, v___f_1076_);
lean_ctor_set(v___x_1074_, 0, v___x_1080_);
v___x_1085_ = v___x_1074_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v___f_1076_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v___f_1083_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v___f_1082_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v___f_1081_);
v___x_1085_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
lean_object* v___x_1087_; 
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 1, v___f_1077_);
lean_ctor_set(v___x_1067_, 0, v___x_1085_);
v___x_1087_ = v___x_1067_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___f_1077_);
v___x_1087_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1088_ = lean_array_get_size(v_acc_1042_);
v___x_1089_ = lean_array_get_size(v_declInfos_1039_);
v___x_1090_ = lean_nat_dec_lt(v___x_1088_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_dec_ref(v___x_1087_);
lean_dec_ref(v_declInfos_1039_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
v___x_1091_ = lean_apply_6(v_k_1040_, v_acc_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, lean_box(0));
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; uint8_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___f_1095_; lean_object* v___f_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v_snd_1101_; lean_object* v_fst_1102_; lean_object* v_fst_1103_; lean_object* v_snd_1104_; lean_object* v___x_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = 0;
v___x_1094_ = l_Lean_instInhabitedExpr;
v___f_1095_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1095_, 0, v___x_1087_);
lean_closure_set(v___f_1095_, 1, v___x_1094_);
v___f_1096_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1096_, 0, v___f_1095_);
v___x_1097_ = lean_box(v___x_1093_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v___f_1096_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1092_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = lean_array_get(v___x_1099_, v_declInfos_1039_, v___x_1088_);
lean_dec_ref_known(v___x_1099_, 2);
v_snd_1101_ = lean_ctor_get(v___x_1100_, 1);
lean_inc(v_snd_1101_);
v_fst_1102_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_fst_1102_);
lean_dec(v___x_1100_);
v_fst_1103_ = lean_ctor_get(v_snd_1101_, 0);
lean_inc(v_fst_1103_);
v_snd_1104_ = lean_ctor_get(v_snd_1101_, 1);
lean_inc(v_snd_1104_);
lean_dec(v_snd_1101_);
v___x_1105_ = lean_box(v_kind_1041_);
lean_inc_ref(v_acc_1042_);
v___f_1106_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1106_, 0, v_acc_1042_);
lean_closure_set(v___f_1106_, 1, v_declInfos_1039_);
lean_closure_set(v___f_1106_, 2, v_k_1040_);
lean_closure_set(v___f_1106_, 3, v___x_1105_);
lean_inc(v___y_1046_);
lean_inc_ref(v___y_1045_);
lean_inc(v___y_1044_);
lean_inc_ref(v___y_1043_);
v___x_1107_ = lean_apply_6(v_snd_1104_, v_acc_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, lean_box(0));
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; uint8_t v___x_1109_; lean_object* v___x_1110_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
v___x_1109_ = lean_unbox(v_fst_1103_);
lean_dec(v_fst_1103_);
v___x_1110_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1102_, v___x_1109_, v_a_1108_, v___f_1106_, v_kind_1041_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
return v___x_1110_;
}
else
{
lean_dec_ref(v___f_1106_);
lean_dec(v_fst_1103_);
lean_dec(v_fst_1102_);
return v___x_1107_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_1039_ = stack[0].m_obj;
lean_object* v_k_1040_ = stack[1].m_obj;
uint8_t v_kind_1041_ = stack[2].m_num;
lean_object* v_acc_1042_ = stack[3].m_obj;
lean_object* v___y_1043_ = stack[4].m_obj;
lean_object* v___y_1044_ = stack[5].m_obj;
lean_object* v___y_1045_ = stack[6].m_obj;
lean_object* v___y_1046_ = stack[7].m_obj;
lean_object* v_res_1117_;
v_res_1117_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1039_, v_k_1040_, v_kind_1041_, v_acc_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
stack->m_obj
 = v_res_1117_;
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(lean_object* v_acc_1118_, lean_object* v_declInfos_1119_, lean_object* v_k_1120_, uint8_t v_kind_1121_, lean_object* v_x_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_array_push(v_acc_1118_, v_x_1122_);
v___x_1129_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1119_, v_k_1120_, v_kind_1121_, v___x_1128_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
return v___x_1129_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_1118_ = stack[0].m_obj;
lean_object* v_declInfos_1119_ = stack[1].m_obj;
lean_object* v_k_1120_ = stack[2].m_obj;
uint8_t v_kind_1121_ = stack[3].m_num;
lean_object* v_x_1122_ = stack[4].m_obj;
lean_object* v___y_1123_ = stack[5].m_obj;
lean_object* v___y_1124_ = stack[6].m_obj;
lean_object* v___y_1125_ = stack[7].m_obj;
lean_object* v___y_1126_ = stack[8].m_obj;
lean_object* v_res_1130_;
v_res_1130_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_1118_, v_declInfos_1119_, v_k_1120_, v_kind_1121_, v_x_1122_, v___y_1123_, v___y_1124_, v___y_1125_, v___y_1126_);
stack->m_obj
 = v_res_1130_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object* v_declInfos_1131_, lean_object* v_k_1132_, lean_object* v_kind_1133_, lean_object* v_acc_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
uint8_t v_kind_boxed_1140_; lean_object* v_res_1141_; 
v_kind_boxed_1140_ = lean_unbox(v_kind_1133_);
v_res_1141_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1131_, v_k_1132_, v_kind_boxed_1140_, v_acc_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
return v_res_1141_;
}
}
lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object* v_declInfos_1144_, lean_object* v_k_1145_, uint8_t v_kind_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_1153_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1144_, v_k_1145_, v_kind_1146_, v___x_1152_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
return v___x_1153_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_1144_ = stack[0].m_obj;
lean_object* v_k_1145_ = stack[1].m_obj;
uint8_t v_kind_1146_ = stack[2].m_num;
lean_object* v___y_1147_ = stack[3].m_obj;
lean_object* v___y_1148_ = stack[4].m_obj;
lean_object* v___y_1149_ = stack[5].m_obj;
lean_object* v___y_1150_ = stack[6].m_obj;
lean_object* v_res_1154_;
v_res_1154_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_declInfos_1144_, v_k_1145_, v_kind_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
stack->m_obj
 = v_res_1154_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object* v_declInfos_1155_, lean_object* v_k_1156_, lean_object* v_kind_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
uint8_t v_kind_boxed_1163_; lean_object* v_res_1164_; 
v_kind_boxed_1163_ = lean_unbox(v_kind_1157_);
v_res_1164_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_declInfos_1155_, v_k_1156_, v_kind_boxed_1163_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1159_);
lean_dec_ref(v___y_1158_);
return v_res_1164_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t v_sz_1165_, size_t v_i_1166_, lean_object* v_bs_1167_){
_start:
{
uint8_t v___x_1168_; 
v___x_1168_ = lean_usize_dec_lt(v_i_1166_, v_sz_1165_);
if (v___x_1168_ == 0)
{
return v_bs_1167_;
}
else
{
lean_object* v_v_1169_; lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1187_; 
v_v_1169_ = lean_array_uget(v_bs_1167_, v_i_1166_);
v_fst_1170_ = lean_ctor_get(v_v_1169_, 0);
v_snd_1171_ = lean_ctor_get(v_v_1169_, 1);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_v_1169_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1173_ = v_v_1169_;
v_isShared_1174_ = v_isSharedCheck_1187_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snd_1171_);
lean_inc(v_fst_1170_);
lean_dec(v_v_1169_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1187_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v_bs_x27_1176_; uint8_t v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1180_; 
v___x_1175_ = lean_unsigned_to_nat(0u);
v_bs_x27_1176_ = lean_array_uset(v_bs_1167_, v_i_1166_, v___x_1175_);
v___x_1177_ = 0;
v___x_1178_ = lean_box(v___x_1177_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 0, v___x_1178_);
v___x_1180_ = v___x_1173_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1178_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_snd_1171_);
v___x_1180_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; lean_object* v___x_1184_; 
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_fst_1170_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_add(v_i_1166_, v___x_1182_);
v___x_1184_ = lean_array_uset(v_bs_x27_1176_, v_i_1166_, v___x_1181_);
v_i_1166_ = v___x_1183_;
v_bs_1167_ = v___x_1184_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1165_ = stack[0].m_num;
size_t v_i_1166_ = stack[1].m_num;
lean_object* v_bs_1167_ = stack[2].m_obj;
lean_object* v_res_1188_;
v_res_1188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1165_, v_i_1166_, v_bs_1167_);
stack->m_obj
 = v_res_1188_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_sz_1189_, lean_object* v_i_1190_, lean_object* v_bs_1191_){
_start:
{
size_t v_sz_boxed_1192_; size_t v_i_boxed_1193_; lean_object* v_res_1194_; 
v_sz_boxed_1192_ = lean_unbox_usize(v_sz_1189_);
lean_dec(v_sz_1189_);
v_i_boxed_1193_ = lean_unbox_usize(v_i_1190_);
lean_dec(v_i_1190_);
v_res_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_1192_, v_i_boxed_1193_, v_bs_1191_);
return v_res_1194_;
}
}
lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_declInfos_1195_, lean_object* v_k_1196_, uint8_t v_kind_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
size_t v_sz_1203_; size_t v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_sz_1203_ = lean_array_size(v_declInfos_1195_);
v___x_1204_ = ((size_t)0ULL);
v___x_1205_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1203_, v___x_1204_, v_declInfos_1195_);
v___x_1206_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v___x_1205_, v_k_1196_, v_kind_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
return v___x_1206_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_1195_ = stack[0].m_obj;
lean_object* v_k_1196_ = stack[1].m_obj;
uint8_t v_kind_1197_ = stack[2].m_num;
lean_object* v___y_1198_ = stack[3].m_obj;
lean_object* v___y_1199_ = stack[4].m_obj;
lean_object* v___y_1200_ = stack[5].m_obj;
lean_object* v___y_1201_ = stack[6].m_obj;
lean_object* v_res_1207_;
v_res_1207_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1195_, v_k_1196_, v_kind_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
stack->m_obj
 = v_res_1207_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_declInfos_1208_, lean_object* v_k_1209_, lean_object* v_kind_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v_kind_boxed_1216_; lean_object* v_res_1217_; 
v_kind_boxed_1216_ = lean_unbox(v_kind_1210_);
v_res_1217_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1208_, v_k_1209_, v_kind_boxed_1216_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1217_;
}
}
lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_declInfos_1218_, lean_object* v_k_1219_, uint8_t v_kind_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
size_t v_sz_1226_; size_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
v_sz_1226_ = lean_array_size(v_declInfos_1218_);
v___x_1227_ = ((size_t)0ULL);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1226_, v___x_1227_, v_declInfos_1218_);
v___x_1229_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_1228_, v_k_1219_, v_kind_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
return v___x_1229_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_1218_ = stack[0].m_obj;
lean_object* v_k_1219_ = stack[1].m_obj;
uint8_t v_kind_1220_ = stack[2].m_num;
lean_object* v___y_1221_ = stack[3].m_obj;
lean_object* v___y_1222_ = stack[4].m_obj;
lean_object* v___y_1223_ = stack[5].m_obj;
lean_object* v___y_1224_ = stack[6].m_obj;
lean_object* v_res_1230_;
v_res_1230_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1218_, v_k_1219_, v_kind_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_);
stack->m_obj
 = v_res_1230_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_declInfos_1231_, lean_object* v_k_1232_, lean_object* v_kind_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
uint8_t v_kind_boxed_1239_; lean_object* v_res_1240_; 
v_kind_boxed_1239_ = lean_unbox(v_kind_1233_);
v_res_1240_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1231_, v_k_1232_, v_kind_boxed_1239_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
return v_res_1240_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_1242_, lean_object* v_dummy_1243_, lean_object* v___x_1244_, lean_object* v___x_1245_, lean_object* v___x_1246_, lean_object* v_motive_1247_, lean_object* v_zs1_1248_, uint8_t v___x_1249_, uint8_t v___x_1250_, uint8_t v___x_1251_, lean_object* v_v_1252_, lean_object* v___x_1253_, lean_object* v_zs2_1254_, lean_object* v_ctorRet2_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = l_Lean_mkAppN(v___x_1242_, v_zs2_1254_);
lean_inc(v___y_1259_);
lean_inc_ref(v___y_1258_);
lean_inc(v___y_1257_);
lean_inc_ref(v___y_1256_);
v___x_1262_ = lean_whnf(v_ctorRet2_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v_nargs_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v_nargs_1264_ = l_Lean_Expr_getAppNumArgs(v_a_1263_);
lean_inc(v_nargs_1264_);
v___x_1265_ = lean_mk_array(v_nargs_1264_, v_dummy_1243_);
v___x_1266_ = lean_nat_sub(v_nargs_1264_, v___x_1244_);
lean_dec(v_nargs_1264_);
v___x_1267_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1263_, v___x_1265_, v___x_1266_);
v___x_1268_ = lean_array_get_size(v___x_1267_);
v___x_1269_ = l_Array_toSubarray___redArg(v___x_1267_, v___x_1245_, v___x_1268_);
v___x_1270_ = l_Subarray_copy___redArg(v___x_1269_);
v___x_1271_ = lean_array_push(v___x_1270_, v___x_1261_);
v___x_1272_ = l_Array_append___redArg(v___x_1246_, v___x_1271_);
lean_dec_ref(v___x_1271_);
v___x_1273_ = l_Lean_mkAppN(v_motive_1247_, v___x_1272_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = l_Array_append___redArg(v_zs1_1248_, v_zs2_1254_);
v___x_1275_ = l_Lean_Meta_mkForallFVars(v___x_1274_, v___x_1273_, v___x_1249_, v___x_1250_, v___x_1250_, v___x_1251_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec_ref(v___x_1274_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1295_; 
v_a_1276_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1278_ = v___x_1275_;
v_isShared_1279_ = v_isSharedCheck_1295_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_dec(v___x_1275_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1295_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___y_1281_; 
if (lean_obj_tag(v_v_1252_) == 1)
{
lean_object* v_str_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v_str_1286_ = lean_ctor_get(v_v_1252_, 1);
lean_inc_ref(v_str_1286_);
lean_dec_ref_known(v_v_1252_, 2);
v___x_1287_ = lean_box(0);
v___x_1288_ = l_Lean_Name_str___override(v___x_1287_, v_str_1286_);
v___y_1281_ = v___x_1288_;
goto v___jp_1280_;
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec(v_v_1252_);
v___x_1289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_1290_ = lean_nat_add(v___x_1253_, v___x_1244_);
v___x_1291_ = l_Nat_reprFast(v___x_1290_);
v___x_1292_ = lean_string_append(v___x_1289_, v___x_1291_);
lean_dec_ref(v___x_1291_);
v___x_1293_ = lean_box(0);
v___x_1294_ = l_Lean_Name_str___override(v___x_1293_, v___x_1292_);
v___y_1281_ = v___x_1294_;
goto v___jp_1280_;
}
v___jp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1282_, 0, v___y_1281_);
lean_ctor_set(v___x_1282_, 1, v_a_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 0, v___x_1282_);
v___x_1284_ = v___x_1278_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1282_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
else
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1303_; 
lean_dec(v_v_1252_);
v_a_1296_ = lean_ctor_get(v___x_1275_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1298_ = v___x_1275_;
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1275_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1303_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1301_; 
if (v_isShared_1299_ == 0)
{
v___x_1301_ = v___x_1298_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_a_1296_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v___x_1261_);
lean_dec(v_v_1252_);
lean_dec_ref(v_zs1_1248_);
lean_dec_ref(v_motive_1247_);
lean_dec_ref(v___x_1246_);
lean_dec(v___x_1245_);
lean_dec_ref(v_dummy_1243_);
v_a_1304_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1262_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1262_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1242_ = stack[0].m_obj;
lean_object* v_dummy_1243_ = stack[1].m_obj;
lean_object* v___x_1244_ = stack[2].m_obj;
lean_object* v___x_1245_ = stack[3].m_obj;
lean_object* v___x_1246_ = stack[4].m_obj;
lean_object* v_motive_1247_ = stack[5].m_obj;
lean_object* v_zs1_1248_ = stack[6].m_obj;
uint8_t v___x_1249_ = stack[7].m_num;
uint8_t v___x_1250_ = stack[8].m_num;
uint8_t v___x_1251_ = stack[9].m_num;
lean_object* v_v_1252_ = stack[10].m_obj;
lean_object* v___x_1253_ = stack[11].m_obj;
lean_object* v_zs2_1254_ = stack[12].m_obj;
lean_object* v_ctorRet2_1255_ = stack[13].m_obj;
lean_object* v___y_1256_ = stack[14].m_obj;
lean_object* v___y_1257_ = stack[15].m_obj;
lean_object* v___y_1258_ = stack[16].m_obj;
lean_object* v___y_1259_ = stack[17].m_obj;
lean_object* v_res_1312_;
v_res_1312_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1242_, v_dummy_1243_, v___x_1244_, v___x_1245_, v___x_1246_, v_motive_1247_, v_zs1_1248_, v___x_1249_, v___x_1250_, v___x_1251_, v_v_1252_, v___x_1253_, v_zs2_1254_, v_ctorRet2_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
stack->m_obj
 = v_res_1312_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1313_ = _args[0];
lean_object* v_dummy_1314_ = _args[1];
lean_object* v___x_1315_ = _args[2];
lean_object* v___x_1316_ = _args[3];
lean_object* v___x_1317_ = _args[4];
lean_object* v_motive_1318_ = _args[5];
lean_object* v_zs1_1319_ = _args[6];
lean_object* v___x_1320_ = _args[7];
lean_object* v___x_1321_ = _args[8];
lean_object* v___x_1322_ = _args[9];
lean_object* v_v_1323_ = _args[10];
lean_object* v___x_1324_ = _args[11];
lean_object* v_zs2_1325_ = _args[12];
lean_object* v_ctorRet2_1326_ = _args[13];
lean_object* v___y_1327_ = _args[14];
lean_object* v___y_1328_ = _args[15];
lean_object* v___y_1329_ = _args[16];
lean_object* v___y_1330_ = _args[17];
lean_object* v___y_1331_ = _args[18];
_start:
{
uint8_t v___x_22728__boxed_1332_; uint8_t v___x_22729__boxed_1333_; uint8_t v___x_22730__boxed_1334_; lean_object* v_res_1335_; 
v___x_22728__boxed_1332_ = lean_unbox(v___x_1320_);
v___x_22729__boxed_1333_ = lean_unbox(v___x_1321_);
v___x_22730__boxed_1334_ = lean_unbox(v___x_1322_);
v_res_1335_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1313_, v_dummy_1314_, v___x_1315_, v___x_1316_, v___x_1317_, v_motive_1318_, v_zs1_1319_, v___x_22728__boxed_1332_, v___x_22729__boxed_1333_, v___x_22730__boxed_1334_, v_v_1323_, v___x_1324_, v_zs2_1325_, v_ctorRet2_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec_ref(v_zs2_1325_);
lean_dec(v___x_1324_);
lean_dec(v___x_1315_);
return v_res_1335_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1336_, lean_object* v___x_1337_, lean_object* v___x_1338_, lean_object* v_motive_1339_, uint8_t v___x_1340_, uint8_t v___x_1341_, uint8_t v___x_1342_, lean_object* v_v_1343_, lean_object* v___x_1344_, lean_object* v_a_1345_, lean_object* v_zs1_1346_, lean_object* v_ctorRet1_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
lean_inc_ref(v___x_1336_);
v___x_1353_ = l_Lean_mkAppN(v___x_1336_, v_zs1_1346_);
lean_inc(v___y_1351_);
lean_inc_ref(v___y_1350_);
lean_inc(v___y_1349_);
lean_inc_ref(v___y_1348_);
v___x_1354_ = lean_whnf(v_ctorRet1_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v_dummy_1356_; lean_object* v_nargs_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v_dummy_1356_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1357_ = l_Lean_Expr_getAppNumArgs(v_a_1355_);
lean_inc(v_nargs_1357_);
v___x_1358_ = lean_mk_array(v_nargs_1357_, v_dummy_1356_);
v___x_1359_ = lean_nat_sub(v_nargs_1357_, v___x_1337_);
lean_dec(v_nargs_1357_);
v___x_1360_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1355_, v___x_1358_, v___x_1359_);
v___x_1361_ = lean_array_get_size(v___x_1360_);
lean_inc(v___x_1338_);
v___x_1362_ = l_Array_toSubarray___redArg(v___x_1360_, v___x_1338_, v___x_1361_);
v___x_1363_ = l_Subarray_copy___redArg(v___x_1362_);
v___x_1364_ = lean_array_push(v___x_1363_, v___x_1353_);
v___x_1365_ = lean_box(v___x_1340_);
v___x_1366_ = lean_box(v___x_1341_);
v___x_1367_ = lean_box(v___x_1342_);
v___f_1368_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1368_, 0, v___x_1336_);
lean_closure_set(v___f_1368_, 1, v_dummy_1356_);
lean_closure_set(v___f_1368_, 2, v___x_1337_);
lean_closure_set(v___f_1368_, 3, v___x_1338_);
lean_closure_set(v___f_1368_, 4, v___x_1364_);
lean_closure_set(v___f_1368_, 5, v_motive_1339_);
lean_closure_set(v___f_1368_, 6, v_zs1_1346_);
lean_closure_set(v___f_1368_, 7, v___x_1365_);
lean_closure_set(v___f_1368_, 8, v___x_1366_);
lean_closure_set(v___f_1368_, 9, v___x_1367_);
lean_closure_set(v___f_1368_, 10, v_v_1343_);
lean_closure_set(v___f_1368_, 11, v___x_1344_);
v___x_1369_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1345_, v___f_1368_, v___x_1340_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
return v___x_1369_;
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec_ref(v___x_1353_);
lean_dec_ref(v_zs1_1346_);
lean_dec_ref(v_a_1345_);
lean_dec(v___x_1344_);
lean_dec(v_v_1343_);
lean_dec_ref(v_motive_1339_);
lean_dec(v___x_1338_);
lean_dec(v___x_1337_);
lean_dec_ref(v___x_1336_);
v_a_1370_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1354_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1354_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1336_ = stack[0].m_obj;
lean_object* v___x_1337_ = stack[1].m_obj;
lean_object* v___x_1338_ = stack[2].m_obj;
lean_object* v_motive_1339_ = stack[3].m_obj;
uint8_t v___x_1340_ = stack[4].m_num;
uint8_t v___x_1341_ = stack[5].m_num;
uint8_t v___x_1342_ = stack[6].m_num;
lean_object* v_v_1343_ = stack[7].m_obj;
lean_object* v___x_1344_ = stack[8].m_obj;
lean_object* v_a_1345_ = stack[9].m_obj;
lean_object* v_zs1_1346_ = stack[10].m_obj;
lean_object* v_ctorRet1_1347_ = stack[11].m_obj;
lean_object* v___y_1348_ = stack[12].m_obj;
lean_object* v___y_1349_ = stack[13].m_obj;
lean_object* v___y_1350_ = stack[14].m_obj;
lean_object* v___y_1351_ = stack[15].m_obj;
lean_object* v_res_1378_;
v_res_1378_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1336_, v___x_1337_, v___x_1338_, v_motive_1339_, v___x_1340_, v___x_1341_, v___x_1342_, v_v_1343_, v___x_1344_, v_a_1345_, v_zs1_1346_, v_ctorRet1_1347_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_);
stack->m_obj
 = v_res_1378_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1379_ = _args[0];
lean_object* v___x_1380_ = _args[1];
lean_object* v___x_1381_ = _args[2];
lean_object* v_motive_1382_ = _args[3];
lean_object* v___x_1383_ = _args[4];
lean_object* v___x_1384_ = _args[5];
lean_object* v___x_1385_ = _args[6];
lean_object* v_v_1386_ = _args[7];
lean_object* v___x_1387_ = _args[8];
lean_object* v_a_1388_ = _args[9];
lean_object* v_zs1_1389_ = _args[10];
lean_object* v_ctorRet1_1390_ = _args[11];
lean_object* v___y_1391_ = _args[12];
lean_object* v___y_1392_ = _args[13];
lean_object* v___y_1393_ = _args[14];
lean_object* v___y_1394_ = _args[15];
lean_object* v___y_1395_ = _args[16];
_start:
{
uint8_t v___x_22946__boxed_1396_; uint8_t v___x_22947__boxed_1397_; uint8_t v___x_22948__boxed_1398_; lean_object* v_res_1399_; 
v___x_22946__boxed_1396_ = lean_unbox(v___x_1383_);
v___x_22947__boxed_1397_ = lean_unbox(v___x_1384_);
v___x_22948__boxed_1398_ = lean_unbox(v___x_1385_);
v_res_1399_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1379_, v___x_1380_, v___x_1381_, v_motive_1382_, v___x_22946__boxed_1396_, v___x_22947__boxed_1397_, v___x_22948__boxed_1398_, v_v_1386_, v___x_1387_, v_a_1388_, v_zs1_1389_, v_ctorRet1_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
return v_res_1399_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1400_, lean_object* v_params_1401_, lean_object* v___x_1402_, lean_object* v_motive_1403_, size_t v_sz_1404_, size_t v_i_1405_, lean_object* v_bs_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_usize_dec_lt(v_i_1405_, v_sz_1404_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
lean_dec_ref(v_motive_1403_);
lean_dec(v___x_1402_);
lean_dec(v_tail_1400_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_bs_1406_);
return v___x_1413_;
}
else
{
uint8_t v___x_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; lean_object* v_v_1417_; lean_object* v___x_1418_; lean_object* v_bs_x27_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1414_ = 0;
v___x_1415_ = 1;
v___x_1416_ = lean_unsigned_to_nat(1u);
v_v_1417_ = lean_array_uget(v_bs_1406_, v_i_1405_);
v___x_1418_ = lean_unsigned_to_nat(0u);
v_bs_x27_1419_ = lean_array_uset(v_bs_1406_, v_i_1405_, v___x_1418_);
v___x_1420_ = lean_usize_to_nat(v_i_1405_);
lean_inc(v_tail_1400_);
lean_inc(v_v_1417_);
v___x_1421_ = l_Lean_mkConst(v_v_1417_, v_tail_1400_);
v___x_1422_ = l_Lean_mkAppN(v___x_1421_, v_params_1401_);
lean_inc(v___y_1410_);
lean_inc_ref(v___y_1409_);
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
lean_inc_ref(v___x_1422_);
v___x_1423_ = lean_infer_type(v___x_1422_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___f_1428_; lean_object* v___x_1429_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc_n(v_a_1424_, 2);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = lean_box(v___x_1414_);
v___x_1426_ = lean_box(v___x_1412_);
v___x_1427_ = lean_box(v___x_1415_);
lean_inc_ref(v_motive_1403_);
lean_inc(v___x_1402_);
v___f_1428_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1428_, 0, v___x_1422_);
lean_closure_set(v___f_1428_, 1, v___x_1416_);
lean_closure_set(v___f_1428_, 2, v___x_1402_);
lean_closure_set(v___f_1428_, 3, v_motive_1403_);
lean_closure_set(v___f_1428_, 4, v___x_1425_);
lean_closure_set(v___f_1428_, 5, v___x_1426_);
lean_closure_set(v___f_1428_, 6, v___x_1427_);
lean_closure_set(v___f_1428_, 7, v_v_1417_);
lean_closure_set(v___f_1428_, 8, v___x_1420_);
lean_closure_set(v___f_1428_, 9, v_a_1424_);
v___x_1429_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1424_, v___f_1428_, v___x_1414_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_object* v_a_1430_; size_t v___x_1431_; size_t v___x_1432_; lean_object* v___x_1433_; 
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___x_1431_ = ((size_t)1ULL);
v___x_1432_ = lean_usize_add(v_i_1405_, v___x_1431_);
v___x_1433_ = lean_array_uset(v_bs_x27_1419_, v_i_1405_, v_a_1430_);
v_i_1405_ = v___x_1432_;
v_bs_1406_ = v___x_1433_;
goto _start;
}
else
{
lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1442_; 
lean_dec_ref(v_bs_x27_1419_);
lean_dec_ref(v_motive_1403_);
lean_dec(v___x_1402_);
lean_dec(v_tail_1400_);
v_a_1435_ = lean_ctor_get(v___x_1429_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1429_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1437_ = v___x_1429_;
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1429_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1442_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1440_; 
if (v_isShared_1438_ == 0)
{
v___x_1440_ = v___x_1437_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v_a_1435_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec_ref(v___x_1422_);
lean_dec(v___x_1420_);
lean_dec_ref(v_bs_x27_1419_);
lean_dec(v_v_1417_);
lean_dec_ref(v_motive_1403_);
lean_dec(v___x_1402_);
lean_dec(v_tail_1400_);
v_a_1443_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1423_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1423_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_1400_ = stack[0].m_obj;
lean_object* v_params_1401_ = stack[1].m_obj;
lean_object* v___x_1402_ = stack[2].m_obj;
lean_object* v_motive_1403_ = stack[3].m_obj;
size_t v_sz_1404_ = stack[4].m_num;
size_t v_i_1405_ = stack[5].m_num;
lean_object* v_bs_1406_ = stack[6].m_obj;
lean_object* v___y_1407_ = stack[7].m_obj;
lean_object* v___y_1408_ = stack[8].m_obj;
lean_object* v___y_1409_ = stack[9].m_obj;
lean_object* v___y_1410_ = stack[10].m_obj;
lean_object* v_res_1451_;
v_res_1451_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1400_, v_params_1401_, v___x_1402_, v_motive_1403_, v_sz_1404_, v_i_1405_, v_bs_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
stack->m_obj
 = v_res_1451_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1452_, lean_object* v_params_1453_, lean_object* v___x_1454_, lean_object* v_motive_1455_, lean_object* v_sz_1456_, lean_object* v_i_1457_, lean_object* v_bs_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
size_t v_sz_boxed_1464_; size_t v_i_boxed_1465_; lean_object* v_res_1466_; 
v_sz_boxed_1464_ = lean_unbox_usize(v_sz_1456_);
lean_dec(v_sz_1456_);
v_i_boxed_1465_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_res_1466_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1452_, v_params_1453_, v___x_1454_, v_motive_1455_, v_sz_boxed_1464_, v_i_boxed_1465_, v_bs_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec_ref(v_params_1453_);
return v_res_1466_;
}
}
lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1467_, lean_object* v_indName_1468_, lean_object* v_tail_1469_, lean_object* v_params_1470_, lean_object* v_ism1_1471_, lean_object* v_ism2_1472_, lean_object* v___x_1473_, uint8_t v___x_1474_, uint8_t v___x_1475_, uint8_t v___x_1476_, lean_object* v_name_1477_, lean_object* v___x_1478_, lean_object* v_numParams_1479_, lean_object* v_val_1480_, lean_object* v___x_1481_, lean_object* v___x_1482_, lean_object* v_motive_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___f_1493_; size_t v_sz_1494_; size_t v___x_1495_; lean_object* v___x_1496_; 
v___x_1489_ = lean_array_mk(v_ctors_1467_);
v___x_1490_ = lean_box(v___x_1474_);
v___x_1491_ = lean_box(v___x_1475_);
v___x_1492_ = lean_box(v___x_1476_);
lean_inc(v_numParams_1479_);
lean_inc_ref(v___x_1489_);
lean_inc_ref(v_motive_1483_);
lean_inc_ref(v_params_1470_);
lean_inc(v_tail_1469_);
v___f_1493_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1493_, 0, v_indName_1468_);
lean_closure_set(v___f_1493_, 1, v_tail_1469_);
lean_closure_set(v___f_1493_, 2, v_params_1470_);
lean_closure_set(v___f_1493_, 3, v_ism1_1471_);
lean_closure_set(v___f_1493_, 4, v_ism2_1472_);
lean_closure_set(v___f_1493_, 5, v_motive_1483_);
lean_closure_set(v___f_1493_, 6, v___x_1473_);
lean_closure_set(v___f_1493_, 7, v___x_1490_);
lean_closure_set(v___f_1493_, 8, v___x_1491_);
lean_closure_set(v___f_1493_, 9, v___x_1492_);
lean_closure_set(v___f_1493_, 10, v_name_1477_);
lean_closure_set(v___f_1493_, 11, v___x_1478_);
lean_closure_set(v___f_1493_, 12, v___x_1489_);
lean_closure_set(v___f_1493_, 13, v_numParams_1479_);
lean_closure_set(v___f_1493_, 14, v_val_1480_);
lean_closure_set(v___f_1493_, 15, v___x_1481_);
lean_closure_set(v___f_1493_, 16, v___x_1482_);
v_sz_1494_ = lean_array_size(v___x_1489_);
v___x_1495_ = ((size_t)0ULL);
v___x_1496_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1469_, v_params_1470_, v_numParams_1479_, v_motive_1483_, v_sz_1494_, v___x_1495_, v___x_1489_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
lean_dec_ref(v_params_1470_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = 0;
v___x_1499_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_a_1497_, v___f_1493_, v___x_1498_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
return v___x_1499_;
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_dec_ref(v___f_1493_);
v_a_1500_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1496_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1496_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtorHet___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctors_1467_ = stack[0].m_obj;
lean_object* v_indName_1468_ = stack[1].m_obj;
lean_object* v_tail_1469_ = stack[2].m_obj;
lean_object* v_params_1470_ = stack[3].m_obj;
lean_object* v_ism1_1471_ = stack[4].m_obj;
lean_object* v_ism2_1472_ = stack[5].m_obj;
lean_object* v___x_1473_ = stack[6].m_obj;
uint8_t v___x_1474_ = stack[7].m_num;
uint8_t v___x_1475_ = stack[8].m_num;
uint8_t v___x_1476_ = stack[9].m_num;
lean_object* v_name_1477_ = stack[10].m_obj;
lean_object* v___x_1478_ = stack[11].m_obj;
lean_object* v_numParams_1479_ = stack[12].m_obj;
lean_object* v_val_1480_ = stack[13].m_obj;
lean_object* v___x_1481_ = stack[14].m_obj;
lean_object* v___x_1482_ = stack[15].m_obj;
lean_object* v_motive_1483_ = stack[16].m_obj;
lean_object* v___y_1484_ = stack[17].m_obj;
lean_object* v___y_1485_ = stack[18].m_obj;
lean_object* v___y_1486_ = stack[19].m_obj;
lean_object* v___y_1487_ = stack[20].m_obj;
lean_object* v_res_1508_;
v_res_1508_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1467_, v_indName_1468_, v_tail_1469_, v_params_1470_, v_ism1_1471_, v_ism2_1472_, v___x_1473_, v___x_1474_, v___x_1475_, v___x_1476_, v_name_1477_, v___x_1478_, v_numParams_1479_, v_val_1480_, v___x_1481_, v___x_1482_, v_motive_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_);
stack->m_obj
 = v_res_1508_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1509_ = _args[0];
lean_object* v_indName_1510_ = _args[1];
lean_object* v_tail_1511_ = _args[2];
lean_object* v_params_1512_ = _args[3];
lean_object* v_ism1_1513_ = _args[4];
lean_object* v_ism2_1514_ = _args[5];
lean_object* v___x_1515_ = _args[6];
lean_object* v___x_1516_ = _args[7];
lean_object* v___x_1517_ = _args[8];
lean_object* v___x_1518_ = _args[9];
lean_object* v_name_1519_ = _args[10];
lean_object* v___x_1520_ = _args[11];
lean_object* v_numParams_1521_ = _args[12];
lean_object* v_val_1522_ = _args[13];
lean_object* v___x_1523_ = _args[14];
lean_object* v___x_1524_ = _args[15];
lean_object* v_motive_1525_ = _args[16];
lean_object* v___y_1526_ = _args[17];
lean_object* v___y_1527_ = _args[18];
lean_object* v___y_1528_ = _args[19];
lean_object* v___y_1529_ = _args[20];
lean_object* v___y_1530_ = _args[21];
_start:
{
uint8_t v___x_23226__boxed_1531_; uint8_t v___x_23227__boxed_1532_; uint8_t v___x_23228__boxed_1533_; lean_object* v_res_1534_; 
v___x_23226__boxed_1531_ = lean_unbox(v___x_1516_);
v___x_23227__boxed_1532_ = lean_unbox(v___x_1517_);
v___x_23228__boxed_1533_ = lean_unbox(v___x_1518_);
v_res_1534_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1509_, v_indName_1510_, v_tail_1511_, v_params_1512_, v_ism1_1513_, v_ism2_1514_, v___x_1515_, v___x_23226__boxed_1531_, v___x_23227__boxed_1532_, v___x_23228__boxed_1533_, v_name_1519_, v___x_1520_, v_numParams_1521_, v_val_1522_, v___x_1523_, v___x_1524_, v_motive_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
return v_res_1534_;
}
}
lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1538_, lean_object* v_head_1539_, lean_object* v_ctors_1540_, lean_object* v_indName_1541_, lean_object* v_tail_1542_, lean_object* v_params_1543_, lean_object* v_name_1544_, lean_object* v___x_1545_, lean_object* v_numParams_1546_, lean_object* v_val_1547_, lean_object* v___x_1548_, lean_object* v___x_1549_, lean_object* v_ism2_1550_, lean_object* v_x_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; uint8_t v___x_1560_; uint8_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___f_1565_; lean_object* v___x_1566_; 
lean_inc_ref(v_ism1_1538_);
v___x_1557_ = l_Array_append___redArg(v_ism1_1538_, v_ism2_1550_);
v___x_1558_ = l_Lean_mkSort(v_head_1539_);
v___x_1559_ = 0;
v___x_1560_ = 1;
v___x_1561_ = 1;
v___x_1562_ = lean_box(v___x_1559_);
v___x_1563_ = lean_box(v___x_1560_);
v___x_1564_ = lean_box(v___x_1561_);
lean_inc_ref(v___x_1557_);
v___f_1565_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 22, 16);
lean_closure_set(v___f_1565_, 0, v_ctors_1540_);
lean_closure_set(v___f_1565_, 1, v_indName_1541_);
lean_closure_set(v___f_1565_, 2, v_tail_1542_);
lean_closure_set(v___f_1565_, 3, v_params_1543_);
lean_closure_set(v___f_1565_, 4, v_ism1_1538_);
lean_closure_set(v___f_1565_, 5, v_ism2_1550_);
lean_closure_set(v___f_1565_, 6, v___x_1557_);
lean_closure_set(v___f_1565_, 7, v___x_1562_);
lean_closure_set(v___f_1565_, 8, v___x_1563_);
lean_closure_set(v___f_1565_, 9, v___x_1564_);
lean_closure_set(v___f_1565_, 10, v_name_1544_);
lean_closure_set(v___f_1565_, 11, v___x_1545_);
lean_closure_set(v___f_1565_, 12, v_numParams_1546_);
lean_closure_set(v___f_1565_, 13, v_val_1547_);
lean_closure_set(v___f_1565_, 14, v___x_1548_);
lean_closure_set(v___f_1565_, 15, v___x_1549_);
v___x_1566_ = l_Lean_Meta_mkForallFVars(v___x_1557_, v___x_1558_, v___x_1559_, v___x_1560_, v___x_1560_, v___x_1561_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
lean_dec_ref(v___x_1557_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v_a_1567_; lean_object* v___x_1568_; uint8_t v___x_1569_; lean_object* v___x_1570_; 
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_a_1567_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1568_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1569_ = 0;
v___x_1570_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1568_, v___x_1561_, v_a_1567_, v___f_1565_, v___x_1569_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
return v___x_1570_;
}
else
{
lean_dec_ref(v___f_1565_);
return v___x_1566_;
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtorHet___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_ism1_1538_ = stack[0].m_obj;
lean_object* v_head_1539_ = stack[1].m_obj;
lean_object* v_ctors_1540_ = stack[2].m_obj;
lean_object* v_indName_1541_ = stack[3].m_obj;
lean_object* v_tail_1542_ = stack[4].m_obj;
lean_object* v_params_1543_ = stack[5].m_obj;
lean_object* v_name_1544_ = stack[6].m_obj;
lean_object* v___x_1545_ = stack[7].m_obj;
lean_object* v_numParams_1546_ = stack[8].m_obj;
lean_object* v_val_1547_ = stack[9].m_obj;
lean_object* v___x_1548_ = stack[10].m_obj;
lean_object* v___x_1549_ = stack[11].m_obj;
lean_object* v_ism2_1550_ = stack[12].m_obj;
lean_object* v_x_1551_ = stack[13].m_obj;
lean_object* v___y_1552_ = stack[14].m_obj;
lean_object* v___y_1553_ = stack[15].m_obj;
lean_object* v___y_1554_ = stack[16].m_obj;
lean_object* v___y_1555_ = stack[17].m_obj;
lean_object* v_res_1571_;
v_res_1571_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1538_, v_head_1539_, v_ctors_1540_, v_indName_1541_, v_tail_1542_, v_params_1543_, v_name_1544_, v___x_1545_, v_numParams_1546_, v_val_1547_, v___x_1548_, v___x_1549_, v_ism2_1550_, v_x_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_);
stack->m_obj
 = v_res_1571_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1572_ = _args[0];
lean_object* v_head_1573_ = _args[1];
lean_object* v_ctors_1574_ = _args[2];
lean_object* v_indName_1575_ = _args[3];
lean_object* v_tail_1576_ = _args[4];
lean_object* v_params_1577_ = _args[5];
lean_object* v_name_1578_ = _args[6];
lean_object* v___x_1579_ = _args[7];
lean_object* v_numParams_1580_ = _args[8];
lean_object* v_val_1581_ = _args[9];
lean_object* v___x_1582_ = _args[10];
lean_object* v___x_1583_ = _args[11];
lean_object* v_ism2_1584_ = _args[12];
lean_object* v_x_1585_ = _args[13];
lean_object* v___y_1586_ = _args[14];
lean_object* v___y_1587_ = _args[15];
lean_object* v___y_1588_ = _args[16];
lean_object* v___y_1589_ = _args[17];
lean_object* v___y_1590_ = _args[18];
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1572_, v_head_1573_, v_ctors_1574_, v_indName_1575_, v_tail_1576_, v_params_1577_, v_name_1578_, v___x_1579_, v_numParams_1580_, v_val_1581_, v___x_1582_, v___x_1583_, v_ism2_1584_, v_x_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
lean_dec_ref(v_x_1585_);
return v_res_1591_;
}
}
lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1592_, lean_object* v_ctors_1593_, lean_object* v_indName_1594_, lean_object* v_tail_1595_, lean_object* v_params_1596_, lean_object* v_name_1597_, lean_object* v___x_1598_, lean_object* v_numParams_1599_, lean_object* v_val_1600_, lean_object* v___x_1601_, lean_object* v___x_1602_, lean_object* v_t_1603_, lean_object* v___x_1604_, lean_object* v_ism1_1605_, lean_object* v_x_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___f_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 19, 12);
lean_closure_set(v___f_1612_, 0, v_ism1_1605_);
lean_closure_set(v___f_1612_, 1, v_head_1592_);
lean_closure_set(v___f_1612_, 2, v_ctors_1593_);
lean_closure_set(v___f_1612_, 3, v_indName_1594_);
lean_closure_set(v___f_1612_, 4, v_tail_1595_);
lean_closure_set(v___f_1612_, 5, v_params_1596_);
lean_closure_set(v___f_1612_, 6, v_name_1597_);
lean_closure_set(v___f_1612_, 7, v___x_1598_);
lean_closure_set(v___f_1612_, 8, v_numParams_1599_);
lean_closure_set(v___f_1612_, 9, v_val_1600_);
lean_closure_set(v___f_1612_, 10, v___x_1601_);
lean_closure_set(v___f_1612_, 11, v___x_1602_);
v___x_1613_ = 0;
v___x_1614_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1603_, v___x_1604_, v___f_1612_, v___x_1613_, v___x_1613_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
return v___x_1614_;
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtorHet___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_head_1592_ = stack[0].m_obj;
lean_object* v_ctors_1593_ = stack[1].m_obj;
lean_object* v_indName_1594_ = stack[2].m_obj;
lean_object* v_tail_1595_ = stack[3].m_obj;
lean_object* v_params_1596_ = stack[4].m_obj;
lean_object* v_name_1597_ = stack[5].m_obj;
lean_object* v___x_1598_ = stack[6].m_obj;
lean_object* v_numParams_1599_ = stack[7].m_obj;
lean_object* v_val_1600_ = stack[8].m_obj;
lean_object* v___x_1601_ = stack[9].m_obj;
lean_object* v___x_1602_ = stack[10].m_obj;
lean_object* v_t_1603_ = stack[11].m_obj;
lean_object* v___x_1604_ = stack[12].m_obj;
lean_object* v_ism1_1605_ = stack[13].m_obj;
lean_object* v_x_1606_ = stack[14].m_obj;
lean_object* v___y_1607_ = stack[15].m_obj;
lean_object* v___y_1608_ = stack[16].m_obj;
lean_object* v___y_1609_ = stack[17].m_obj;
lean_object* v___y_1610_ = stack[18].m_obj;
lean_object* v_res_1615_;
v_res_1615_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1592_, v_ctors_1593_, v_indName_1594_, v_tail_1595_, v_params_1596_, v_name_1597_, v___x_1598_, v_numParams_1599_, v_val_1600_, v___x_1601_, v___x_1602_, v_t_1603_, v___x_1604_, v_ism1_1605_, v_x_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_);
stack->m_obj
 = v_res_1615_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1616_ = _args[0];
lean_object* v_ctors_1617_ = _args[1];
lean_object* v_indName_1618_ = _args[2];
lean_object* v_tail_1619_ = _args[3];
lean_object* v_params_1620_ = _args[4];
lean_object* v_name_1621_ = _args[5];
lean_object* v___x_1622_ = _args[6];
lean_object* v_numParams_1623_ = _args[7];
lean_object* v_val_1624_ = _args[8];
lean_object* v___x_1625_ = _args[9];
lean_object* v___x_1626_ = _args[10];
lean_object* v_t_1627_ = _args[11];
lean_object* v___x_1628_ = _args[12];
lean_object* v_ism1_1629_ = _args[13];
lean_object* v_x_1630_ = _args[14];
lean_object* v___y_1631_ = _args[15];
lean_object* v___y_1632_ = _args[16];
lean_object* v___y_1633_ = _args[17];
lean_object* v___y_1634_ = _args[18];
lean_object* v___y_1635_ = _args[19];
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1616_, v_ctors_1617_, v_indName_1618_, v_tail_1619_, v_params_1620_, v_name_1621_, v___x_1622_, v_numParams_1623_, v_val_1624_, v___x_1625_, v___x_1626_, v_t_1627_, v___x_1628_, v_ism1_1629_, v_x_1630_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_);
lean_dec(v___y_1634_);
lean_dec_ref(v___y_1633_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec_ref(v_x_1630_);
return v_res_1636_;
}
}
lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1637_, lean_object* v___x_1638_, lean_object* v_head_1639_, lean_object* v_ctors_1640_, lean_object* v_indName_1641_, lean_object* v_tail_1642_, lean_object* v_params_1643_, lean_object* v_name_1644_, lean_object* v___x_1645_, lean_object* v_numParams_1646_, lean_object* v_val_1647_, lean_object* v___x_1648_, lean_object* v_x_1649_, lean_object* v_t_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___f_1658_; uint8_t v___x_1659_; lean_object* v___x_1660_; 
v___x_1656_ = lean_nat_add(v_numIndices_1637_, v___x_1638_);
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_inc_ref(v___x_1657_);
lean_inc_ref(v_t_1650_);
v___f_1658_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 20, 13);
lean_closure_set(v___f_1658_, 0, v_head_1639_);
lean_closure_set(v___f_1658_, 1, v_ctors_1640_);
lean_closure_set(v___f_1658_, 2, v_indName_1641_);
lean_closure_set(v___f_1658_, 3, v_tail_1642_);
lean_closure_set(v___f_1658_, 4, v_params_1643_);
lean_closure_set(v___f_1658_, 5, v_name_1644_);
lean_closure_set(v___f_1658_, 6, v___x_1645_);
lean_closure_set(v___f_1658_, 7, v_numParams_1646_);
lean_closure_set(v___f_1658_, 8, v_val_1647_);
lean_closure_set(v___f_1658_, 9, v___x_1648_);
lean_closure_set(v___f_1658_, 10, v___x_1638_);
lean_closure_set(v___f_1658_, 11, v_t_1650_);
lean_closure_set(v___f_1658_, 12, v___x_1657_);
v___x_1659_ = 0;
v___x_1660_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1650_, v___x_1657_, v___f_1658_, v___x_1659_, v___x_1659_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1660_;
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtorHet___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_1637_ = stack[0].m_obj;
lean_object* v___x_1638_ = stack[1].m_obj;
lean_object* v_head_1639_ = stack[2].m_obj;
lean_object* v_ctors_1640_ = stack[3].m_obj;
lean_object* v_indName_1641_ = stack[4].m_obj;
lean_object* v_tail_1642_ = stack[5].m_obj;
lean_object* v_params_1643_ = stack[6].m_obj;
lean_object* v_name_1644_ = stack[7].m_obj;
lean_object* v___x_1645_ = stack[8].m_obj;
lean_object* v_numParams_1646_ = stack[9].m_obj;
lean_object* v_val_1647_ = stack[10].m_obj;
lean_object* v___x_1648_ = stack[11].m_obj;
lean_object* v_x_1649_ = stack[12].m_obj;
lean_object* v_t_1650_ = stack[13].m_obj;
lean_object* v___y_1651_ = stack[14].m_obj;
lean_object* v___y_1652_ = stack[15].m_obj;
lean_object* v___y_1653_ = stack[16].m_obj;
lean_object* v___y_1654_ = stack[17].m_obj;
lean_object* v_res_1661_;
v_res_1661_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1637_, v___x_1638_, v_head_1639_, v_ctors_1640_, v_indName_1641_, v_tail_1642_, v_params_1643_, v_name_1644_, v___x_1645_, v_numParams_1646_, v_val_1647_, v___x_1648_, v_x_1649_, v_t_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
stack->m_obj
 = v_res_1661_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1662_ = _args[0];
lean_object* v___x_1663_ = _args[1];
lean_object* v_head_1664_ = _args[2];
lean_object* v_ctors_1665_ = _args[3];
lean_object* v_indName_1666_ = _args[4];
lean_object* v_tail_1667_ = _args[5];
lean_object* v_params_1668_ = _args[6];
lean_object* v_name_1669_ = _args[7];
lean_object* v___x_1670_ = _args[8];
lean_object* v_numParams_1671_ = _args[9];
lean_object* v_val_1672_ = _args[10];
lean_object* v___x_1673_ = _args[11];
lean_object* v_x_1674_ = _args[12];
lean_object* v_t_1675_ = _args[13];
lean_object* v___y_1676_ = _args[14];
lean_object* v___y_1677_ = _args[15];
lean_object* v___y_1678_ = _args[16];
lean_object* v___y_1679_ = _args[17];
lean_object* v___y_1680_ = _args[18];
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1662_, v___x_1663_, v_head_1664_, v_ctors_1665_, v_indName_1666_, v_tail_1667_, v_params_1668_, v_name_1669_, v___x_1670_, v_numParams_1671_, v_val_1672_, v___x_1673_, v_x_1674_, v_t_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v_x_1674_);
lean_dec(v_numIndices_1662_);
return v_res_1681_;
}
}
lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1684_, lean_object* v_head_1685_, lean_object* v_ctors_1686_, lean_object* v_indName_1687_, lean_object* v_tail_1688_, lean_object* v_name_1689_, lean_object* v___x_1690_, lean_object* v_numParams_1691_, lean_object* v_val_1692_, lean_object* v___x_1693_, lean_object* v_params_1694_, lean_object* v_t_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1701_ = lean_unsigned_to_nat(1u);
v___f_1702_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 19, 12);
lean_closure_set(v___f_1702_, 0, v_numIndices_1684_);
lean_closure_set(v___f_1702_, 1, v___x_1701_);
lean_closure_set(v___f_1702_, 2, v_head_1685_);
lean_closure_set(v___f_1702_, 3, v_ctors_1686_);
lean_closure_set(v___f_1702_, 4, v_indName_1687_);
lean_closure_set(v___f_1702_, 5, v_tail_1688_);
lean_closure_set(v___f_1702_, 6, v_params_1694_);
lean_closure_set(v___f_1702_, 7, v_name_1689_);
lean_closure_set(v___f_1702_, 8, v___x_1690_);
lean_closure_set(v___f_1702_, 9, v_numParams_1691_);
lean_closure_set(v___f_1702_, 10, v_val_1692_);
lean_closure_set(v___f_1702_, 11, v___x_1693_);
v___x_1703_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1704_ = 0;
v___x_1705_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1695_, v___x_1703_, v___f_1702_, v___x_1704_, v___x_1704_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
return v___x_1705_;
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtorHet___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_1684_ = stack[0].m_obj;
lean_object* v_head_1685_ = stack[1].m_obj;
lean_object* v_ctors_1686_ = stack[2].m_obj;
lean_object* v_indName_1687_ = stack[3].m_obj;
lean_object* v_tail_1688_ = stack[4].m_obj;
lean_object* v_name_1689_ = stack[5].m_obj;
lean_object* v___x_1690_ = stack[6].m_obj;
lean_object* v_numParams_1691_ = stack[7].m_obj;
lean_object* v_val_1692_ = stack[8].m_obj;
lean_object* v___x_1693_ = stack[9].m_obj;
lean_object* v_params_1694_ = stack[10].m_obj;
lean_object* v_t_1695_ = stack[11].m_obj;
lean_object* v___y_1696_ = stack[12].m_obj;
lean_object* v___y_1697_ = stack[13].m_obj;
lean_object* v___y_1698_ = stack[14].m_obj;
lean_object* v___y_1699_ = stack[15].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1684_, v_head_1685_, v_ctors_1686_, v_indName_1687_, v_tail_1688_, v_name_1689_, v___x_1690_, v_numParams_1691_, v_val_1692_, v___x_1693_, v_params_1694_, v_t_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
stack->m_obj
 = v_res_1706_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1707_ = _args[0];
lean_object* v_head_1708_ = _args[1];
lean_object* v_ctors_1709_ = _args[2];
lean_object* v_indName_1710_ = _args[3];
lean_object* v_tail_1711_ = _args[4];
lean_object* v_name_1712_ = _args[5];
lean_object* v___x_1713_ = _args[6];
lean_object* v_numParams_1714_ = _args[7];
lean_object* v_val_1715_ = _args[8];
lean_object* v___x_1716_ = _args[9];
lean_object* v_params_1717_ = _args[10];
lean_object* v_t_1718_ = _args[11];
lean_object* v___y_1719_ = _args[12];
lean_object* v___y_1720_ = _args[13];
lean_object* v___y_1721_ = _args[14];
lean_object* v___y_1722_ = _args[15];
lean_object* v___y_1723_ = _args[16];
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1707_, v_head_1708_, v_ctors_1709_, v_indName_1710_, v_tail_1711_, v_name_1712_, v___x_1713_, v_numParams_1714_, v_val_1715_, v___x_1716_, v_params_1717_, v_t_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1724_;
}
}
lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1725_, lean_object* v_declName_1726_, lean_object* v_levelParams_1727_, uint8_t v___x_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v___x_1734_; 
lean_inc(v___y_1732_);
lean_inc_ref(v___y_1731_);
lean_inc_ref(v_a_1725_);
v___x_1734_ = lean_infer_type(v_a_1725_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1746_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_a_1735_);
lean_dec_ref_known(v___x_1734_, 1);
v___x_1736_ = lean_box(1);
v___x_1737_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1726_, v_levelParams_1727_, v_a_1735_, v_a_1725_, v___x_1736_, v___y_1732_);
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1746_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1743_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set_tag(v___x_1740_, 1);
v___x_1743_ = v___x_1740_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1738_);
v___x_1743_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_addDecl(v___x_1743_, v___x_1728_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v___x_1744_;
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v_levelParams_1727_);
lean_dec(v_declName_1726_);
lean_dec_ref(v_a_1725_);
v_a_1747_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1734_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1734_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtorHet___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1725_ = stack[0].m_obj;
lean_object* v_declName_1726_ = stack[1].m_obj;
lean_object* v_levelParams_1727_ = stack[2].m_obj;
uint8_t v___x_1728_ = stack[3].m_num;
lean_object* v___y_1729_ = stack[4].m_obj;
lean_object* v___y_1730_ = stack[5].m_obj;
lean_object* v___y_1731_ = stack[6].m_obj;
lean_object* v___y_1732_ = stack[7].m_obj;
lean_object* v_res_1755_;
v_res_1755_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1725_, v_declName_1726_, v_levelParams_1727_, v___x_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
stack->m_obj
 = v_res_1755_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1756_, lean_object* v_declName_1757_, lean_object* v_levelParams_1758_, lean_object* v___x_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
uint8_t v___x_23686__boxed_1765_; lean_object* v_res_1766_; 
v___x_23686__boxed_1765_ = lean_unbox(v___x_1759_);
v_res_1766_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1756_, v_declName_1757_, v_levelParams_1758_, v___x_23686__boxed_1765_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
if (lean_obj_tag(v_a_1767_) == 0)
{
lean_object* v___x_1769_; 
v___x_1769_ = l_List_reverse___redArg(v_a_1768_);
return v___x_1769_;
}
else
{
lean_object* v_head_1770_; lean_object* v_tail_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1780_; 
v_head_1770_ = lean_ctor_get(v_a_1767_, 0);
v_tail_1771_ = lean_ctor_get(v_a_1767_, 1);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_a_1767_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1773_ = v_a_1767_;
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_tail_1771_);
lean_inc(v_head_1770_);
lean_dec(v_a_1767_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1780_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
v___x_1775_ = l_Lean_mkLevelParam(v_head_1770_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 1, v_a_1768_);
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_a_1768_);
v___x_1777_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
v_a_1767_ = v_tail_1771_;
v_a_1768_ = v___x_1777_;
goto _start;
}
}
}
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object* v_msgData_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; lean_object* v_env_1788_; uint8_t v___x_1789_; lean_object* v_env_1790_; lean_object* v___x_1791_; lean_object* v_toCold_1792_; lean_object* v_mctx_1793_; lean_object* v_lctx_1794_; lean_object* v_options_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1787_ = lean_st_ref_get(v___y_1785_);
v_env_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc_ref(v_env_1788_);
lean_dec(v___x_1787_);
v___x_1789_ = 0;
v_env_1790_ = l_Lean_Environment_setRecordingDeps(v_env_1788_, v___x_1789_);
v___x_1791_ = lean_st_ref_get(v___y_1783_);
v_toCold_1792_ = lean_ctor_get(v___y_1784_, 0);
v_mctx_1793_ = lean_ctor_get(v___x_1791_, 0);
lean_inc_ref(v_mctx_1793_);
lean_dec(v___x_1791_);
v_lctx_1794_ = lean_ctor_get(v___y_1782_, 2);
v_options_1795_ = lean_ctor_get(v_toCold_1792_, 2);
lean_inc_ref(v_options_1795_);
lean_inc_ref(v_lctx_1794_);
v___x_1796_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1796_, 0, v_env_1790_);
lean_ctor_set(v___x_1796_, 1, v_mctx_1793_);
lean_ctor_set(v___x_1796_, 2, v_lctx_1794_);
lean_ctor_set(v___x_1796_, 3, v_options_1795_);
v___x_1797_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
lean_ctor_set(v___x_1797_, 1, v_msgData_1781_);
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1781_ = stack[0].m_obj;
lean_object* v___y_1782_ = stack[1].m_obj;
lean_object* v___y_1783_ = stack[2].m_obj;
lean_object* v___y_1784_ = stack[3].m_obj;
lean_object* v___y_1785_ = stack[4].m_obj;
lean_object* v_res_1799_;
v_res_1799_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
stack->m_obj
 = v_res_1799_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1806_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_ref_1813_; lean_object* v___x_1814_; lean_object* v_a_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1823_; 
v_ref_1813_ = lean_ctor_get(v___y_1810_, 2);
v___x_1814_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1823_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1817_ = v___x_1814_;
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_a_1815_);
lean_dec(v___x_1814_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1823_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
lean_inc(v_ref_1813_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v_ref_1813_);
lean_ctor_set(v___x_1819_, 1, v_a_1815_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set_tag(v___x_1817_, 1);
lean_ctor_set(v___x_1817_, 0, v___x_1819_);
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1807_ = stack[0].m_obj;
lean_object* v___y_1808_ = stack[1].m_obj;
lean_object* v___y_1809_ = stack[2].m_obj;
lean_object* v___y_1810_ = stack[3].m_obj;
lean_object* v___y_1811_ = stack[4].m_obj;
lean_object* v_res_1824_;
v_res_1824_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_);
stack->m_obj
 = v_res_1824_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1832_, lean_object* v_msg_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_toCold_1839_; lean_object* v_currRecDepth_1840_; lean_object* v_ref_1841_; uint16_t v_optionFlags_1842_; uint8_t v_suppressElabErrors_1843_; uint8_t v_isRecordingDeps_1844_; lean_object* v_ref_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v_toCold_1839_ = lean_ctor_get(v___y_1836_, 0);
v_currRecDepth_1840_ = lean_ctor_get(v___y_1836_, 1);
v_ref_1841_ = lean_ctor_get(v___y_1836_, 2);
v_optionFlags_1842_ = lean_ctor_get_uint16(v___y_1836_, sizeof(void*)*3);
v_suppressElabErrors_1843_ = lean_ctor_get_uint8(v___y_1836_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1844_ = lean_ctor_get_uint8(v___y_1836_, sizeof(void*)*3 + 3);
v_ref_1845_ = l_Lean_replaceRef(v_ref_1832_, v_ref_1841_);
lean_inc(v_currRecDepth_1840_);
lean_inc_ref(v_toCold_1839_);
v___x_1846_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1846_, 0, v_toCold_1839_);
lean_ctor_set(v___x_1846_, 1, v_currRecDepth_1840_);
lean_ctor_set(v___x_1846_, 2, v_ref_1845_);
lean_ctor_set_uint16(v___x_1846_, sizeof(void*)*3, v_optionFlags_1842_);
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*3 + 2, v_suppressElabErrors_1843_);
lean_ctor_set_uint8(v___x_1846_, sizeof(void*)*3 + 3, v_isRecordingDeps_1844_);
v___x_1847_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1833_, v___y_1834_, v___y_1835_, v___x_1846_, v___y_1837_);
lean_dec_ref_known(v___x_1846_, 3);
return v___x_1847_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1832_ = stack[0].m_obj;
lean_object* v_msg_1833_ = stack[1].m_obj;
lean_object* v___y_1834_ = stack[2].m_obj;
lean_object* v___y_1835_ = stack[3].m_obj;
lean_object* v___y_1836_ = stack[4].m_obj;
lean_object* v___y_1837_ = stack[5].m_obj;
lean_object* v_res_1848_;
v_res_1848_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1832_, v_msg_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
stack->m_obj
 = v_res_1848_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1849_, lean_object* v_msg_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1849_, v_msg_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v_ref_1849_);
return v_res_1856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1859_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1860_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
lean_ctor_set(v___x_1862_, 2, v___x_1861_);
lean_ctor_set(v___x_1862_, 3, v___x_1861_);
lean_ctor_set(v___x_1862_, 4, v___x_1860_);
lean_ctor_set(v___x_1862_, 5, v___x_1860_);
lean_ctor_set(v___x_1862_, 6, v___x_1860_);
lean_ctor_set(v___x_1862_, 7, v___x_1860_);
lean_ctor_set(v___x_1862_, 8, v___x_1860_);
lean_ctor_set(v___x_1862_, 9, v___x_1860_);
lean_ctor_set(v___x_1862_, 10, v___x_1860_);
lean_ctor_set(v___x_1862_, 11, v___x_1859_);
return v___x_1862_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_unsigned_to_nat(32u);
v___x_1864_ = lean_mk_empty_array_with_capacity(v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
return v___x_1865_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
size_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1866_ = ((size_t)5ULL);
v___x_1867_ = lean_unsigned_to_nat(0u);
v___x_1868_ = lean_unsigned_to_nat(32u);
v___x_1869_ = lean_mk_empty_array_with_capacity(v___x_1868_);
v___x_1870_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1871_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v___x_1869_);
lean_ctor_set(v___x_1871_, 2, v___x_1867_);
lean_ctor_set(v___x_1871_, 3, v___x_1867_);
lean_ctor_set_usize(v___x_1871_, 4, v___x_1866_);
return v___x_1871_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1872_ = lean_box(1);
v___x_1873_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1874_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1873_);
lean_ctor_set(v___x_1875_, 2, v___x_1872_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5));
v___x_1878_ = l_Lean_stringToMessageData(v___x_1877_);
return v___x_1878_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7));
v___x_1881_ = l_Lean_stringToMessageData(v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9));
v___x_1884_ = l_Lean_stringToMessageData(v___x_1883_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11));
v___x_1887_ = l_Lean_stringToMessageData(v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13));
v___x_1890_ = l_Lean_stringToMessageData(v___x_1889_);
return v___x_1890_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15));
v___x_1893_ = l_Lean_stringToMessageData(v___x_1892_);
return v___x_1893_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1895_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17));
v___x_1896_ = l_Lean_stringToMessageData(v___x_1895_);
return v___x_1896_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__20(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19));
v___x_1899_ = l_Lean_stringToMessageData(v___x_1898_);
return v___x_1899_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__22(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__21));
v___x_1902_ = l_Lean_stringToMessageData(v___x_1901_);
return v___x_1902_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__24(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__23));
v___x_1905_ = l_Lean_stringToMessageData(v___x_1904_);
return v___x_1905_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__26(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__25));
v___x_1908_ = l_Lean_stringToMessageData(v___x_1907_);
return v___x_1908_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1909_, lean_object* v_declHint_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v_env_1915_; uint8_t v___x_1916_; 
v___x_1913_ = lean_box(0);
v___x_1914_ = lean_st_ref_get(v___y_1911_);
v_env_1915_ = lean_ctor_get(v___x_1914_, 0);
lean_inc_ref(v_env_1915_);
lean_dec(v___x_1914_);
v___x_1916_ = l_Lean_Name_isAnonymous(v_declHint_1910_);
if (v___x_1916_ == 0)
{
uint8_t v_isExporting_1917_; 
v_isExporting_1917_ = lean_ctor_get_uint8(v_env_1915_, sizeof(void*)*13);
if (v_isExporting_1917_ == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref(v_env_1915_);
lean_dec(v_declHint_1910_);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_msg_1909_);
return v___x_1918_;
}
else
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
lean_inc_ref(v_env_1915_);
v___x_1919_ = l_Lean_Environment_setExporting(v_env_1915_, v___x_1916_);
lean_inc(v_declHint_1910_);
lean_inc_ref(v___x_1919_);
v___x_1920_ = l_Lean_Environment_contains(v___x_1919_, v_declHint_1910_, v_isExporting_1917_);
if (v___x_1920_ == 0)
{
lean_object* v___x_1921_; 
lean_dec_ref(v___x_1919_);
lean_dec_ref(v_env_1915_);
lean_dec(v_declHint_1910_);
v___x_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1921_, 0, v_msg_1909_);
return v___x_1921_;
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v_c_1927_; lean_object* v___x_1928_; 
v___x_1922_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1923_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1924_ = l_Lean_Options_empty;
v___x_1925_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1919_);
lean_ctor_set(v___x_1925_, 1, v___x_1922_);
lean_ctor_set(v___x_1925_, 2, v___x_1923_);
lean_ctor_set(v___x_1925_, 3, v___x_1924_);
lean_inc(v_declHint_1910_);
v___x_1926_ = l_Lean_MessageData_ofConstName(v_declHint_1910_, v___x_1916_);
v_c_1927_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1927_, 0, v___x_1925_);
lean_ctor_set(v_c_1927_, 1, v___x_1926_);
v___x_1928_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1915_, v_declHint_1910_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_dec_ref(v_env_1915_);
lean_dec(v_declHint_1910_);
v___x_1929_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
lean_ctor_set(v___x_1930_, 1, v_c_1927_);
v___x_1931_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = l_Lean_MessageData_note(v___x_1932_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_msg_1909_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
else
{
lean_object* v_val_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1992_; 
v_val_1936_ = lean_ctor_get(v___x_1928_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1938_ = v___x_1928_;
v_isShared_1939_ = v_isSharedCheck_1992_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_val_1936_);
lean_dec(v___x_1928_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1992_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v_modules_1941_; lean_object* v_moduleNames_1942_; lean_object* v_mod_1943_; uint8_t v___y_1945_; uint8_t v___x_1975_; 
v___x_1940_ = l_Lean_Environment_header(v_env_1915_);
lean_dec_ref(v_env_1915_);
v_modules_1941_ = lean_ctor_get(v___x_1940_, 3);
lean_inc_ref(v_modules_1941_);
v_moduleNames_1942_ = lean_ctor_get(v___x_1940_, 4);
lean_inc_ref(v_moduleNames_1942_);
lean_dec_ref(v___x_1940_);
v_mod_1943_ = lean_array_get(v___x_1913_, v_moduleNames_1942_, v_val_1936_);
lean_dec_ref(v_moduleNames_1942_);
v___x_1975_ = l_Lean_isPrivateName(v_declHint_1910_);
lean_dec(v_declHint_1910_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = lean_array_get_size(v_modules_1941_);
v___x_1977_ = lean_nat_dec_lt(v_val_1936_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_dec_ref(v_modules_1941_);
lean_dec(v_val_1936_);
v___y_1945_ = v___x_1975_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_1978_; lean_object* v_toImport_1979_; uint8_t v_isExported_1980_; 
v___x_1978_ = lean_array_fget(v_modules_1941_, v_val_1936_);
lean_dec(v_val_1936_);
lean_dec_ref(v_modules_1941_);
v_toImport_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc_ref(v_toImport_1979_);
lean_dec(v___x_1978_);
v_isExported_1980_ = lean_ctor_get_uint8(v_toImport_1979_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1979_);
v___y_1945_ = v_isExported_1980_;
goto v___jp_1944_;
}
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
lean_dec_ref(v_modules_1941_);
lean_del_object(v___x_1938_);
lean_dec(v_val_1936_);
v___x_1981_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v_c_1927_);
v___x_1983_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__24, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__24_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__24);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_MessageData_ofName(v_mod_1943_);
v___x_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__26, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__26_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__26);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = l_Lean_MessageData_note(v___x_1988_);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v_msg_1909_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
return v___x_1991_;
}
v___jp_1944_:
{
if (v___y_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1946_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v_c_1927_);
v___x_1948_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_MessageData_ofName(v_mod_1943_);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14);
v___x_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = l_Lean_MessageData_note(v___x_1953_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v_msg_1909_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set_tag(v___x_1938_, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1955_);
v___x_1957_ = v___x_1938_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
else
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v___x_1959_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16);
v___x_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v_c_1927_);
v___x_1961_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = l_Lean_MessageData_ofName(v_mod_1943_);
lean_inc_ref(v___x_1963_);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__20, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__20_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__20);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1964_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1966_);
lean_ctor_set(v___x_1967_, 1, v___x_1963_);
v___x_1968_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__22, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__22_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__22);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = l_Lean_MessageData_note(v___x_1969_);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v_msg_1909_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set_tag(v___x_1938_, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1971_);
v___x_1973_ = v___x_1938_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
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
lean_object* v___x_1993_; 
lean_dec_ref(v_env_1915_);
lean_dec(v_declHint_1910_);
v___x_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_msg_1909_);
return v___x_1993_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1909_ = stack[0].m_obj;
lean_object* v_declHint_1910_ = stack[1].m_obj;
lean_object* v___y_1911_ = stack[2].m_obj;
lean_object* v_res_1994_;
v_res_1994_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1909_, v_declHint_1910_, v___y_1911_);
stack->m_obj
 = v_res_1994_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1995_, lean_object* v_declHint_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1995_, v_declHint_1996_, v___y_1997_);
lean_dec(v___y_1997_);
return v_res_1999_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_2000_, lean_object* v_declHint_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v___x_2007_; lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2017_; 
v___x_2007_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2000_, v_declHint_2001_, v___y_2005_);
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2017_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2017_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; 
v___x_2012_ = l_Lean_unknownIdentifierMessageTag;
v___x_2013_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v_a_2008_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2013_);
v___x_2015_ = v___x_2010_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2013_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2000_ = stack[0].m_obj;
lean_object* v_declHint_2001_ = stack[1].m_obj;
lean_object* v___y_2002_ = stack[2].m_obj;
lean_object* v___y_2003_ = stack[3].m_obj;
lean_object* v___y_2004_ = stack[4].m_obj;
lean_object* v___y_2005_ = stack[5].m_obj;
lean_object* v_res_2018_;
v_res_2018_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_2000_, v_declHint_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
stack->m_obj
 = v_res_2018_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_2019_, lean_object* v_declHint_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_2019_, v_declHint_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2026_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_2027_, lean_object* v_msg_2028_, lean_object* v_declHint_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v___x_2035_; lean_object* v_a_2036_; lean_object* v___x_2037_; 
v___x_2035_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_2028_, v_declHint_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
lean_inc(v_a_2036_);
lean_dec_ref(v___x_2035_);
v___x_2037_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2027_, v_a_2036_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
return v___x_2037_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2027_ = stack[0].m_obj;
lean_object* v_msg_2028_ = stack[1].m_obj;
lean_object* v_declHint_2029_ = stack[2].m_obj;
lean_object* v___y_2030_ = stack[3].m_obj;
lean_object* v___y_2031_ = stack[4].m_obj;
lean_object* v___y_2032_ = stack[5].m_obj;
lean_object* v___y_2033_ = stack[6].m_obj;
lean_object* v_res_2038_;
v_res_2038_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2027_, v_msg_2028_, v_declHint_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
stack->m_obj
 = v_res_2038_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_2039_, lean_object* v_msg_2040_, lean_object* v_declHint_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2039_, v_msg_2040_, v_declHint_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v_ref_2039_);
return v_res_2047_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2049_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_2050_ = l_Lean_stringToMessageData(v___x_2049_);
return v___x_2050_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2052_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_2053_ = l_Lean_stringToMessageData(v___x_2052_);
return v___x_2053_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_2054_, lean_object* v_constName_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2061_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_2062_ = 0;
lean_inc(v_constName_2055_);
v___x_2063_ = l_Lean_MessageData_ofConstName(v_constName_2055_, v___x_2062_);
v___x_2064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2061_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2064_);
lean_ctor_set(v___x_2066_, 1, v___x_2065_);
v___x_2067_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2054_, v___x_2066_, v_constName_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
return v___x_2067_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2054_ = stack[0].m_obj;
lean_object* v_constName_2055_ = stack[1].m_obj;
lean_object* v___y_2056_ = stack[2].m_obj;
lean_object* v___y_2057_ = stack[3].m_obj;
lean_object* v___y_2058_ = stack[4].m_obj;
lean_object* v___y_2059_ = stack[5].m_obj;
lean_object* v_res_2068_;
v_res_2068_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2054_, v_constName_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_);
stack->m_obj
 = v_res_2068_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_2069_, lean_object* v_constName_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2069_, v_constName_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v_ref_2069_);
return v_res_2076_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_ref_2083_; lean_object* v___x_2084_; 
v_ref_2083_ = lean_ctor_get(v___y_2080_, 2);
v___x_2084_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2083_, v_constName_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
return v___x_2084_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2077_ = stack[0].m_obj;
lean_object* v___y_2078_ = stack[1].m_obj;
lean_object* v___y_2079_ = stack[2].m_obj;
lean_object* v___y_2080_ = stack[3].m_obj;
lean_object* v___y_2081_ = stack[4].m_obj;
lean_object* v_res_2085_;
v_res_2085_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
stack->m_obj
 = v_res_2085_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
return v_res_2092_;
}
}
lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v_env_2100_; uint8_t v___x_2101_; lean_object* v___x_2102_; 
v___x_2099_ = lean_st_ref_get(v___y_2097_);
v_env_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_ref(v_env_2100_);
lean_dec(v___x_2099_);
v___x_2101_ = 0;
lean_inc(v_constName_2093_);
v___x_2102_ = l_Lean_Environment_findConstVal_x3f(v_env_2100_, v_constName_2093_, v___x_2101_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
return v___x_2103_;
}
else
{
lean_object* v_val_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec(v_constName_2093_);
v_val_2104_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2102_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_val_2104_);
lean_dec(v___x_2102_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
lean_ctor_set_tag(v___x_2106_, 0);
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_val_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2093_ = stack[0].m_obj;
lean_object* v___y_2094_ = stack[1].m_obj;
lean_object* v___y_2095_ = stack[2].m_obj;
lean_object* v___y_2096_ = stack[3].m_obj;
lean_object* v___y_2097_ = stack[4].m_obj;
lean_object* v_res_2112_;
v_res_2112_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
stack->m_obj
 = v_res_2112_;
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
return v_res_2119_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2120_, uint8_t v_s_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; lean_object* v_env_2126_; lean_object* v_nextMacroScope_2127_; lean_object* v_ngen_2128_; lean_object* v_auxDeclNGen_2129_; lean_object* v_traceState_2130_; lean_object* v_recordedDeps_2131_; lean_object* v_messages_2132_; lean_object* v_infoState_2133_; lean_object* v_snapshotTasks_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2163_; 
v___x_2125_ = lean_st_ref_take(v___y_2123_);
v_env_2126_ = lean_ctor_get(v___x_2125_, 0);
v_nextMacroScope_2127_ = lean_ctor_get(v___x_2125_, 1);
v_ngen_2128_ = lean_ctor_get(v___x_2125_, 2);
v_auxDeclNGen_2129_ = lean_ctor_get(v___x_2125_, 3);
v_traceState_2130_ = lean_ctor_get(v___x_2125_, 4);
v_recordedDeps_2131_ = lean_ctor_get(v___x_2125_, 6);
v_messages_2132_ = lean_ctor_get(v___x_2125_, 7);
v_infoState_2133_ = lean_ctor_get(v___x_2125_, 8);
v_snapshotTasks_2134_ = lean_ctor_get(v___x_2125_, 9);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v___x_2125_, 5);
lean_dec(v_unused_2164_);
v___x_2136_ = v___x_2125_;
v_isShared_2137_ = v_isSharedCheck_2163_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_snapshotTasks_2134_);
lean_inc(v_infoState_2133_);
lean_inc(v_messages_2132_);
lean_inc(v_recordedDeps_2131_);
lean_inc(v_traceState_2130_);
lean_inc(v_auxDeclNGen_2129_);
lean_inc(v_ngen_2128_);
lean_inc(v_nextMacroScope_2127_);
lean_inc(v_env_2126_);
lean_dec(v___x_2125_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2163_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2143_; 
v___x_2138_ = 0;
v___x_2139_ = lean_box(0);
v___x_2140_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2126_, v_declName_2120_, v_s_2121_, v___x_2138_, v___x_2139_);
v___x_2141_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 5, v___x_2141_);
lean_ctor_set(v___x_2136_, 0, v___x_2140_);
v___x_2143_ = v___x_2136_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2140_);
lean_ctor_set(v_reuseFailAlloc_2162_, 1, v_nextMacroScope_2127_);
lean_ctor_set(v_reuseFailAlloc_2162_, 2, v_ngen_2128_);
lean_ctor_set(v_reuseFailAlloc_2162_, 3, v_auxDeclNGen_2129_);
lean_ctor_set(v_reuseFailAlloc_2162_, 4, v_traceState_2130_);
lean_ctor_set(v_reuseFailAlloc_2162_, 5, v___x_2141_);
lean_ctor_set(v_reuseFailAlloc_2162_, 6, v_recordedDeps_2131_);
lean_ctor_set(v_reuseFailAlloc_2162_, 7, v_messages_2132_);
lean_ctor_set(v_reuseFailAlloc_2162_, 8, v_infoState_2133_);
lean_ctor_set(v_reuseFailAlloc_2162_, 9, v_snapshotTasks_2134_);
v___x_2143_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v_mctx_2146_; lean_object* v_zetaDeltaFVarIds_2147_; lean_object* v_postponed_2148_; lean_object* v_diag_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2160_; 
v___x_2144_ = lean_st_ref_put(v___y_2123_, v___x_2143_);
v___x_2145_ = lean_st_ref_take(v___y_2122_);
v_mctx_2146_ = lean_ctor_get(v___x_2145_, 0);
v_zetaDeltaFVarIds_2147_ = lean_ctor_get(v___x_2145_, 2);
v_postponed_2148_ = lean_ctor_get(v___x_2145_, 3);
v_diag_2149_ = lean_ctor_get(v___x_2145_, 4);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2160_ == 0)
{
lean_object* v_unused_2161_; 
v_unused_2161_ = lean_ctor_get(v___x_2145_, 1);
lean_dec(v_unused_2161_);
v___x_2151_ = v___x_2145_;
v_isShared_2152_ = v_isSharedCheck_2160_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_diag_2149_);
lean_inc(v_postponed_2148_);
lean_inc(v_zetaDeltaFVarIds_2147_);
lean_inc(v_mctx_2146_);
lean_dec(v___x_2145_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2160_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v___x_2154_);
v___x_2156_ = v___x_2151_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_mctx_2146_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2154_);
lean_ctor_set(v_reuseFailAlloc_2159_, 2, v_zetaDeltaFVarIds_2147_);
lean_ctor_set(v_reuseFailAlloc_2159_, 3, v_postponed_2148_);
lean_ctor_set(v_reuseFailAlloc_2159_, 4, v_diag_2149_);
v___x_2156_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_st_ref_put(v___y_2122_, v___x_2156_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2153_);
return v___x_2158_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2120_ = stack[0].m_obj;
uint8_t v_s_2121_ = stack[1].m_num;
lean_object* v___y_2122_ = stack[2].m_obj;
lean_object* v___y_2123_ = stack[3].m_obj;
lean_object* v_res_2165_;
v_res_2165_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2120_, v_s_2121_, v___y_2122_, v___y_2123_);
stack->m_obj
 = v_res_2165_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2166_, lean_object* v_s_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v_s_boxed_2171_; lean_object* v_res_2172_; 
v_s_boxed_2171_ = lean_unbox(v_s_2167_);
v_res_2172_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2166_, v_s_boxed_2171_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec(v___y_2168_);
return v_res_2172_;
}
}
lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v___x_2179_; lean_object* v___x_2180_; 
v___x_2179_ = 0;
v___x_2180_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2173_, v___x_2179_, v___y_2175_, v___y_2177_);
return v___x_2180_;
}
}
LEAN_EXPORT void l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2173_ = stack[0].m_obj;
lean_object* v___y_2174_ = stack[1].m_obj;
lean_object* v___y_2175_ = stack[2].m_obj;
lean_object* v___y_2176_ = stack[3].m_obj;
lean_object* v___y_2177_ = stack[4].m_obj;
lean_object* v_res_2181_;
v_res_2181_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
stack->m_obj
 = v_res_2181_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2188_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2191_ = l_Lean_stringToMessageData(v___x_2190_);
return v___x_2191_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2193_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2194_ = l_Lean_stringToMessageData(v___x_2193_);
return v___x_2194_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2197_ = l_Lean_stringToMessageData(v___x_2196_);
return v___x_2197_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2198_, lean_object* v_declName_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; uint8_t v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; 
v___x_2205_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2206_ = l_Lean_MessageData_ofName(v_attrName_2198_);
v___x_2207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2205_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = 0;
v___x_2211_ = l_Lean_MessageData_ofConstName(v_declName_2199_, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2209_);
lean_ctor_set(v___x_2212_, 1, v___x_2211_);
v___x_2213_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2212_);
lean_ctor_set(v___x_2214_, 1, v___x_2213_);
v___x_2215_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2214_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
return v___x_2215_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2198_ = stack[0].m_obj;
lean_object* v_declName_2199_ = stack[1].m_obj;
lean_object* v___y_2200_ = stack[2].m_obj;
lean_object* v___y_2201_ = stack[3].m_obj;
lean_object* v___y_2202_ = stack[4].m_obj;
lean_object* v___y_2203_ = stack[5].m_obj;
lean_object* v_res_2216_;
v_res_2216_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2198_, v_declName_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
stack->m_obj
 = v_res_2216_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2217_, lean_object* v_declName_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2217_, v_declName_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0(lean_object* v_addEntryFn_2225_, lean_object* v_decl_2226_, lean_object* v_s_2227_){
_start:
{
lean_object* v_importedEntries_2228_; lean_object* v_state_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2237_; 
v_importedEntries_2228_ = lean_ctor_get(v_s_2227_, 0);
v_state_2229_ = lean_ctor_get(v_s_2227_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_s_2227_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2231_ = v_s_2227_;
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_state_2229_);
lean_inc(v_importedEntries_2228_);
lean_dec(v_s_2227_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_state_2233_; lean_object* v___x_2235_; 
v_state_2233_ = lean_apply_2(v_addEntryFn_2225_, v_state_2229_, v_decl_2226_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v_state_2233_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_importedEntries_2228_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_state_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2240_ = l_Lean_stringToMessageData(v___x_2239_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2242_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2243_ = l_Lean_stringToMessageData(v___x_2242_);
return v___x_2243_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2244_, lean_object* v_declName_2245_, lean_object* v_asyncPrefix_x3f_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___y_2253_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2246_) == 0)
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_MessageData_nil;
v___y_2253_ = v___x_2266_;
goto v___jp_2252_;
}
else
{
lean_object* v_val_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_val_2267_ = lean_ctor_get(v_asyncPrefix_x3f_2246_, 0);
lean_inc(v_val_2267_);
lean_dec_ref_known(v_asyncPrefix_x3f_2246_, 1);
v___x_2268_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2269_ = l_Lean_MessageData_ofName(v_val_2267_);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set(v___x_2272_, 1, v___x_2271_);
v___y_2253_ = v___x_2272_;
goto v___jp_2252_;
}
v___jp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2254_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2255_ = l_Lean_MessageData_ofName(v_attrName_2244_);
v___x_2256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2254_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2256_);
lean_ctor_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = 0;
v___x_2260_ = l_Lean_MessageData_ofConstName(v_declName_2245_, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2258_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2261_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v___x_2264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v___y_2253_);
v___x_2265_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2264_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
return v___x_2265_;
}
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2244_ = stack[0].m_obj;
lean_object* v_declName_2245_ = stack[1].m_obj;
lean_object* v_asyncPrefix_x3f_2246_ = stack[2].m_obj;
lean_object* v___y_2247_ = stack[3].m_obj;
lean_object* v___y_2248_ = stack[4].m_obj;
lean_object* v___y_2249_ = stack[5].m_obj;
lean_object* v___y_2250_ = stack[6].m_obj;
lean_object* v_res_2273_;
v_res_2273_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2244_, v_declName_2245_, v_asyncPrefix_x3f_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
stack->m_obj
 = v_res_2273_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2274_, lean_object* v_declName_2275_, lean_object* v_asyncPrefix_x3f_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2274_, v_declName_2275_, v_asyncPrefix_x3f_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2282_;
}
}
lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2283_, lean_object* v_decl_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v___y_2291_; lean_object* v___y_2292_; lean_object* v___y_2293_; lean_object* v___y_2294_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2323_; lean_object* v___y_2324_; lean_object* v___x_2345_; lean_object* v_env_2346_; lean_object* v___y_2348_; lean_object* v___y_2349_; lean_object* v___y_2350_; lean_object* v___y_2351_; lean_object* v___x_2361_; 
v___x_2345_ = lean_st_ref_get(v___y_2288_);
v_env_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc_ref(v_env_2346_);
lean_dec(v___x_2345_);
v___x_2361_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2346_, v_decl_2284_);
if (lean_obj_tag(v___x_2361_) == 0)
{
v___y_2348_ = v___y_2285_;
v___y_2349_ = v___y_2286_;
v___y_2350_ = v___y_2287_;
v___y_2351_ = v___y_2288_;
goto v___jp_2347_;
}
else
{
lean_object* v_attr_2362_; lean_object* v_toAttributeImplCore_2363_; lean_object* v_name_2364_; lean_object* v___x_2365_; 
lean_dec_ref_known(v___x_2361_, 1);
lean_dec_ref(v_env_2346_);
v_attr_2362_ = lean_ctor_get(v_attr_2283_, 0);
lean_inc_ref(v_attr_2362_);
lean_dec_ref(v_attr_2283_);
v_toAttributeImplCore_2363_ = lean_ctor_get(v_attr_2362_, 0);
lean_inc_ref(v_toAttributeImplCore_2363_);
lean_dec_ref(v_attr_2362_);
v_name_2364_ = lean_ctor_get(v_toAttributeImplCore_2363_, 1);
lean_inc(v_name_2364_);
lean_dec_ref(v_toAttributeImplCore_2363_);
v___x_2365_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2364_, v_decl_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
return v___x_2365_;
}
v___jp_2290_:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v_mctx_2306_; lean_object* v_zetaDeltaFVarIds_2307_; lean_object* v_postponed_2308_; lean_object* v_diag_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2320_; 
v___x_2302_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
v___x_2303_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2303_, 0, v___y_2301_);
lean_ctor_set(v___x_2303_, 1, v___y_2300_);
lean_ctor_set(v___x_2303_, 2, v___y_2299_);
lean_ctor_set(v___x_2303_, 3, v___y_2291_);
lean_ctor_set(v___x_2303_, 4, v___y_2296_);
lean_ctor_set(v___x_2303_, 5, v___x_2302_);
lean_ctor_set(v___x_2303_, 6, v___y_2293_);
lean_ctor_set(v___x_2303_, 7, v___y_2298_);
lean_ctor_set(v___x_2303_, 8, v___y_2294_);
lean_ctor_set(v___x_2303_, 9, v___y_2292_);
v___x_2304_ = lean_st_ref_put(v___y_2295_, v___x_2303_);
v___x_2305_ = lean_st_ref_take(v___y_2297_);
v_mctx_2306_ = lean_ctor_get(v___x_2305_, 0);
v_zetaDeltaFVarIds_2307_ = lean_ctor_get(v___x_2305_, 2);
v_postponed_2308_ = lean_ctor_get(v___x_2305_, 3);
v_diag_2309_ = lean_ctor_get(v___x_2305_, 4);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v___x_2305_, 1);
lean_dec(v_unused_2321_);
v___x_2311_ = v___x_2305_;
v_isShared_2312_ = v_isSharedCheck_2320_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_diag_2309_);
lean_inc(v_postponed_2308_);
lean_inc(v_zetaDeltaFVarIds_2307_);
lean_inc(v_mctx_2306_);
lean_dec(v___x_2305_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2320_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2313_ = lean_box(0);
v___x_2314_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v___x_2314_);
v___x_2316_ = v___x_2311_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_mctx_2306_);
lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2319_, 2, v_zetaDeltaFVarIds_2307_);
lean_ctor_set(v_reuseFailAlloc_2319_, 3, v_postponed_2308_);
lean_ctor_set(v_reuseFailAlloc_2319_, 4, v_diag_2309_);
v___x_2316_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_st_ref_put(v___y_2297_, v___x_2316_);
v___x_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2313_);
return v___x_2318_;
}
}
}
v___jp_2322_:
{
lean_object* v___x_2325_; lean_object* v_ext_2326_; lean_object* v_toEnvExtension_2327_; lean_object* v_env_2328_; lean_object* v_nextMacroScope_2329_; lean_object* v_ngen_2330_; lean_object* v_auxDeclNGen_2331_; lean_object* v_traceState_2332_; lean_object* v_recordedDeps_2333_; lean_object* v_messages_2334_; lean_object* v_infoState_2335_; lean_object* v_snapshotTasks_2336_; lean_object* v_addEntryFn_2337_; lean_object* v_asyncMode_2338_; uint8_t v_logWrites_2339_; lean_object* v___f_2340_; uint8_t v___x_2341_; 
v___x_2325_ = lean_st_ref_take(v___y_2324_);
v_ext_2326_ = lean_ctor_get(v_attr_2283_, 1);
lean_inc_ref(v_ext_2326_);
lean_dec_ref(v_attr_2283_);
v_toEnvExtension_2327_ = lean_ctor_get(v_ext_2326_, 0);
lean_inc_ref(v_toEnvExtension_2327_);
v_env_2328_ = lean_ctor_get(v___x_2325_, 0);
lean_inc_ref(v_env_2328_);
v_nextMacroScope_2329_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_nextMacroScope_2329_);
v_ngen_2330_ = lean_ctor_get(v___x_2325_, 2);
lean_inc_ref(v_ngen_2330_);
v_auxDeclNGen_2331_ = lean_ctor_get(v___x_2325_, 3);
lean_inc_ref(v_auxDeclNGen_2331_);
v_traceState_2332_ = lean_ctor_get(v___x_2325_, 4);
lean_inc_ref(v_traceState_2332_);
v_recordedDeps_2333_ = lean_ctor_get(v___x_2325_, 6);
lean_inc_ref(v_recordedDeps_2333_);
v_messages_2334_ = lean_ctor_get(v___x_2325_, 7);
lean_inc_ref(v_messages_2334_);
v_infoState_2335_ = lean_ctor_get(v___x_2325_, 8);
lean_inc_ref(v_infoState_2335_);
v_snapshotTasks_2336_ = lean_ctor_get(v___x_2325_, 9);
lean_inc_ref(v_snapshotTasks_2336_);
lean_dec(v___x_2325_);
v_addEntryFn_2337_ = lean_ctor_get(v_ext_2326_, 3);
lean_inc(v_addEntryFn_2337_);
lean_dec_ref(v_ext_2326_);
v_asyncMode_2338_ = lean_ctor_get(v_toEnvExtension_2327_, 2);
lean_inc(v_asyncMode_2338_);
v_logWrites_2339_ = lean_ctor_get_uint8(v_toEnvExtension_2327_, sizeof(void*)*6);
lean_inc(v_decl_2284_);
v___f_2340_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0), 3, 2);
lean_closure_set(v___f_2340_, 0, v_addEntryFn_2337_);
lean_closure_set(v___f_2340_, 1, v_decl_2284_);
v___x_2341_ = 1;
if (v_logWrites_2339_ == 0)
{
lean_object* v___x_2342_; 
v___x_2342_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2327_, v_env_2328_, v___f_2340_, v_asyncMode_2338_, v_decl_2284_, v___x_2341_);
lean_dec(v_asyncMode_2338_);
v___y_2291_ = v_auxDeclNGen_2331_;
v___y_2292_ = v_snapshotTasks_2336_;
v___y_2293_ = v_recordedDeps_2333_;
v___y_2294_ = v_infoState_2335_;
v___y_2295_ = v___y_2324_;
v___y_2296_ = v_traceState_2332_;
v___y_2297_ = v___y_2323_;
v___y_2298_ = v_messages_2334_;
v___y_2299_ = v_ngen_2330_;
v___y_2300_ = v_nextMacroScope_2329_;
v___y_2301_ = v___x_2342_;
goto v___jp_2290_;
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_inc_ref(v_toEnvExtension_2327_);
v___x_2343_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2327_, v_env_2328_);
lean_dec_ref(v_env_2328_);
v___x_2344_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2327_, v___x_2343_, v___f_2340_, v_asyncMode_2338_, v_decl_2284_, v___x_2341_);
lean_dec(v_asyncMode_2338_);
v___y_2291_ = v_auxDeclNGen_2331_;
v___y_2292_ = v_snapshotTasks_2336_;
v___y_2293_ = v_recordedDeps_2333_;
v___y_2294_ = v_infoState_2335_;
v___y_2295_ = v___y_2324_;
v___y_2296_ = v_traceState_2332_;
v___y_2297_ = v___y_2323_;
v___y_2298_ = v_messages_2334_;
v___y_2299_ = v_ngen_2330_;
v___y_2300_ = v_nextMacroScope_2329_;
v___y_2301_ = v___x_2344_;
goto v___jp_2290_;
}
}
v___jp_2347_:
{
lean_object* v_ext_2352_; lean_object* v_toEnvExtension_2353_; lean_object* v_attr_2354_; lean_object* v_asyncMode_2355_; uint8_t v___x_2356_; 
v_ext_2352_ = lean_ctor_get(v_attr_2283_, 1);
v_toEnvExtension_2353_ = lean_ctor_get(v_ext_2352_, 0);
v_attr_2354_ = lean_ctor_get(v_attr_2283_, 0);
v_asyncMode_2355_ = lean_ctor_get(v_toEnvExtension_2353_, 2);
lean_inc(v_decl_2284_);
lean_inc_ref(v_env_2346_);
v___x_2356_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2346_, v_decl_2284_, v_asyncMode_2355_);
if (v___x_2356_ == 0)
{
lean_object* v_toAttributeImplCore_2357_; lean_object* v_name_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
lean_inc_ref(v_attr_2354_);
lean_dec_ref(v_attr_2283_);
v_toAttributeImplCore_2357_ = lean_ctor_get(v_attr_2354_, 0);
lean_inc_ref(v_toAttributeImplCore_2357_);
lean_dec_ref(v_attr_2354_);
v_name_2358_ = lean_ctor_get(v_toAttributeImplCore_2357_, 1);
lean_inc(v_name_2358_);
lean_dec_ref(v_toAttributeImplCore_2357_);
v___x_2359_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2346_);
v___x_2360_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2358_, v_decl_2284_, v___x_2359_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
return v___x_2360_;
}
else
{
lean_dec_ref(v_env_2346_);
v___y_2323_ = v___y_2349_;
v___y_2324_ = v___y_2351_;
goto v___jp_2322_;
}
}
}
}
LEAN_EXPORT void l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_attr_2283_ = stack[0].m_obj;
lean_object* v_decl_2284_ = stack[1].m_obj;
lean_object* v___y_2285_ = stack[2].m_obj;
lean_object* v___y_2286_ = stack[3].m_obj;
lean_object* v___y_2287_ = stack[4].m_obj;
lean_object* v___y_2288_ = stack[5].m_obj;
lean_object* v_res_2366_;
v_res_2366_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2283_, v_decl_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
stack->m_obj
 = v_res_2366_;
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2367_, lean_object* v_decl_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2367_, v_decl_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
return v_res_2374_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; lean_object* v_env_2382_; uint8_t v___x_2383_; lean_object* v___x_2384_; 
v___x_2381_ = lean_st_ref_get(v___y_2379_);
v_env_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc_ref(v_env_2382_);
lean_dec(v___x_2381_);
v___x_2383_ = 0;
lean_inc(v_constName_2375_);
v___x_2384_ = l_Lean_Environment_find_x3f(v_env_2382_, v_constName_2375_, v___x_2383_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2385_;
}
else
{
lean_object* v_val_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
lean_dec(v_constName_2375_);
v_val_2386_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2384_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_val_2386_);
lean_dec(v___x_2384_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
lean_ctor_set_tag(v___x_2388_, 0);
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_val_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2375_ = stack[0].m_obj;
lean_object* v___y_2376_ = stack[1].m_obj;
lean_object* v___y_2377_ = stack[2].m_obj;
lean_object* v___y_2378_ = stack[3].m_obj;
lean_object* v___y_2379_ = stack[4].m_obj;
lean_object* v_res_2394_;
v_res_2394_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
stack->m_obj
 = v_res_2394_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_res_2401_; 
v_res_2401_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2395_, v___y_2396_, v___y_2397_, v___y_2398_, v___y_2399_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
return v_res_2401_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2405_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2406_ = lean_unsigned_to_nat(58u);
v___x_2407_ = lean_unsigned_to_nat(33u);
v___x_2408_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2409_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2410_ = l_mkPanicMessageWithDecl(v___x_2409_, v___x_2408_, v___x_2407_, v___x_2406_, v___x_2405_);
return v___x_2410_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2412_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2413_ = lean_unsigned_to_nat(60u);
v___x_2414_ = lean_unsigned_to_nat(30u);
v___x_2415_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2416_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2417_ = l_mkPanicMessageWithDecl(v___x_2416_, v___x_2415_, v___x_2414_, v___x_2413_, v___x_2412_);
return v___x_2417_;
}
}
lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2418_, lean_object* v_indName_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2425_; 
lean_inc(v_indName_2419_);
v___x_2425_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
if (lean_obj_tag(v_a_2426_) == 5)
{
lean_object* v_val_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2617_; 
v_val_2427_ = lean_ctor_get(v_a_2426_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v_a_2426_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2429_ = v_a_2426_;
v_isShared_2430_ = v_isSharedCheck_2617_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_val_2427_);
lean_dec(v_a_2426_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2617_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; 
lean_inc(v_indName_2419_);
v___x_2431_ = l_Lean_mkCasesOnName(v_indName_2419_);
lean_inc(v___x_2431_);
v___x_2432_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2431_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v_name_2434_; lean_object* v_levelParams_2435_; lean_object* v_type_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v_name_2434_ = lean_ctor_get(v_a_2433_, 0);
lean_inc(v_name_2434_);
v_levelParams_2435_ = lean_ctor_get(v_a_2433_, 1);
lean_inc_n(v_levelParams_2435_, 2);
v_type_2436_ = lean_ctor_get(v_a_2433_, 2);
lean_inc_ref(v_type_2436_);
lean_dec(v_a_2433_);
v___x_2437_ = lean_box(0);
v___x_2438_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2435_, v___x_2437_);
if (lean_obj_tag(v___x_2438_) == 1)
{
lean_object* v_head_2439_; lean_object* v_tail_2440_; lean_object* v_numParams_2441_; lean_object* v_numIndices_2442_; lean_object* v_ctors_2443_; lean_object* v___f_2444_; lean_object* v___x_2446_; 
v_head_2439_ = lean_ctor_get(v___x_2438_, 0);
lean_inc(v_head_2439_);
v_tail_2440_ = lean_ctor_get(v___x_2438_, 1);
lean_inc(v_tail_2440_);
v_numParams_2441_ = lean_ctor_get(v_val_2427_, 1);
lean_inc_n(v_numParams_2441_, 2);
v_numIndices_2442_ = lean_ctor_get(v_val_2427_, 2);
lean_inc(v_numIndices_2442_);
v_ctors_2443_ = lean_ctor_get(v_val_2427_, 4);
lean_inc(v_ctors_2443_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2444_, 0, v_numIndices_2442_);
lean_closure_set(v___f_2444_, 1, v_head_2439_);
lean_closure_set(v___f_2444_, 2, v_ctors_2443_);
lean_closure_set(v___f_2444_, 3, v_indName_2419_);
lean_closure_set(v___f_2444_, 4, v_tail_2440_);
lean_closure_set(v___f_2444_, 5, v_name_2434_);
lean_closure_set(v___f_2444_, 6, v___x_2438_);
lean_closure_set(v___f_2444_, 7, v_numParams_2441_);
lean_closure_set(v___f_2444_, 8, v_val_2427_);
lean_closure_set(v___f_2444_, 9, v___x_2431_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set_tag(v___x_2429_, 1);
lean_ctor_set(v___x_2429_, 0, v_numParams_2441_);
v___x_2446_ = v___x_2429_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_numParams_2441_);
v___x_2446_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
uint8_t v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = 0;
v___x_2448_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2436_, v___x_2446_, v___f_2444_, v___x_2447_, v___x_2447_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2450_; lean_object* v___f_2451_; uint8_t v___y_2453_; uint8_t v___x_2596_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v___x_2450_ = lean_box(v___x_2447_);
lean_inc(v_declName_2418_);
v___f_2451_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2451_, 0, v_a_2449_);
lean_closure_set(v___f_2451_, 1, v_declName_2418_);
lean_closure_set(v___f_2451_, 2, v_levelParams_2435_);
lean_closure_set(v___f_2451_, 3, v___x_2450_);
v___x_2596_ = l_Lean_isPrivateName(v_declName_2418_);
if (v___x_2596_ == 0)
{
uint8_t v___x_2597_; 
v___x_2597_ = 1;
v___y_2453_ = v___x_2597_;
goto v___jp_2452_;
}
else
{
v___y_2453_ = v___x_2447_;
goto v___jp_2452_;
}
v___jp_2452_:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2451_, v___y_2453_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v___x_2455_; lean_object* v_env_2456_; lean_object* v_nextMacroScope_2457_; lean_object* v_ngen_2458_; lean_object* v_auxDeclNGen_2459_; lean_object* v_traceState_2460_; lean_object* v_recordedDeps_2461_; lean_object* v_messages_2462_; lean_object* v_infoState_2463_; lean_object* v_snapshotTasks_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2594_; 
lean_dec_ref_known(v___x_2454_, 1);
v___x_2455_ = lean_st_ref_take(v_a_2423_);
v_env_2456_ = lean_ctor_get(v___x_2455_, 0);
v_nextMacroScope_2457_ = lean_ctor_get(v___x_2455_, 1);
v_ngen_2458_ = lean_ctor_get(v___x_2455_, 2);
v_auxDeclNGen_2459_ = lean_ctor_get(v___x_2455_, 3);
v_traceState_2460_ = lean_ctor_get(v___x_2455_, 4);
v_recordedDeps_2461_ = lean_ctor_get(v___x_2455_, 6);
v_messages_2462_ = lean_ctor_get(v___x_2455_, 7);
v_infoState_2463_ = lean_ctor_get(v___x_2455_, 8);
v_snapshotTasks_2464_ = lean_ctor_get(v___x_2455_, 9);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v___x_2455_, 5);
lean_dec(v_unused_2595_);
v___x_2466_ = v___x_2455_;
v_isShared_2467_ = v_isSharedCheck_2594_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_snapshotTasks_2464_);
lean_inc(v_infoState_2463_);
lean_inc(v_messages_2462_);
lean_inc(v_recordedDeps_2461_);
lean_inc(v_traceState_2460_);
lean_inc(v_auxDeclNGen_2459_);
lean_inc(v_ngen_2458_);
lean_inc(v_nextMacroScope_2457_);
lean_inc(v_env_2456_);
lean_dec(v___x_2455_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2594_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
lean_inc(v_declName_2418_);
v___x_2468_ = l_Lean_Meta_markMatcherLike(v_env_2456_, v_declName_2418_);
v___x_2469_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 5, v___x_2469_);
lean_ctor_set(v___x_2466_, 0, v___x_2468_);
v___x_2471_ = v___x_2466_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2468_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_nextMacroScope_2457_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v_ngen_2458_);
lean_ctor_set(v_reuseFailAlloc_2593_, 3, v_auxDeclNGen_2459_);
lean_ctor_set(v_reuseFailAlloc_2593_, 4, v_traceState_2460_);
lean_ctor_set(v_reuseFailAlloc_2593_, 5, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2593_, 6, v_recordedDeps_2461_);
lean_ctor_set(v_reuseFailAlloc_2593_, 7, v_messages_2462_);
lean_ctor_set(v_reuseFailAlloc_2593_, 8, v_infoState_2463_);
lean_ctor_set(v_reuseFailAlloc_2593_, 9, v_snapshotTasks_2464_);
v___x_2471_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v_mctx_2474_; lean_object* v_zetaDeltaFVarIds_2475_; lean_object* v_postponed_2476_; lean_object* v_diag_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2591_; 
v___x_2472_ = lean_st_ref_put(v_a_2423_, v___x_2471_);
v___x_2473_ = lean_st_ref_take(v_a_2421_);
v_mctx_2474_ = lean_ctor_get(v___x_2473_, 0);
v_zetaDeltaFVarIds_2475_ = lean_ctor_get(v___x_2473_, 2);
v_postponed_2476_ = lean_ctor_get(v___x_2473_, 3);
v_diag_2477_ = lean_ctor_get(v___x_2473_, 4);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2591_ == 0)
{
lean_object* v_unused_2592_; 
v_unused_2592_ = lean_ctor_get(v___x_2473_, 1);
lean_dec(v_unused_2592_);
v___x_2479_ = v___x_2473_;
v_isShared_2480_ = v_isSharedCheck_2591_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_diag_2477_);
lean_inc(v_postponed_2476_);
lean_inc(v_zetaDeltaFVarIds_2475_);
lean_inc(v_mctx_2474_);
lean_dec(v___x_2473_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2591_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 1, v___x_2481_);
v___x_2483_ = v___x_2479_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_mctx_2474_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2590_, 2, v_zetaDeltaFVarIds_2475_);
lean_ctor_set(v_reuseFailAlloc_2590_, 3, v_postponed_2476_);
lean_ctor_set(v_reuseFailAlloc_2590_, 4, v_diag_2477_);
v___x_2483_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v_env_2486_; lean_object* v_nextMacroScope_2487_; lean_object* v_ngen_2488_; lean_object* v_auxDeclNGen_2489_; lean_object* v_traceState_2490_; lean_object* v_recordedDeps_2491_; lean_object* v_messages_2492_; lean_object* v_infoState_2493_; lean_object* v_snapshotTasks_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2588_; 
v___x_2484_ = lean_st_ref_put(v_a_2421_, v___x_2483_);
v___x_2485_ = lean_st_ref_take(v_a_2423_);
v_env_2486_ = lean_ctor_get(v___x_2485_, 0);
v_nextMacroScope_2487_ = lean_ctor_get(v___x_2485_, 1);
v_ngen_2488_ = lean_ctor_get(v___x_2485_, 2);
v_auxDeclNGen_2489_ = lean_ctor_get(v___x_2485_, 3);
v_traceState_2490_ = lean_ctor_get(v___x_2485_, 4);
v_recordedDeps_2491_ = lean_ctor_get(v___x_2485_, 6);
v_messages_2492_ = lean_ctor_get(v___x_2485_, 7);
v_infoState_2493_ = lean_ctor_get(v___x_2485_, 8);
v_snapshotTasks_2494_ = lean_ctor_get(v___x_2485_, 9);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v___x_2485_, 5);
lean_dec(v_unused_2589_);
v___x_2496_ = v___x_2485_;
v_isShared_2497_ = v_isSharedCheck_2588_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_snapshotTasks_2494_);
lean_inc(v_infoState_2493_);
lean_inc(v_messages_2492_);
lean_inc(v_recordedDeps_2491_);
lean_inc(v_traceState_2490_);
lean_inc(v_auxDeclNGen_2489_);
lean_inc(v_ngen_2488_);
lean_inc(v_nextMacroScope_2487_);
lean_inc(v_env_2486_);
lean_dec(v___x_2485_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2588_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2500_; 
lean_inc(v_declName_2418_);
v___x_2498_ = l_Lean_markAuxRecursor(v_env_2486_, v_declName_2418_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 5, v___x_2469_);
lean_ctor_set(v___x_2496_, 0, v___x_2498_);
v___x_2500_ = v___x_2496_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_nextMacroScope_2487_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v_ngen_2488_);
lean_ctor_set(v_reuseFailAlloc_2587_, 3, v_auxDeclNGen_2489_);
lean_ctor_set(v_reuseFailAlloc_2587_, 4, v_traceState_2490_);
lean_ctor_set(v_reuseFailAlloc_2587_, 5, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2587_, 6, v_recordedDeps_2491_);
lean_ctor_set(v_reuseFailAlloc_2587_, 7, v_messages_2492_);
lean_ctor_set(v_reuseFailAlloc_2587_, 8, v_infoState_2493_);
lean_ctor_set(v_reuseFailAlloc_2587_, 9, v_snapshotTasks_2494_);
v___x_2500_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_mctx_2503_; lean_object* v_zetaDeltaFVarIds_2504_; lean_object* v_postponed_2505_; lean_object* v_diag_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2585_; 
v___x_2501_ = lean_st_ref_put(v_a_2423_, v___x_2500_);
v___x_2502_ = lean_st_ref_take(v_a_2421_);
v_mctx_2503_ = lean_ctor_get(v___x_2502_, 0);
v_zetaDeltaFVarIds_2504_ = lean_ctor_get(v___x_2502_, 2);
v_postponed_2505_ = lean_ctor_get(v___x_2502_, 3);
v_diag_2506_ = lean_ctor_get(v___x_2502_, 4);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v___x_2502_, 1);
lean_dec(v_unused_2586_);
v___x_2508_ = v___x_2502_;
v_isShared_2509_ = v_isSharedCheck_2585_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_diag_2506_);
lean_inc(v_postponed_2505_);
lean_inc(v_zetaDeltaFVarIds_2504_);
lean_inc(v_mctx_2503_);
lean_dec(v___x_2502_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2585_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v___x_2481_);
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_mctx_2503_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2584_, 2, v_zetaDeltaFVarIds_2504_);
lean_ctor_set(v_reuseFailAlloc_2584_, 3, v_postponed_2505_);
lean_ctor_set(v_reuseFailAlloc_2584_, 4, v_diag_2506_);
v___x_2511_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v_env_2514_; lean_object* v_nextMacroScope_2515_; lean_object* v_ngen_2516_; lean_object* v_auxDeclNGen_2517_; lean_object* v_traceState_2518_; lean_object* v_recordedDeps_2519_; lean_object* v_messages_2520_; lean_object* v_infoState_2521_; lean_object* v_snapshotTasks_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2582_; 
v___x_2512_ = lean_st_ref_put(v_a_2421_, v___x_2511_);
v___x_2513_ = lean_st_ref_take(v_a_2423_);
v_env_2514_ = lean_ctor_get(v___x_2513_, 0);
v_nextMacroScope_2515_ = lean_ctor_get(v___x_2513_, 1);
v_ngen_2516_ = lean_ctor_get(v___x_2513_, 2);
v_auxDeclNGen_2517_ = lean_ctor_get(v___x_2513_, 3);
v_traceState_2518_ = lean_ctor_get(v___x_2513_, 4);
v_recordedDeps_2519_ = lean_ctor_get(v___x_2513_, 6);
v_messages_2520_ = lean_ctor_get(v___x_2513_, 7);
v_infoState_2521_ = lean_ctor_get(v___x_2513_, 8);
v_snapshotTasks_2522_ = lean_ctor_get(v___x_2513_, 9);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; 
v_unused_2583_ = lean_ctor_get(v___x_2513_, 5);
lean_dec(v_unused_2583_);
v___x_2524_ = v___x_2513_;
v_isShared_2525_ = v_isSharedCheck_2582_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_snapshotTasks_2522_);
lean_inc(v_infoState_2521_);
lean_inc(v_messages_2520_);
lean_inc(v_recordedDeps_2519_);
lean_inc(v_traceState_2518_);
lean_inc(v_auxDeclNGen_2517_);
lean_inc(v_ngen_2516_);
lean_inc(v_nextMacroScope_2515_);
lean_inc(v_env_2514_);
lean_dec(v___x_2513_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2582_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___x_2528_; 
lean_inc(v_declName_2418_);
v___x_2526_ = l_Lean_Meta_addToCompletionBlackList(v_env_2514_, v_declName_2418_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 5, v___x_2469_);
lean_ctor_set(v___x_2524_, 0, v___x_2526_);
v___x_2528_ = v___x_2524_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2526_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_nextMacroScope_2515_);
lean_ctor_set(v_reuseFailAlloc_2581_, 2, v_ngen_2516_);
lean_ctor_set(v_reuseFailAlloc_2581_, 3, v_auxDeclNGen_2517_);
lean_ctor_set(v_reuseFailAlloc_2581_, 4, v_traceState_2518_);
lean_ctor_set(v_reuseFailAlloc_2581_, 5, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2581_, 6, v_recordedDeps_2519_);
lean_ctor_set(v_reuseFailAlloc_2581_, 7, v_messages_2520_);
lean_ctor_set(v_reuseFailAlloc_2581_, 8, v_infoState_2521_);
lean_ctor_set(v_reuseFailAlloc_2581_, 9, v_snapshotTasks_2522_);
v___x_2528_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_mctx_2531_; lean_object* v_zetaDeltaFVarIds_2532_; lean_object* v_postponed_2533_; lean_object* v_diag_2534_; lean_object* v___x_2536_; uint8_t v_isShared_2537_; uint8_t v_isSharedCheck_2579_; 
v___x_2529_ = lean_st_ref_put(v_a_2423_, v___x_2528_);
v___x_2530_ = lean_st_ref_take(v_a_2421_);
v_mctx_2531_ = lean_ctor_get(v___x_2530_, 0);
v_zetaDeltaFVarIds_2532_ = lean_ctor_get(v___x_2530_, 2);
v_postponed_2533_ = lean_ctor_get(v___x_2530_, 3);
v_diag_2534_ = lean_ctor_get(v___x_2530_, 4);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v___x_2530_, 1);
lean_dec(v_unused_2580_);
v___x_2536_ = v___x_2530_;
v_isShared_2537_ = v_isSharedCheck_2579_;
goto v_resetjp_2535_;
}
else
{
lean_inc(v_diag_2534_);
lean_inc(v_postponed_2533_);
lean_inc(v_zetaDeltaFVarIds_2532_);
lean_inc(v_mctx_2531_);
lean_dec(v___x_2530_);
v___x_2536_ = lean_box(0);
v_isShared_2537_ = v_isSharedCheck_2579_;
goto v_resetjp_2535_;
}
v_resetjp_2535_:
{
lean_object* v___x_2539_; 
if (v_isShared_2537_ == 0)
{
lean_ctor_set(v___x_2536_, 1, v___x_2481_);
v___x_2539_ = v___x_2536_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_mctx_2531_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2578_, 2, v_zetaDeltaFVarIds_2532_);
lean_ctor_set(v_reuseFailAlloc_2578_, 3, v_postponed_2533_);
lean_ctor_set(v_reuseFailAlloc_2578_, 4, v_diag_2534_);
v___x_2539_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v_env_2542_; lean_object* v_nextMacroScope_2543_; lean_object* v_ngen_2544_; lean_object* v_auxDeclNGen_2545_; lean_object* v_traceState_2546_; lean_object* v_recordedDeps_2547_; lean_object* v_messages_2548_; lean_object* v_infoState_2549_; lean_object* v_snapshotTasks_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2576_; 
v___x_2540_ = lean_st_ref_put(v_a_2421_, v___x_2539_);
v___x_2541_ = lean_st_ref_take(v_a_2423_);
v_env_2542_ = lean_ctor_get(v___x_2541_, 0);
v_nextMacroScope_2543_ = lean_ctor_get(v___x_2541_, 1);
v_ngen_2544_ = lean_ctor_get(v___x_2541_, 2);
v_auxDeclNGen_2545_ = lean_ctor_get(v___x_2541_, 3);
v_traceState_2546_ = lean_ctor_get(v___x_2541_, 4);
v_recordedDeps_2547_ = lean_ctor_get(v___x_2541_, 6);
v_messages_2548_ = lean_ctor_get(v___x_2541_, 7);
v_infoState_2549_ = lean_ctor_get(v___x_2541_, 8);
v_snapshotTasks_2550_ = lean_ctor_get(v___x_2541_, 9);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2576_ == 0)
{
lean_object* v_unused_2577_; 
v_unused_2577_ = lean_ctor_get(v___x_2541_, 5);
lean_dec(v_unused_2577_);
v___x_2552_ = v___x_2541_;
v_isShared_2553_ = v_isSharedCheck_2576_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_snapshotTasks_2550_);
lean_inc(v_infoState_2549_);
lean_inc(v_messages_2548_);
lean_inc(v_recordedDeps_2547_);
lean_inc(v_traceState_2546_);
lean_inc(v_auxDeclNGen_2545_);
lean_inc(v_ngen_2544_);
lean_inc(v_nextMacroScope_2543_);
lean_inc(v_env_2542_);
lean_dec(v___x_2541_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2576_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2556_; 
lean_inc(v_declName_2418_);
v___x_2554_ = l_Lean_addProtected(v_env_2542_, v_declName_2418_);
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 5, v___x_2469_);
lean_ctor_set(v___x_2552_, 0, v___x_2554_);
v___x_2556_ = v___x_2552_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2554_);
lean_ctor_set(v_reuseFailAlloc_2575_, 1, v_nextMacroScope_2543_);
lean_ctor_set(v_reuseFailAlloc_2575_, 2, v_ngen_2544_);
lean_ctor_set(v_reuseFailAlloc_2575_, 3, v_auxDeclNGen_2545_);
lean_ctor_set(v_reuseFailAlloc_2575_, 4, v_traceState_2546_);
lean_ctor_set(v_reuseFailAlloc_2575_, 5, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2575_, 6, v_recordedDeps_2547_);
lean_ctor_set(v_reuseFailAlloc_2575_, 7, v_messages_2548_);
lean_ctor_set(v_reuseFailAlloc_2575_, 8, v_infoState_2549_);
lean_ctor_set(v_reuseFailAlloc_2575_, 9, v_snapshotTasks_2550_);
v___x_2556_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v_mctx_2559_; lean_object* v_zetaDeltaFVarIds_2560_; lean_object* v_postponed_2561_; lean_object* v_diag_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2573_; 
v___x_2557_ = lean_st_ref_put(v_a_2423_, v___x_2556_);
v___x_2558_ = lean_st_ref_take(v_a_2421_);
v_mctx_2559_ = lean_ctor_get(v___x_2558_, 0);
v_zetaDeltaFVarIds_2560_ = lean_ctor_get(v___x_2558_, 2);
v_postponed_2561_ = lean_ctor_get(v___x_2558_, 3);
v_diag_2562_ = lean_ctor_get(v___x_2558_, 4);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2573_ == 0)
{
lean_object* v_unused_2574_; 
v_unused_2574_ = lean_ctor_get(v___x_2558_, 1);
lean_dec(v_unused_2574_);
v___x_2564_ = v___x_2558_;
v_isShared_2565_ = v_isSharedCheck_2573_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_diag_2562_);
lean_inc(v_postponed_2561_);
lean_inc(v_zetaDeltaFVarIds_2560_);
lean_inc(v_mctx_2559_);
lean_dec(v___x_2558_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2573_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 1, v___x_2481_);
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_mctx_2559_);
lean_ctor_set(v_reuseFailAlloc_2572_, 1, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_zetaDeltaFVarIds_2560_);
lean_ctor_set(v_reuseFailAlloc_2572_, 3, v_postponed_2561_);
lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_diag_2562_);
v___x_2567_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = lean_st_ref_put(v_a_2421_, v___x_2567_);
v___x_2569_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2418_);
v___x_2570_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2569_, v_declName_2418_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2571_; 
lean_dec_ref_known(v___x_2570_, 1);
v___x_2571_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2418_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
return v___x_2571_;
}
else
{
lean_dec(v_declName_2418_);
return v___x_2570_;
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
lean_dec(v_declName_2418_);
return v___x_2454_;
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_levelParams_2435_);
lean_dec(v_declName_2418_);
v_a_2598_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2448_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2448_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
lean_dec(v___x_2438_);
lean_dec_ref(v_type_2436_);
lean_dec(v_levelParams_2435_);
lean_dec(v_name_2434_);
lean_dec(v___x_2431_);
lean_del_object(v___x_2429_);
lean_dec_ref(v_val_2427_);
lean_dec(v_indName_2419_);
lean_dec(v_declName_2418_);
v___x_2607_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2608_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2607_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
return v___x_2608_;
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v___x_2431_);
lean_del_object(v___x_2429_);
lean_dec_ref(v_val_2427_);
lean_dec(v_indName_2419_);
lean_dec(v_declName_2418_);
v_a_2609_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2432_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2432_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
}
else
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_dec(v_a_2426_);
lean_dec(v_indName_2419_);
lean_dec(v_declName_2418_);
v___x_2618_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2619_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2618_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
return v___x_2619_;
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec(v_indName_2419_);
lean_dec(v_declName_2418_);
v_a_2620_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2425_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2425_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtorHet_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2418_ = stack[0].m_obj;
lean_object* v_indName_2419_ = stack[1].m_obj;
lean_object* v_a_2420_ = stack[2].m_obj;
lean_object* v_a_2421_ = stack[3].m_obj;
lean_object* v_a_2422_ = stack[4].m_obj;
lean_object* v_a_2423_ = stack[5].m_obj;
lean_object* v_res_2628_;
v_res_2628_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2418_, v_indName_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_);
stack->m_obj
 = v_res_2628_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2629_, lean_object* v_indName_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2629_, v_indName_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
return v_res_2636_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2637_, lean_object* v_name_2638_, lean_object* v_type_2639_, lean_object* v_k_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2638_, v_type_2639_, v_k_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_2638_ = stack[1].m_obj;
lean_object* v_type_2639_ = stack[2].m_obj;
lean_object* v_k_2640_ = stack[3].m_obj;
lean_object* v___y_2641_ = stack[4].m_obj;
lean_object* v___y_2642_ = stack[5].m_obj;
lean_object* v___y_2643_ = stack[6].m_obj;
lean_object* v___y_2644_ = stack[7].m_obj;
lean_object* v_res_2647_;
v_res_2647_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_box(0), v_name_2638_, v_type_2639_, v_k_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
stack->m_obj
 = v_res_2647_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2648_, lean_object* v_name_2649_, lean_object* v_type_2650_, lean_object* v_k_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2648_, v_name_2649_, v_type_2650_, v_k_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
return v_res_2657_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2658_, lean_object* v_params_2659_, lean_object* v_alts_2660_, lean_object* v___x_2661_, lean_object* v_ism2_2662_, lean_object* v_motive_2663_, lean_object* v_val_2664_, lean_object* v_indName_2665_, lean_object* v___x_2666_, lean_object* v___x_2667_, lean_object* v___x_2668_, lean_object* v_as_2669_, size_t v_sz_2670_, size_t v_i_2671_, lean_object* v_bs_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2658_, v_params_2659_, v_alts_2660_, v___x_2661_, v_ism2_2662_, v_motive_2663_, v_val_2664_, v_indName_2665_, v___x_2666_, v___x_2667_, v___x_2668_, v_sz_2670_, v_i_2671_, v_bs_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
return v___x_2678_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_2658_ = stack[0].m_obj;
lean_object* v_params_2659_ = stack[1].m_obj;
lean_object* v_alts_2660_ = stack[2].m_obj;
lean_object* v___x_2661_ = stack[3].m_obj;
lean_object* v_ism2_2662_ = stack[4].m_obj;
lean_object* v_motive_2663_ = stack[5].m_obj;
lean_object* v_val_2664_ = stack[6].m_obj;
lean_object* v_indName_2665_ = stack[7].m_obj;
lean_object* v___x_2666_ = stack[8].m_obj;
lean_object* v___x_2667_ = stack[9].m_obj;
lean_object* v___x_2668_ = stack[10].m_obj;
lean_object* v_as_2669_ = stack[11].m_obj;
size_t v_sz_2670_ = stack[12].m_num;
size_t v_i_2671_ = stack[13].m_num;
lean_object* v_bs_2672_ = stack[14].m_obj;
lean_object* v___y_2673_ = stack[15].m_obj;
lean_object* v___y_2674_ = stack[16].m_obj;
lean_object* v___y_2675_ = stack[17].m_obj;
lean_object* v___y_2676_ = stack[18].m_obj;
lean_object* v_res_2679_;
v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2658_, v_params_2659_, v_alts_2660_, v___x_2661_, v_ism2_2662_, v_motive_2663_, v_val_2664_, v_indName_2665_, v___x_2666_, v___x_2667_, v___x_2668_, v_as_2669_, v_sz_2670_, v_i_2671_, v_bs_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
stack->m_obj
 = v_res_2679_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2680_ = _args[0];
lean_object* v_params_2681_ = _args[1];
lean_object* v_alts_2682_ = _args[2];
lean_object* v___x_2683_ = _args[3];
lean_object* v_ism2_2684_ = _args[4];
lean_object* v_motive_2685_ = _args[5];
lean_object* v_val_2686_ = _args[6];
lean_object* v_indName_2687_ = _args[7];
lean_object* v___x_2688_ = _args[8];
lean_object* v___x_2689_ = _args[9];
lean_object* v___x_2690_ = _args[10];
lean_object* v_as_2691_ = _args[11];
lean_object* v_sz_2692_ = _args[12];
lean_object* v_i_2693_ = _args[13];
lean_object* v_bs_2694_ = _args[14];
lean_object* v___y_2695_ = _args[15];
lean_object* v___y_2696_ = _args[16];
lean_object* v___y_2697_ = _args[17];
lean_object* v___y_2698_ = _args[18];
lean_object* v___y_2699_ = _args[19];
_start:
{
size_t v_sz_boxed_2700_; size_t v_i_boxed_2701_; lean_object* v_res_2702_; 
v_sz_boxed_2700_ = lean_unbox_usize(v_sz_2692_);
lean_dec(v_sz_2692_);
v_i_boxed_2701_ = lean_unbox_usize(v_i_2693_);
lean_dec(v_i_2693_);
v_res_2702_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2680_, v_params_2681_, v_alts_2682_, v___x_2683_, v_ism2_2684_, v_motive_2685_, v_val_2686_, v_indName_2687_, v___x_2688_, v___x_2689_, v___x_2690_, v_as_2691_, v_sz_boxed_2700_, v_i_boxed_2701_, v_bs_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec_ref(v_as_2691_);
return v_res_2702_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2703_, lean_object* v_params_2704_, lean_object* v___x_2705_, lean_object* v_motive_2706_, lean_object* v_as_2707_, size_t v_sz_2708_, size_t v_i_2709_, lean_object* v_bs_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v___x_2716_; 
v___x_2716_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2703_, v_params_2704_, v___x_2705_, v_motive_2706_, v_sz_2708_, v_i_2709_, v_bs_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
return v___x_2716_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_2703_ = stack[0].m_obj;
lean_object* v_params_2704_ = stack[1].m_obj;
lean_object* v___x_2705_ = stack[2].m_obj;
lean_object* v_motive_2706_ = stack[3].m_obj;
lean_object* v_as_2707_ = stack[4].m_obj;
size_t v_sz_2708_ = stack[5].m_num;
size_t v_i_2709_ = stack[6].m_num;
lean_object* v_bs_2710_ = stack[7].m_obj;
lean_object* v___y_2711_ = stack[8].m_obj;
lean_object* v___y_2712_ = stack[9].m_obj;
lean_object* v___y_2713_ = stack[10].m_obj;
lean_object* v___y_2714_ = stack[11].m_obj;
lean_object* v_res_2717_;
v_res_2717_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2703_, v_params_2704_, v___x_2705_, v_motive_2706_, v_as_2707_, v_sz_2708_, v_i_2709_, v_bs_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
stack->m_obj
 = v_res_2717_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2718_, lean_object* v_params_2719_, lean_object* v___x_2720_, lean_object* v_motive_2721_, lean_object* v_as_2722_, lean_object* v_sz_2723_, lean_object* v_i_2724_, lean_object* v_bs_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
size_t v_sz_boxed_2731_; size_t v_i_boxed_2732_; lean_object* v_res_2733_; 
v_sz_boxed_2731_ = lean_unbox_usize(v_sz_2723_);
lean_dec(v_sz_2723_);
v_i_boxed_2732_ = lean_unbox_usize(v_i_2724_);
lean_dec(v_i_2724_);
v_res_2733_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2718_, v_params_2719_, v___x_2720_, v_motive_2721_, v_as_2722_, v_sz_boxed_2731_, v_i_boxed_2732_, v_bs_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec_ref(v_as_2722_);
lean_dec_ref(v_params_2719_);
return v_res_2733_;
}
}
lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2734_, uint8_t v_s_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2734_, v_s_2735_, v___y_2737_, v___y_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT void l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2734_ = stack[0].m_obj;
uint8_t v_s_2735_ = stack[1].m_num;
lean_object* v___y_2736_ = stack[2].m_obj;
lean_object* v___y_2737_ = stack[3].m_obj;
lean_object* v___y_2738_ = stack[4].m_obj;
lean_object* v___y_2739_ = stack[5].m_obj;
lean_object* v_res_2742_;
v_res_2742_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2734_, v_s_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
stack->m_obj
 = v_res_2742_;
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2743_, lean_object* v_s_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
uint8_t v_s_boxed_2750_; lean_object* v_res_2751_; 
v_s_boxed_2750_ = lean_unbox(v_s_2744_);
v_res_2751_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2743_, v_s_boxed_2750_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2751_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2752_, lean_object* v_constName_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
return v___x_2759_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2753_ = stack[1].m_obj;
lean_object* v___y_2754_ = stack[2].m_obj;
lean_object* v___y_2755_ = stack[3].m_obj;
lean_object* v___y_2756_ = stack[4].m_obj;
lean_object* v___y_2757_ = stack[5].m_obj;
lean_object* v_res_2760_;
v_res_2760_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_box(0), v_constName_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_);
stack->m_obj
 = v_res_2760_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2761_, lean_object* v_constName_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2761_, v_constName_2762_, v___y_2763_, v___y_2764_, v___y_2765_, v___y_2766_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
lean_dec(v___y_2764_);
lean_dec_ref(v___y_2763_);
return v_res_2768_;
}
}
lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2769_, lean_object* v_attrName_2770_, lean_object* v_declName_2771_, lean_object* v_asyncPrefix_x3f_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2770_, v_declName_2771_, v_asyncPrefix_x3f_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
return v___x_2778_;
}
}
LEAN_EXPORT void l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2770_ = stack[1].m_obj;
lean_object* v_declName_2771_ = stack[2].m_obj;
lean_object* v_asyncPrefix_x3f_2772_ = stack[3].m_obj;
lean_object* v___y_2773_ = stack[4].m_obj;
lean_object* v___y_2774_ = stack[5].m_obj;
lean_object* v___y_2775_ = stack[6].m_obj;
lean_object* v___y_2776_ = stack[7].m_obj;
lean_object* v_res_2779_;
v_res_2779_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_box(0), v_attrName_2770_, v_declName_2771_, v_asyncPrefix_x3f_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_);
stack->m_obj
 = v_res_2779_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2780_, lean_object* v_attrName_2781_, lean_object* v_declName_2782_, lean_object* v_asyncPrefix_x3f_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2780_, v_attrName_2781_, v_declName_2782_, v_asyncPrefix_x3f_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
return v_res_2789_;
}
}
lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2790_, lean_object* v_attrName_2791_, lean_object* v_declName_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2791_, v_declName_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT void l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_attrName_2791_ = stack[1].m_obj;
lean_object* v_declName_2792_ = stack[2].m_obj;
lean_object* v___y_2793_ = stack[3].m_obj;
lean_object* v___y_2794_ = stack[4].m_obj;
lean_object* v___y_2795_ = stack[5].m_obj;
lean_object* v___y_2796_ = stack[6].m_obj;
lean_object* v_res_2799_;
v_res_2799_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_box(0), v_attrName_2791_, v_declName_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_);
stack->m_obj
 = v_res_2799_;
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2800_, lean_object* v_attrName_2801_, lean_object* v_declName_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2800_, v_attrName_2801_, v_declName_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2808_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2809_, lean_object* v_ref_2810_, lean_object* v_constName_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2810_, v_constName_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
return v___x_2817_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2810_ = stack[1].m_obj;
lean_object* v_constName_2811_ = stack[2].m_obj;
lean_object* v___y_2812_ = stack[3].m_obj;
lean_object* v___y_2813_ = stack[4].m_obj;
lean_object* v___y_2814_ = stack[5].m_obj;
lean_object* v___y_2815_ = stack[6].m_obj;
lean_object* v_res_2818_;
v_res_2818_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_box(0), v_ref_2810_, v_constName_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
stack->m_obj
 = v_res_2818_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2819_, lean_object* v_ref_2820_, lean_object* v_constName_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2819_, v_ref_2820_, v_constName_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v_ref_2820_);
return v_res_2827_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2828_, lean_object* v_msg_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
return v___x_2835_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2829_ = stack[1].m_obj;
lean_object* v___y_2830_ = stack[2].m_obj;
lean_object* v___y_2831_ = stack[3].m_obj;
lean_object* v___y_2832_ = stack[4].m_obj;
lean_object* v___y_2833_ = stack[5].m_obj;
lean_object* v_res_2836_;
v_res_2836_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_box(0), v_msg_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_);
stack->m_obj
 = v_res_2836_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2837_, lean_object* v_msg_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2837_, v_msg_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec(v___y_2842_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
return v_res_2844_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2845_, lean_object* v_ref_2846_, lean_object* v_msg_2847_, lean_object* v_declHint_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2846_, v_msg_2847_, v_declHint_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2846_ = stack[1].m_obj;
lean_object* v_msg_2847_ = stack[2].m_obj;
lean_object* v_declHint_2848_ = stack[3].m_obj;
lean_object* v___y_2849_ = stack[4].m_obj;
lean_object* v___y_2850_ = stack[5].m_obj;
lean_object* v___y_2851_ = stack[6].m_obj;
lean_object* v___y_2852_ = stack[7].m_obj;
lean_object* v_res_2855_;
v_res_2855_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_box(0), v_ref_2846_, v_msg_2847_, v_declHint_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
stack->m_obj
 = v_res_2855_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2856_, lean_object* v_ref_2857_, lean_object* v_msg_2858_, lean_object* v_declHint_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2856_, v_ref_2857_, v_msg_2858_, v_declHint_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec_ref(v___y_2862_);
lean_dec(v___y_2861_);
lean_dec_ref(v___y_2860_);
lean_dec(v_ref_2857_);
return v_res_2865_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2866_, lean_object* v_declHint_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2866_, v_declHint_2867_, v___y_2871_);
return v___x_2873_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2866_ = stack[0].m_obj;
lean_object* v_declHint_2867_ = stack[1].m_obj;
lean_object* v___y_2868_ = stack[2].m_obj;
lean_object* v___y_2869_ = stack[3].m_obj;
lean_object* v___y_2870_ = stack[4].m_obj;
lean_object* v___y_2871_ = stack[5].m_obj;
lean_object* v_res_2874_;
v_res_2874_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2866_, v_declHint_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
stack->m_obj
 = v_res_2874_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2875_, lean_object* v_declHint_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2875_, v_declHint_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2882_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2883_, lean_object* v_ref_2884_, lean_object* v_msg_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2884_, v_msg_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2884_ = stack[1].m_obj;
lean_object* v_msg_2885_ = stack[2].m_obj;
lean_object* v___y_2886_ = stack[3].m_obj;
lean_object* v___y_2887_ = stack[4].m_obj;
lean_object* v___y_2888_ = stack[5].m_obj;
lean_object* v___y_2889_ = stack[6].m_obj;
lean_object* v_res_2892_;
v_res_2892_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_box(0), v_ref_2884_, v_msg_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
stack->m_obj
 = v_res_2892_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2893_, lean_object* v_ref_2894_, lean_object* v_msg_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2893_, v_ref_2894_, v_msg_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v_ref_2894_);
return v_res_2901_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2902_, lean_object* v___y_2903_){
_start:
{
uint8_t v___x_2905_; 
v___x_2905_ = l_Lean_Expr_hasMVar(v_e_2902_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_e_2902_);
return v___x_2906_;
}
else
{
lean_object* v___x_2907_; lean_object* v_mctx_2908_; lean_object* v___x_2909_; lean_object* v_fst_2910_; lean_object* v_snd_2911_; lean_object* v___x_2912_; lean_object* v_cache_2913_; lean_object* v_zetaDeltaFVarIds_2914_; lean_object* v_postponed_2915_; lean_object* v_diag_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2925_; 
v___x_2907_ = lean_st_ref_get(v___y_2903_);
v_mctx_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc_ref(v_mctx_2908_);
lean_dec(v___x_2907_);
v___x_2909_ = l_Lean_instantiateMVarsCore(v_mctx_2908_, v_e_2902_);
v_fst_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_fst_2910_);
v_snd_2911_ = lean_ctor_get(v___x_2909_, 1);
lean_inc(v_snd_2911_);
lean_dec_ref(v___x_2909_);
v___x_2912_ = lean_st_ref_take(v___y_2903_);
v_cache_2913_ = lean_ctor_get(v___x_2912_, 1);
v_zetaDeltaFVarIds_2914_ = lean_ctor_get(v___x_2912_, 2);
v_postponed_2915_ = lean_ctor_get(v___x_2912_, 3);
v_diag_2916_ = lean_ctor_get(v___x_2912_, 4);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2925_ == 0)
{
lean_object* v_unused_2926_; 
v_unused_2926_ = lean_ctor_get(v___x_2912_, 0);
lean_dec(v_unused_2926_);
v___x_2918_ = v___x_2912_;
v_isShared_2919_ = v_isSharedCheck_2925_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_diag_2916_);
lean_inc(v_postponed_2915_);
lean_inc(v_zetaDeltaFVarIds_2914_);
lean_inc(v_cache_2913_);
lean_dec(v___x_2912_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2925_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
lean_ctor_set(v___x_2918_, 0, v_snd_2911_);
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_snd_2911_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_cache_2913_);
lean_ctor_set(v_reuseFailAlloc_2924_, 2, v_zetaDeltaFVarIds_2914_);
lean_ctor_set(v_reuseFailAlloc_2924_, 3, v_postponed_2915_);
lean_ctor_set(v_reuseFailAlloc_2924_, 4, v_diag_2916_);
v___x_2921_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_st_ref_put(v___y_2903_, v___x_2921_);
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_fst_2910_);
return v___x_2923_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2902_ = stack[0].m_obj;
lean_object* v___y_2903_ = stack[1].m_obj;
lean_object* v_res_2927_;
v_res_2927_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2902_, v___y_2903_);
stack->m_obj
 = v_res_2927_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2928_, v___y_2929_);
lean_dec(v___y_2929_);
return v_res_2931_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2932_, v___y_2934_);
return v___x_2938_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2932_ = stack[0].m_obj;
lean_object* v___y_2933_ = stack[1].m_obj;
lean_object* v___y_2934_ = stack[2].m_obj;
lean_object* v___y_2935_ = stack[3].m_obj;
lean_object* v___y_2936_ = stack[4].m_obj;
lean_object* v_res_2939_;
v_res_2939_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
stack->m_obj
 = v_res_2939_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
return v_res_2946_;
}
}
lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2947_, lean_object* v_info_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2952_; lean_object* v_env_2953_; lean_object* v_nextMacroScope_2954_; lean_object* v_ngen_2955_; lean_object* v_auxDeclNGen_2956_; lean_object* v_traceState_2957_; lean_object* v_recordedDeps_2958_; lean_object* v_messages_2959_; lean_object* v_infoState_2960_; lean_object* v_snapshotTasks_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2988_; 
v___x_2952_ = lean_st_ref_take(v___y_2950_);
v_env_2953_ = lean_ctor_get(v___x_2952_, 0);
v_nextMacroScope_2954_ = lean_ctor_get(v___x_2952_, 1);
v_ngen_2955_ = lean_ctor_get(v___x_2952_, 2);
v_auxDeclNGen_2956_ = lean_ctor_get(v___x_2952_, 3);
v_traceState_2957_ = lean_ctor_get(v___x_2952_, 4);
v_recordedDeps_2958_ = lean_ctor_get(v___x_2952_, 6);
v_messages_2959_ = lean_ctor_get(v___x_2952_, 7);
v_infoState_2960_ = lean_ctor_get(v___x_2952_, 8);
v_snapshotTasks_2961_ = lean_ctor_get(v___x_2952_, 9);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2988_ == 0)
{
lean_object* v_unused_2989_; 
v_unused_2989_ = lean_ctor_get(v___x_2952_, 5);
lean_dec(v_unused_2989_);
v___x_2963_ = v___x_2952_;
v_isShared_2964_ = v_isSharedCheck_2988_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_snapshotTasks_2961_);
lean_inc(v_infoState_2960_);
lean_inc(v_messages_2959_);
lean_inc(v_recordedDeps_2958_);
lean_inc(v_traceState_2957_);
lean_inc(v_auxDeclNGen_2956_);
lean_inc(v_ngen_2955_);
lean_inc(v_nextMacroScope_2954_);
lean_inc(v_env_2953_);
lean_dec(v___x_2952_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2988_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2968_; 
v___x_2965_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2953_, v_matcherName_2947_, v_info_2948_);
v___x_2966_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 5, v___x_2966_);
lean_ctor_set(v___x_2963_, 0, v___x_2965_);
v___x_2968_ = v___x_2963_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v___x_2965_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_nextMacroScope_2954_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_ngen_2955_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_auxDeclNGen_2956_);
lean_ctor_set(v_reuseFailAlloc_2987_, 4, v_traceState_2957_);
lean_ctor_set(v_reuseFailAlloc_2987_, 5, v___x_2966_);
lean_ctor_set(v_reuseFailAlloc_2987_, 6, v_recordedDeps_2958_);
lean_ctor_set(v_reuseFailAlloc_2987_, 7, v_messages_2959_);
lean_ctor_set(v_reuseFailAlloc_2987_, 8, v_infoState_2960_);
lean_ctor_set(v_reuseFailAlloc_2987_, 9, v_snapshotTasks_2961_);
v___x_2968_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v_mctx_2971_; lean_object* v_zetaDeltaFVarIds_2972_; lean_object* v_postponed_2973_; lean_object* v_diag_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2985_; 
v___x_2969_ = lean_st_ref_put(v___y_2950_, v___x_2968_);
v___x_2970_ = lean_st_ref_take(v___y_2949_);
v_mctx_2971_ = lean_ctor_get(v___x_2970_, 0);
v_zetaDeltaFVarIds_2972_ = lean_ctor_get(v___x_2970_, 2);
v_postponed_2973_ = lean_ctor_get(v___x_2970_, 3);
v_diag_2974_ = lean_ctor_get(v___x_2970_, 4);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2985_ == 0)
{
lean_object* v_unused_2986_; 
v_unused_2986_ = lean_ctor_get(v___x_2970_, 1);
lean_dec(v_unused_2986_);
v___x_2976_ = v___x_2970_;
v_isShared_2977_ = v_isSharedCheck_2985_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_diag_2974_);
lean_inc(v_postponed_2973_);
lean_inc(v_zetaDeltaFVarIds_2972_);
lean_inc(v_mctx_2971_);
lean_dec(v___x_2970_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2985_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2981_; 
v___x_2978_ = lean_box(0);
v___x_2979_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 1, v___x_2979_);
v___x_2981_ = v___x_2976_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_mctx_2971_);
lean_ctor_set(v_reuseFailAlloc_2984_, 1, v___x_2979_);
lean_ctor_set(v_reuseFailAlloc_2984_, 2, v_zetaDeltaFVarIds_2972_);
lean_ctor_set(v_reuseFailAlloc_2984_, 3, v_postponed_2973_);
lean_ctor_set(v_reuseFailAlloc_2984_, 4, v_diag_2974_);
v___x_2981_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; 
v___x_2982_ = lean_st_ref_put(v___y_2949_, v___x_2981_);
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2978_);
return v___x_2983_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherName_2947_ = stack[0].m_obj;
lean_object* v_info_2948_ = stack[1].m_obj;
lean_object* v___y_2949_ = stack[2].m_obj;
lean_object* v___y_2950_ = stack[3].m_obj;
lean_object* v_res_2990_;
v_res_2990_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2947_, v_info_2948_, v___y_2949_, v___y_2950_);
stack->m_obj
 = v_res_2990_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2991_, lean_object* v_info_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2991_, v_info_2992_, v___y_2993_, v___y_2994_);
lean_dec(v___y_2994_);
lean_dec(v___y_2993_);
return v_res_2996_;
}
}
lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2997_, lean_object* v_info_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2997_, v_info_2998_, v___y_3000_, v___y_3002_);
return v___x_3004_;
}
}
LEAN_EXPORT void l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherName_2997_ = stack[0].m_obj;
lean_object* v_info_2998_ = stack[1].m_obj;
lean_object* v___y_2999_ = stack[2].m_obj;
lean_object* v___y_3000_ = stack[3].m_obj;
lean_object* v___y_3001_ = stack[4].m_obj;
lean_object* v___y_3002_ = stack[5].m_obj;
lean_object* v_res_3005_;
v_res_3005_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2997_, v_info_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_);
stack->m_obj
 = v_res_3005_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_3006_, lean_object* v_info_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_3006_, v_info_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_);
lean_dec(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec(v___y_3009_);
lean_dec_ref(v___y_3008_);
return v_res_3013_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_3014_, lean_object* v___x_3015_, lean_object* v_newEqs1_3016_, uint8_t v___x_3017_, uint8_t v___x_3018_, uint8_t v___x_3019_, lean_object* v_ism1_x27_3020_, lean_object* v_ism2_x27_3021_, lean_object* v_newRefls1_3022_, lean_object* v_newEqs2_3023_, lean_object* v_newRefls2_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = l_Lean_mkAppN(v_motive_3014_, v___x_3015_);
v___x_3031_ = l_Array_append___redArg(v_newEqs1_3016_, v_newEqs2_3023_);
v___x_3032_ = l_Lean_Meta_mkForallFVars(v___x_3031_, v___x_3030_, v___x_3017_, v___x_3018_, v___x_3018_, v___x_3019_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec_ref(v___x_3031_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = l_Array_append___redArg(v_ism1_x27_3020_, v_ism2_x27_3021_);
v___x_3035_ = l_Lean_Meta_mkLambdaFVars(v___x_3034_, v_a_3033_, v___x_3017_, v___x_3018_, v___x_3017_, v___x_3018_, v___x_3019_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec_ref(v___x_3034_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3045_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3045_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3045_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3043_; 
v___x_3040_ = l_Array_append___redArg(v_newRefls1_3022_, v_newRefls2_3024_);
v___x_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3041_, 0, v_a_3036_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3041_);
v___x_3043_ = v___x_3038_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec_ref(v_newRefls1_3022_);
v_a_3046_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3035_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3035_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v_newRefls1_3022_);
lean_dec_ref(v_ism1_x27_3020_);
v_a_3054_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3032_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3032_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_motive_3014_ = stack[0].m_obj;
lean_object* v___x_3015_ = stack[1].m_obj;
lean_object* v_newEqs1_3016_ = stack[2].m_obj;
uint8_t v___x_3017_ = stack[3].m_num;
uint8_t v___x_3018_ = stack[4].m_num;
uint8_t v___x_3019_ = stack[5].m_num;
lean_object* v_ism1_x27_3020_ = stack[6].m_obj;
lean_object* v_ism2_x27_3021_ = stack[7].m_obj;
lean_object* v_newRefls1_3022_ = stack[8].m_obj;
lean_object* v_newEqs2_3023_ = stack[9].m_obj;
lean_object* v_newRefls2_3024_ = stack[10].m_obj;
lean_object* v___y_3025_ = stack[11].m_obj;
lean_object* v___y_3026_ = stack[12].m_obj;
lean_object* v___y_3027_ = stack[13].m_obj;
lean_object* v___y_3028_ = stack[14].m_obj;
lean_object* v_res_3062_;
v_res_3062_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_3014_, v___x_3015_, v_newEqs1_3016_, v___x_3017_, v___x_3018_, v___x_3019_, v_ism1_x27_3020_, v_ism2_x27_3021_, v_newRefls1_3022_, v_newEqs2_3023_, v_newRefls2_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
stack->m_obj
 = v_res_3062_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_3063_, lean_object* v___x_3064_, lean_object* v_newEqs1_3065_, lean_object* v___x_3066_, lean_object* v___x_3067_, lean_object* v___x_3068_, lean_object* v_ism1_x27_3069_, lean_object* v_ism2_x27_3070_, lean_object* v_newRefls1_3071_, lean_object* v_newEqs2_3072_, lean_object* v_newRefls2_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
uint8_t v___x_15033__boxed_3079_; uint8_t v___x_15034__boxed_3080_; uint8_t v___x_15035__boxed_3081_; lean_object* v_res_3082_; 
v___x_15033__boxed_3079_ = lean_unbox(v___x_3066_);
v___x_15034__boxed_3080_ = lean_unbox(v___x_3067_);
v___x_15035__boxed_3081_ = lean_unbox(v___x_3068_);
v_res_3082_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_3063_, v___x_3064_, v_newEqs1_3065_, v___x_15033__boxed_3079_, v___x_15034__boxed_3080_, v___x_15035__boxed_3081_, v_ism1_x27_3069_, v_ism2_x27_3070_, v_newRefls1_3071_, v_newEqs2_3072_, v_newRefls2_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec_ref(v_newRefls2_3073_);
lean_dec_ref(v_newEqs2_3072_);
lean_dec_ref(v_ism2_x27_3070_);
lean_dec_ref(v___x_3064_);
return v_res_3082_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_3083_, lean_object* v___x_3084_, uint8_t v___x_3085_, uint8_t v___x_3086_, uint8_t v___x_3087_, lean_object* v_ism1_x27_3088_, lean_object* v_ism2_x27_3089_, lean_object* v_is_3090_, lean_object* v___x_3091_, lean_object* v_newEqs1_3092_, lean_object* v_newRefls1_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___f_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3099_ = lean_box(v___x_3085_);
v___x_3100_ = lean_box(v___x_3086_);
v___x_3101_ = lean_box(v___x_3087_);
lean_inc_ref(v_ism2_x27_3089_);
v___f_3102_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3102_, 0, v_motive_3083_);
lean_closure_set(v___f_3102_, 1, v___x_3084_);
lean_closure_set(v___f_3102_, 2, v_newEqs1_3092_);
lean_closure_set(v___f_3102_, 3, v___x_3099_);
lean_closure_set(v___f_3102_, 4, v___x_3100_);
lean_closure_set(v___f_3102_, 5, v___x_3101_);
lean_closure_set(v___f_3102_, 6, v_ism1_x27_3088_);
lean_closure_set(v___f_3102_, 7, v_ism2_x27_3089_);
lean_closure_set(v___f_3102_, 8, v_newRefls1_3093_);
v___x_3103_ = lean_array_push(v_is_3090_, v___x_3091_);
v___x_3104_ = l_Lean_Meta_withNewEqs___redArg(v___x_3103_, v_ism2_x27_3089_, v___f_3102_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
return v___x_3104_;
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_motive_3083_ = stack[0].m_obj;
lean_object* v___x_3084_ = stack[1].m_obj;
uint8_t v___x_3085_ = stack[2].m_num;
uint8_t v___x_3086_ = stack[3].m_num;
uint8_t v___x_3087_ = stack[4].m_num;
lean_object* v_ism1_x27_3088_ = stack[5].m_obj;
lean_object* v_ism2_x27_3089_ = stack[6].m_obj;
lean_object* v_is_3090_ = stack[7].m_obj;
lean_object* v___x_3091_ = stack[8].m_obj;
lean_object* v_newEqs1_3092_ = stack[9].m_obj;
lean_object* v_newRefls1_3093_ = stack[10].m_obj;
lean_object* v___y_3094_ = stack[11].m_obj;
lean_object* v___y_3095_ = stack[12].m_obj;
lean_object* v___y_3096_ = stack[13].m_obj;
lean_object* v___y_3097_ = stack[14].m_obj;
lean_object* v_res_3105_;
v_res_3105_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_3083_, v___x_3084_, v___x_3085_, v___x_3086_, v___x_3087_, v_ism1_x27_3088_, v_ism2_x27_3089_, v_is_3090_, v___x_3091_, v_newEqs1_3092_, v_newRefls1_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
stack->m_obj
 = v_res_3105_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_3106_, lean_object* v___x_3107_, lean_object* v___x_3108_, lean_object* v___x_3109_, lean_object* v___x_3110_, lean_object* v_ism1_x27_3111_, lean_object* v_ism2_x27_3112_, lean_object* v_is_3113_, lean_object* v___x_3114_, lean_object* v_newEqs1_3115_, lean_object* v_newRefls1_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
uint8_t v___x_15174__boxed_3122_; uint8_t v___x_15175__boxed_3123_; uint8_t v___x_15176__boxed_3124_; lean_object* v_res_3125_; 
v___x_15174__boxed_3122_ = lean_unbox(v___x_3108_);
v___x_15175__boxed_3123_ = lean_unbox(v___x_3109_);
v___x_15176__boxed_3124_ = lean_unbox(v___x_3110_);
v_res_3125_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_3106_, v___x_3107_, v___x_15174__boxed_3122_, v___x_15175__boxed_3123_, v___x_15176__boxed_3124_, v_ism1_x27_3111_, v_ism2_x27_3112_, v_is_3113_, v___x_3114_, v_newEqs1_3115_, v_newRefls1_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
return v_res_3125_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_3126_, uint8_t v___x_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___x_3133_; 
v___x_3133_ = l_Lean_addDecl(v___x_3126_, v___x_3127_, v___y_3130_, v___y_3131_);
return v___x_3133_;
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3126_ = stack[0].m_obj;
uint8_t v___x_3127_ = stack[1].m_num;
lean_object* v___y_3128_ = stack[2].m_obj;
lean_object* v___y_3129_ = stack[3].m_obj;
lean_object* v___y_3130_ = stack[4].m_obj;
lean_object* v___y_3131_ = stack[5].m_obj;
lean_object* v_res_3134_;
v_res_3134_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3126_, v___x_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
stack->m_obj
 = v_res_3134_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3135_, lean_object* v___x_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
uint8_t v___x_15242__boxed_3142_; lean_object* v_res_3143_; 
v___x_15242__boxed_3142_ = lean_unbox(v___x_3136_);
v_res_3143_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3135_, v___x_15242__boxed_3142_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
return v_res_3143_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3146_ = l_Lean_stringToMessageData(v___x_3145_);
return v___x_3146_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3149_ = l_Lean_stringToMessageData(v___x_3148_);
return v___x_3149_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3155_ = lean_box(0);
v___x_3156_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3157_ = l_Lean_mkConst(v___x_3156_, v___x_3155_);
return v___x_3157_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3160_ = l_Lean_stringToMessageData(v___x_3159_);
return v___x_3160_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3161_, lean_object* v_a_3162_, lean_object* v___x_3163_, lean_object* v_zs1_3164_, lean_object* v_snd_3165_, uint8_t v___x_3166_, uint8_t v___x_3167_, uint8_t v___x_3168_, lean_object* v_alts_3169_, lean_object* v_zs2_3170_, lean_object* v___ctorRet2_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = lean_array_get_borrowed(v___x_3161_, v_a_3162_, v___x_3163_);
lean_inc_ref(v_zs1_3164_);
v___x_3178_ = l_Array_append___redArg(v_zs1_3164_, v_zs2_3170_);
lean_inc(v___x_3177_);
v___x_3179_ = l_Lean_Meta_instantiateForall(v___x_3177_, v___x_3178_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
if (lean_obj_tag(v___x_3179_) == 0)
{
lean_object* v_a_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc(v_a_3180_);
lean_dec_ref_known(v___x_3179_, 1);
v___x_3181_ = lean_box(0);
v___x_3182_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3180_, v___x_3181_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref_known(v___x_3182_, 1);
v___x_3184_ = l_Lean_Expr_mvarId_x21(v_a_3183_);
v___x_3185_ = lean_array_get_size(v_snd_3165_);
v___x_3186_ = lean_box(0);
v___x_3187_ = lean_box(0);
lean_inc_ref(v___y_3174_);
v___x_3188_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3185_, v___x_3184_, v___x_3186_, v___x_3187_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_object* v_a_3189_; 
v_a_3189_ = lean_ctor_get(v___x_3188_, 0);
lean_inc(v_a_3189_);
lean_dec_ref_known(v___x_3188_, 1);
if (lean_obj_tag(v_a_3189_) == 1)
{
lean_object* v_val_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3237_; 
v_val_3190_ = lean_ctor_get(v_a_3189_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_a_3189_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3192_ = v_a_3189_;
v_isShared_3193_ = v_isSharedCheck_3237_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_val_3190_);
lean_dec(v_a_3189_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3237_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v_fst_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3235_; 
v_fst_3194_ = lean_ctor_get(v_val_3190_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v_val_3190_);
if (v_isSharedCheck_3235_ == 0)
{
lean_object* v_unused_3236_; 
v_unused_3236_ = lean_ctor_get(v_val_3190_, 1);
lean_dec(v_unused_3236_);
v___x_3196_ = v_val_3190_;
v_isShared_3197_ = v_isSharedCheck_3235_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_fst_3194_);
lean_dec(v_val_3190_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3235_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___y_3199_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v___x_3227_ = lean_array_get_borrowed(v___x_3161_, v_alts_3169_, v___x_3163_);
v___x_3228_ = lean_array_get_size(v_zs1_3164_);
lean_dec_ref(v_zs1_3164_);
v___x_3229_ = lean_unsigned_to_nat(0u);
v___x_3230_ = lean_nat_dec_eq(v___x_3228_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_inc(v___x_3227_);
v___y_3199_ = v___x_3227_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3231_; uint8_t v___x_3232_; 
v___x_3231_ = lean_array_get_size(v_zs2_3170_);
v___x_3232_ = lean_nat_dec_eq(v___x_3231_, v___x_3229_);
if (v___x_3232_ == 0)
{
lean_inc(v___x_3227_);
v___y_3199_ = v___x_3227_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3227_);
v___x_3234_ = l_Lean_Expr_app___override(v___x_3227_, v___x_3233_);
v___y_3199_ = v___x_3234_;
goto v___jp_3198_;
}
}
v___jp_3198_:
{
uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3200_ = 0;
v___x_3201_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3201_, 0, v___x_3200_);
lean_ctor_set_uint8(v___x_3201_, 1, v___x_3166_);
lean_ctor_set_uint8(v___x_3201_, 2, v___x_3167_);
lean_ctor_set_uint8(v___x_3201_, 3, v___x_3166_);
lean_inc_ref(v___y_3199_);
lean_inc(v_fst_3194_);
v___x_3202_ = l_Lean_MVarId_apply(v_fst_3194_, v___y_3199_, v___x_3201_, v___x_3187_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref_known(v___x_3202_, 1);
if (lean_obj_tag(v_a_3203_) == 0)
{
lean_object* v___x_3204_; 
lean_dec_ref(v___y_3199_);
lean_del_object(v___x_3196_);
lean_dec(v_fst_3194_);
lean_del_object(v___x_3192_);
v___x_3204_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3183_, v___y_3173_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; lean_object* v___x_3206_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref_known(v___x_3204_, 1);
v___x_3206_ = l_Lean_Meta_mkLambdaFVars(v___x_3178_, v_a_3205_, v___x_3167_, v___x_3166_, v___x_3167_, v___x_3166_, v___x_3168_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec_ref(v___x_3178_);
return v___x_3206_;
}
else
{
lean_dec_ref(v___x_3178_);
return v___x_3204_;
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3210_; 
lean_dec(v_a_3203_);
lean_dec(v_a_3183_);
lean_dec_ref(v___x_3178_);
v___x_3207_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3208_ = l_Lean_MessageData_ofExpr(v___y_3199_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set_tag(v___x_3196_, 7);
lean_ctor_set(v___x_3196_, 1, v___x_3208_);
lean_ctor_set(v___x_3196_, 0, v___x_3207_);
v___x_3210_ = v___x_3196_;
goto v_reusejp_3209_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3207_);
lean_ctor_set(v_reuseFailAlloc_3218_, 1, v___x_3208_);
v___x_3210_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3209_;
}
v_reusejp_3209_:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3214_; 
v___x_3211_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3210_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 0, v_fst_3194_);
v___x_3214_ = v___x_3192_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_fst_3194_);
v___x_3214_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3212_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3215_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3226_; 
lean_dec_ref(v___y_3199_);
lean_del_object(v___x_3196_);
lean_dec(v_fst_3194_);
lean_del_object(v___x_3192_);
lean_dec(v_a_3183_);
lean_dec_ref(v___x_3178_);
v_a_3219_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3226_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3226_ == 0)
{
v___x_3221_ = v___x_3202_;
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___x_3202_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3226_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3224_; 
if (v_isShared_3222_ == 0)
{
v___x_3224_ = v___x_3221_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_a_3219_);
v___x_3224_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
return v___x_3224_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
lean_dec(v_a_3189_);
lean_dec(v_a_3183_);
lean_dec_ref(v___x_3178_);
lean_dec_ref(v_zs1_3164_);
v___x_3238_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3239_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3238_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3239_;
}
}
else
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3247_; 
lean_dec(v_a_3183_);
lean_dec_ref(v___x_3178_);
lean_dec_ref(v_zs1_3164_);
v_a_3240_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3242_ = v___x_3188_;
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3188_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3247_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3245_; 
if (v_isShared_3243_ == 0)
{
v___x_3245_ = v___x_3242_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
}
else
{
lean_dec_ref(v___x_3178_);
lean_dec_ref(v_zs1_3164_);
return v___x_3182_;
}
}
else
{
lean_dec_ref(v___x_3178_);
lean_dec_ref(v_zs1_3164_);
return v___x_3179_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3161_ = stack[0].m_obj;
lean_object* v_a_3162_ = stack[1].m_obj;
lean_object* v___x_3163_ = stack[2].m_obj;
lean_object* v_zs1_3164_ = stack[3].m_obj;
lean_object* v_snd_3165_ = stack[4].m_obj;
uint8_t v___x_3166_ = stack[5].m_num;
uint8_t v___x_3167_ = stack[6].m_num;
uint8_t v___x_3168_ = stack[7].m_num;
lean_object* v_alts_3169_ = stack[8].m_obj;
lean_object* v_zs2_3170_ = stack[9].m_obj;
lean_object* v___ctorRet2_3171_ = stack[10].m_obj;
lean_object* v___y_3172_ = stack[11].m_obj;
lean_object* v___y_3173_ = stack[12].m_obj;
lean_object* v___y_3174_ = stack[13].m_obj;
lean_object* v___y_3175_ = stack[14].m_obj;
lean_object* v_res_3248_;
v_res_3248_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3161_, v_a_3162_, v___x_3163_, v_zs1_3164_, v_snd_3165_, v___x_3166_, v___x_3167_, v___x_3168_, v_alts_3169_, v_zs2_3170_, v___ctorRet2_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
stack->m_obj
 = v_res_3248_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3249_, lean_object* v_a_3250_, lean_object* v___x_3251_, lean_object* v_zs1_3252_, lean_object* v_snd_3253_, lean_object* v___x_3254_, lean_object* v___x_3255_, lean_object* v___x_3256_, lean_object* v_alts_3257_, lean_object* v_zs2_3258_, lean_object* v___ctorRet2_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
uint8_t v___x_15317__boxed_3265_; uint8_t v___x_15318__boxed_3266_; uint8_t v___x_15319__boxed_3267_; lean_object* v_res_3268_; 
v___x_15317__boxed_3265_ = lean_unbox(v___x_3254_);
v___x_15318__boxed_3266_ = lean_unbox(v___x_3255_);
v___x_15319__boxed_3267_ = lean_unbox(v___x_3256_);
v_res_3268_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3249_, v_a_3250_, v___x_3251_, v_zs1_3252_, v_snd_3253_, v___x_15317__boxed_3265_, v___x_15318__boxed_3266_, v___x_15319__boxed_3267_, v_alts_3257_, v_zs2_3258_, v___ctorRet2_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
lean_dec_ref(v___y_3260_);
lean_dec_ref(v___ctorRet2_3259_);
lean_dec_ref(v_zs2_3258_);
lean_dec_ref(v_alts_3257_);
lean_dec_ref(v_snd_3253_);
lean_dec(v___x_3251_);
lean_dec_ref(v_a_3250_);
lean_dec_ref(v___x_3249_);
return v_res_3268_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3269_, lean_object* v_a_3270_, lean_object* v___x_3271_, lean_object* v_snd_3272_, uint8_t v___x_3273_, uint8_t v___x_3274_, uint8_t v___x_3275_, lean_object* v_alts_3276_, lean_object* v_a_3277_, lean_object* v_zs1_3278_, lean_object* v___ctorRet1_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___f_3288_; lean_object* v___x_3289_; 
v___x_3285_ = lean_box(v___x_3273_);
v___x_3286_ = lean_box(v___x_3274_);
v___x_3287_ = lean_box(v___x_3275_);
v___f_3288_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3288_, 0, v___x_3269_);
lean_closure_set(v___f_3288_, 1, v_a_3270_);
lean_closure_set(v___f_3288_, 2, v___x_3271_);
lean_closure_set(v___f_3288_, 3, v_zs1_3278_);
lean_closure_set(v___f_3288_, 4, v_snd_3272_);
lean_closure_set(v___f_3288_, 5, v___x_3285_);
lean_closure_set(v___f_3288_, 6, v___x_3286_);
lean_closure_set(v___f_3288_, 7, v___x_3287_);
lean_closure_set(v___f_3288_, 8, v_alts_3276_);
v___x_3289_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3277_, v___f_3288_, v___x_3274_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
return v___x_3289_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3269_ = stack[0].m_obj;
lean_object* v_a_3270_ = stack[1].m_obj;
lean_object* v___x_3271_ = stack[2].m_obj;
lean_object* v_snd_3272_ = stack[3].m_obj;
uint8_t v___x_3273_ = stack[4].m_num;
uint8_t v___x_3274_ = stack[5].m_num;
uint8_t v___x_3275_ = stack[6].m_num;
lean_object* v_alts_3276_ = stack[7].m_obj;
lean_object* v_a_3277_ = stack[8].m_obj;
lean_object* v_zs1_3278_ = stack[9].m_obj;
lean_object* v___ctorRet1_3279_ = stack[10].m_obj;
lean_object* v___y_3280_ = stack[11].m_obj;
lean_object* v___y_3281_ = stack[12].m_obj;
lean_object* v___y_3282_ = stack[13].m_obj;
lean_object* v___y_3283_ = stack[14].m_obj;
lean_object* v_res_3290_;
v_res_3290_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3269_, v_a_3270_, v___x_3271_, v_snd_3272_, v___x_3273_, v___x_3274_, v___x_3275_, v_alts_3276_, v_a_3277_, v_zs1_3278_, v___ctorRet1_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
stack->m_obj
 = v_res_3290_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3291_, lean_object* v_a_3292_, lean_object* v___x_3293_, lean_object* v_snd_3294_, lean_object* v___x_3295_, lean_object* v___x_3296_, lean_object* v___x_3297_, lean_object* v_alts_3298_, lean_object* v_a_3299_, lean_object* v_zs1_3300_, lean_object* v___ctorRet1_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
uint8_t v___x_15628__boxed_3307_; uint8_t v___x_15629__boxed_3308_; uint8_t v___x_15630__boxed_3309_; lean_object* v_res_3310_; 
v___x_15628__boxed_3307_ = lean_unbox(v___x_3295_);
v___x_15629__boxed_3308_ = lean_unbox(v___x_3296_);
v___x_15630__boxed_3309_ = lean_unbox(v___x_3297_);
v_res_3310_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3291_, v_a_3292_, v___x_3293_, v_snd_3294_, v___x_15628__boxed_3307_, v___x_15629__boxed_3308_, v___x_15630__boxed_3309_, v_alts_3298_, v_a_3299_, v_zs1_3300_, v___ctorRet1_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec_ref(v___ctorRet1_3301_);
return v_res_3310_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3311_, lean_object* v_params_3312_, lean_object* v_a_3313_, lean_object* v_snd_3314_, lean_object* v_alts_3315_, size_t v_sz_3316_, size_t v_i_3317_, lean_object* v_bs_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
uint8_t v___x_3324_; 
v___x_3324_ = lean_usize_dec_lt(v_i_3317_, v_sz_3316_);
if (v___x_3324_ == 0)
{
lean_object* v___x_3325_; 
lean_dec_ref(v_alts_3315_);
lean_dec_ref(v_snd_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_tail_3311_);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v_bs_3318_);
return v___x_3325_;
}
else
{
lean_object* v___x_3326_; uint8_t v___x_3327_; uint8_t v___x_3328_; lean_object* v_v_3329_; lean_object* v___x_3330_; lean_object* v_bs_x27_3331_; lean_object* v___y_3333_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3326_ = l_Lean_instInhabitedExpr;
v___x_3327_ = 0;
v___x_3328_ = 1;
v_v_3329_ = lean_array_uget(v_bs_3318_, v_i_3317_);
v___x_3330_ = lean_unsigned_to_nat(0u);
v_bs_x27_3331_ = lean_array_uset(v_bs_3318_, v_i_3317_, v___x_3330_);
v___x_3347_ = lean_usize_to_nat(v_i_3317_);
lean_inc(v_tail_3311_);
v___x_3348_ = l_Lean_mkConst(v_v_3329_, v_tail_3311_);
v___x_3349_ = l_Lean_mkAppN(v___x_3348_, v_params_3312_);
lean_inc(v___y_3322_);
lean_inc_ref(v___y_3321_);
lean_inc(v___y_3320_);
lean_inc_ref(v___y_3319_);
v___x_3350_ = lean_infer_type(v___x_3349_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___f_3355_; lean_object* v___x_3356_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc_n(v_a_3351_, 2);
lean_dec_ref_known(v___x_3350_, 1);
v___x_3352_ = lean_box(v___x_3324_);
v___x_3353_ = lean_box(v___x_3327_);
v___x_3354_ = lean_box(v___x_3328_);
lean_inc_ref(v_alts_3315_);
lean_inc_ref(v_snd_3314_);
lean_inc_ref(v_a_3313_);
v___f_3355_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3355_, 0, v___x_3326_);
lean_closure_set(v___f_3355_, 1, v_a_3313_);
lean_closure_set(v___f_3355_, 2, v___x_3347_);
lean_closure_set(v___f_3355_, 3, v_snd_3314_);
lean_closure_set(v___f_3355_, 4, v___x_3352_);
lean_closure_set(v___f_3355_, 5, v___x_3353_);
lean_closure_set(v___f_3355_, 6, v___x_3354_);
lean_closure_set(v___f_3355_, 7, v_alts_3315_);
lean_closure_set(v___f_3355_, 8, v_a_3351_);
v___x_3356_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3351_, v___f_3355_, v___x_3327_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
v___y_3333_ = v___x_3356_;
goto v___jp_3332_;
}
else
{
lean_dec(v___x_3347_);
v___y_3333_ = v___x_3350_;
goto v___jp_3332_;
}
v___jp_3332_:
{
if (lean_obj_tag(v___y_3333_) == 0)
{
lean_object* v_a_3334_; size_t v___x_3335_; size_t v___x_3336_; lean_object* v___x_3337_; 
v_a_3334_ = lean_ctor_get(v___y_3333_, 0);
lean_inc(v_a_3334_);
lean_dec_ref_known(v___y_3333_, 1);
v___x_3335_ = ((size_t)1ULL);
v___x_3336_ = lean_usize_add(v_i_3317_, v___x_3335_);
v___x_3337_ = lean_array_uset(v_bs_x27_3331_, v_i_3317_, v_a_3334_);
v_i_3317_ = v___x_3336_;
v_bs_3318_ = v___x_3337_;
goto _start;
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec_ref(v_bs_x27_3331_);
lean_dec_ref(v_alts_3315_);
lean_dec_ref(v_snd_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_tail_3311_);
v_a_3339_ = lean_ctor_get(v___y_3333_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___y_3333_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___y_3333_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___y_3333_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_3311_ = stack[0].m_obj;
lean_object* v_params_3312_ = stack[1].m_obj;
lean_object* v_a_3313_ = stack[2].m_obj;
lean_object* v_snd_3314_ = stack[3].m_obj;
lean_object* v_alts_3315_ = stack[4].m_obj;
size_t v_sz_3316_ = stack[5].m_num;
size_t v_i_3317_ = stack[6].m_num;
lean_object* v_bs_3318_ = stack[7].m_obj;
lean_object* v___y_3319_ = stack[8].m_obj;
lean_object* v___y_3320_ = stack[9].m_obj;
lean_object* v___y_3321_ = stack[10].m_obj;
lean_object* v___y_3322_ = stack[11].m_obj;
lean_object* v_res_3357_;
v_res_3357_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3311_, v_params_3312_, v_a_3313_, v_snd_3314_, v_alts_3315_, v_sz_3316_, v_i_3317_, v_bs_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_);
stack->m_obj
 = v_res_3357_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3358_, lean_object* v_params_3359_, lean_object* v_a_3360_, lean_object* v_snd_3361_, lean_object* v_alts_3362_, lean_object* v_sz_3363_, lean_object* v_i_3364_, lean_object* v_bs_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
size_t v_sz_boxed_3371_; size_t v_i_boxed_3372_; lean_object* v_res_3373_; 
v_sz_boxed_3371_ = lean_unbox_usize(v_sz_3363_);
lean_dec(v_sz_3363_);
v_i_boxed_3372_ = lean_unbox_usize(v_i_3364_);
lean_dec(v_i_3364_);
v_res_3373_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3358_, v_params_3359_, v_a_3360_, v_snd_3361_, v_alts_3362_, v_sz_boxed_3371_, v_i_boxed_3372_, v_bs_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_);
lean_dec(v___y_3369_);
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3367_);
lean_dec_ref(v___y_3366_);
lean_dec_ref(v_params_3359_);
return v_res_3373_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_unsigned_to_nat(16u);
v___x_3376_ = lean_mk_array(v___x_3375_, v___x_3374_);
return v___x_3376_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3377_, lean_object* v___x_3378_, uint8_t v___x_3379_, uint8_t v___x_3380_, uint8_t v___x_3381_, lean_object* v_ism1_x27_3382_, lean_object* v_is_3383_, lean_object* v___x_3384_, lean_object* v___x_3385_, lean_object* v___x_3386_, lean_object* v___x_3387_, lean_object* v_params_3388_, lean_object* v___x_3389_, lean_object* v___x_3390_, lean_object* v_heq_3391_, lean_object* v_val_3392_, lean_object* v_tail_3393_, lean_object* v_alts_3394_, size_t v_sz_3395_, size_t v___x_3396_, lean_object* v___x_3397_, lean_object* v___x_3398_, lean_object* v_declName_3399_, lean_object* v_levelParams_3400_, lean_object* v_numIndices_3401_, lean_object* v___x_3402_, lean_object* v___x_3403_, lean_object* v_numParams_3404_, lean_object* v_snd_3405_, lean_object* v_ism2_x27_3406_, lean_object* v_x_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___f_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
v___x_3413_ = lean_box(v___x_3379_);
v___x_3414_ = lean_box(v___x_3380_);
v___x_3415_ = lean_box(v___x_3381_);
lean_inc_ref(v___x_3384_);
lean_inc_ref_n(v_is_3383_, 2);
lean_inc_ref(v_ism1_x27_3382_);
lean_inc_ref(v_motive_3377_);
v___f_3416_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3416_, 0, v_motive_3377_);
lean_closure_set(v___f_3416_, 1, v___x_3378_);
lean_closure_set(v___f_3416_, 2, v___x_3413_);
lean_closure_set(v___f_3416_, 3, v___x_3414_);
lean_closure_set(v___f_3416_, 4, v___x_3415_);
lean_closure_set(v___f_3416_, 5, v_ism1_x27_3382_);
lean_closure_set(v___f_3416_, 6, v_ism2_x27_3406_);
lean_closure_set(v___f_3416_, 7, v_is_3383_);
lean_closure_set(v___f_3416_, 8, v___x_3384_);
lean_inc_ref(v___x_3385_);
v___x_3417_ = lean_array_push(v_is_3383_, v___x_3385_);
v___x_3418_ = l_Lean_Meta_withNewEqs___redArg(v___x_3417_, v_ism1_x27_3382_, v___f_3416_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v_a_3419_; lean_object* v_fst_3420_; lean_object* v_snd_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3522_; 
v_a_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc(v_a_3419_);
lean_dec_ref_known(v___x_3418_, 1);
v_fst_3420_ = lean_ctor_get(v_a_3419_, 0);
v_snd_3421_ = lean_ctor_get(v_a_3419_, 1);
v_isSharedCheck_3522_ = !lean_is_exclusive(v_a_3419_);
if (v_isSharedCheck_3522_ == 0)
{
v___x_3423_ = v_a_3419_;
v_isShared_3424_ = v_isSharedCheck_3522_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_snd_3421_);
lean_inc(v_fst_3420_);
lean_dec(v_a_3419_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3522_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3425_ = l_Lean_mkConst(v___x_3386_, v___x_3387_);
v___x_3426_ = l_Lean_mkAppN(v___x_3425_, v_params_3388_);
v___x_3427_ = l_Lean_Expr_app___override(v___x_3426_, v_fst_3420_);
lean_inc_ref(v_is_3383_);
v___x_3428_ = l_Array_append___redArg(v_is_3383_, v___x_3389_);
v___x_3429_ = l_Array_append___redArg(v___x_3428_, v_is_3383_);
v___x_3430_ = l_Array_append___redArg(v___x_3429_, v___x_3390_);
v___x_3431_ = l_Lean_mkAppN(v___x_3427_, v___x_3430_);
lean_dec_ref(v___x_3430_);
lean_inc_ref(v_heq_3391_);
v___x_3432_ = l_Lean_Expr_app___override(v___x_3431_, v_heq_3391_);
v___x_3433_ = l_Lean_InductiveVal_numCtors(v_val_3392_);
lean_inc_ref(v___x_3432_);
v___x_3434_ = l_Lean_Meta_inferArgumentTypesN(v___x_3433_, v___x_3432_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_object* v_a_3435_; lean_object* v___x_3436_; 
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref_known(v___x_3434_, 1);
lean_inc_ref(v_alts_3394_);
lean_inc(v_snd_3421_);
v___x_3436_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3393_, v_params_3388_, v_a_3435_, v_snd_3421_, v_alts_3394_, v_sz_3395_, v___x_3396_, v___x_3397_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3436_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v_a_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc(v_a_3437_);
lean_dec_ref_known(v___x_3436_, 1);
v___x_3438_ = l_Lean_mkAppN(v___x_3432_, v_a_3437_);
lean_dec(v_a_3437_);
v___x_3439_ = l_Lean_mkAppN(v___x_3438_, v_snd_3421_);
lean_dec(v_snd_3421_);
lean_inc_ref(v___x_3398_);
v___x_3440_ = lean_array_push(v___x_3398_, v_motive_3377_);
v___x_3441_ = l_Array_append___redArg(v_params_3388_, v___x_3440_);
lean_dec_ref(v___x_3440_);
v___x_3442_ = l_Array_append___redArg(v___x_3441_, v_is_3383_);
lean_dec_ref(v_is_3383_);
v___x_3443_ = lean_unsigned_to_nat(2u);
v___x_3444_ = lean_mk_empty_array_with_capacity(v___x_3443_);
v___x_3445_ = lean_array_push(v___x_3444_, v___x_3385_);
v___x_3446_ = lean_array_push(v___x_3445_, v___x_3384_);
v___x_3447_ = l_Array_append___redArg(v___x_3442_, v___x_3446_);
lean_dec_ref(v___x_3446_);
v___x_3448_ = lean_array_push(v___x_3398_, v_heq_3391_);
v___x_3449_ = l_Array_append___redArg(v___x_3447_, v___x_3448_);
lean_dec_ref(v___x_3448_);
v___x_3450_ = l_Array_append___redArg(v___x_3449_, v_alts_3394_);
lean_dec_ref(v_alts_3394_);
v___x_3451_ = l_Lean_Meta_mkLambdaFVars(v___x_3450_, v___x_3439_, v___x_3379_, v___x_3380_, v___x_3379_, v___x_3380_, v___x_3381_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec_ref(v___x_3450_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3453_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc_n(v_a_3452_, 2);
lean_dec_ref_known(v___x_3451_, 1);
lean_inc(v___y_3411_);
lean_inc_ref(v___y_3410_);
lean_inc(v___y_3409_);
lean_inc_ref(v___y_3408_);
v___x_3453_ = lean_infer_type(v_a_3452_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3489_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = lean_box(1);
lean_inc(v_declName_3399_);
v___x_3456_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3399_, v_levelParams_3400_, v_a_3454_, v_a_3452_, v___x_3455_, v___y_3411_);
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3489_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3489_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
lean_ctor_set_tag(v___x_3459_, 1);
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v___f_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3474_; 
v___x_3463_ = lean_box(v___x_3379_);
lean_inc_ref(v___x_3462_);
v___f_3464_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3464_, 0, v___x_3462_);
lean_closure_set(v___f_3464_, 1, v___x_3463_);
v___x_3465_ = lean_nat_add(v_numIndices_3401_, v___x_3402_);
lean_inc(v___x_3403_);
v___x_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3403_);
v___x_3467_ = lean_box(0);
v___x_3468_ = lean_mk_empty_array_with_capacity(v___x_3402_);
v___x_3469_ = lean_array_push(v___x_3468_, v___x_3467_);
v___x_3470_ = lean_array_push(v___x_3469_, v___x_3467_);
v___x_3471_ = lean_array_push(v___x_3470_, v___x_3467_);
v___x_3472_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 1, v___x_3472_);
lean_ctor_set(v___x_3423_, 0, v___x_3403_);
v___x_3474_ = v___x_3423_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3403_);
lean_ctor_set(v_reuseFailAlloc_3487_, 1, v___x_3472_);
v___x_3474_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
lean_object* v___x_3475_; uint8_t v___y_3477_; uint8_t v___x_3486_; 
v___x_3475_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3475_, 0, v_numParams_3404_);
lean_ctor_set(v___x_3475_, 1, v___x_3465_);
lean_ctor_set(v___x_3475_, 2, v_snd_3405_);
lean_ctor_set(v___x_3475_, 3, v___x_3466_);
lean_ctor_set(v___x_3475_, 4, v___x_3471_);
lean_ctor_set(v___x_3475_, 5, v___x_3474_);
v___x_3486_ = l_Lean_isPrivateName(v_declName_3399_);
if (v___x_3486_ == 0)
{
v___y_3477_ = v___x_3380_;
goto v___jp_3476_;
}
else
{
v___y_3477_ = v___x_3379_;
goto v___jp_3476_;
}
v___jp_3476_:
{
lean_object* v___x_3478_; 
v___x_3478_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3464_, v___y_3477_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
lean_dec_ref_known(v___x_3478_, 1);
v___x_3479_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3399_);
v___x_3480_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3479_, v_declName_3399_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v___x_3481_; uint8_t v___x_3482_; lean_object* v___x_3483_; 
lean_dec_ref_known(v___x_3480_, 1);
lean_inc_n(v_declName_3399_, 2);
v___x_3481_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3399_, v___x_3475_, v___y_3409_, v___y_3411_);
lean_dec_ref(v___x_3481_);
v___x_3482_ = 0;
v___x_3483_ = l_Lean_Meta_setInlineAttribute(v_declName_3399_, v___x_3482_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_object* v___x_3484_; 
lean_dec_ref_known(v___x_3483_, 1);
v___x_3484_ = l_Lean_enableRealizationsForConst(v_declName_3399_, v___y_3410_, v___y_3411_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3485_; 
lean_dec_ref_known(v___x_3484_, 1);
v___x_3485_ = l_Lean_compileDecl(v___x_3462_, v___x_3380_, v___y_3410_, v___y_3411_);
return v___x_3485_;
}
else
{
lean_dec_ref(v___x_3462_);
return v___x_3484_;
}
}
else
{
lean_dec_ref(v___x_3462_);
lean_dec(v_declName_3399_);
return v___x_3483_;
}
}
else
{
lean_dec_ref_known(v___x_3475_, 6);
lean_dec_ref(v___x_3462_);
lean_dec(v_declName_3399_);
return v___x_3480_;
}
}
else
{
lean_dec_ref_known(v___x_3475_, 6);
lean_dec_ref(v___x_3462_);
lean_dec(v_declName_3399_);
return v___x_3478_;
}
}
}
}
}
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec(v_a_3452_);
lean_del_object(v___x_3423_);
lean_dec_ref(v_snd_3405_);
lean_dec(v_numParams_3404_);
lean_dec(v___x_3403_);
lean_dec(v_levelParams_3400_);
lean_dec(v_declName_3399_);
v_a_3490_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3453_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3453_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_del_object(v___x_3423_);
lean_dec_ref(v_snd_3405_);
lean_dec(v_numParams_3404_);
lean_dec(v___x_3403_);
lean_dec(v_levelParams_3400_);
lean_dec(v_declName_3399_);
v_a_3498_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3451_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3451_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_dec_ref(v___x_3432_);
lean_del_object(v___x_3423_);
lean_dec(v_snd_3421_);
lean_dec_ref(v_snd_3405_);
lean_dec(v_numParams_3404_);
lean_dec(v___x_3403_);
lean_dec(v_levelParams_3400_);
lean_dec(v_declName_3399_);
lean_dec_ref(v___x_3398_);
lean_dec_ref(v_alts_3394_);
lean_dec_ref(v_heq_3391_);
lean_dec_ref(v_params_3388_);
lean_dec_ref(v___x_3385_);
lean_dec_ref(v___x_3384_);
lean_dec_ref(v_is_3383_);
lean_dec_ref(v_motive_3377_);
v_a_3506_ = lean_ctor_get(v___x_3436_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3436_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3436_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3436_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec_ref(v___x_3432_);
lean_del_object(v___x_3423_);
lean_dec(v_snd_3421_);
lean_dec_ref(v_snd_3405_);
lean_dec(v_numParams_3404_);
lean_dec(v___x_3403_);
lean_dec(v_levelParams_3400_);
lean_dec(v_declName_3399_);
lean_dec_ref(v___x_3398_);
lean_dec_ref(v___x_3397_);
lean_dec_ref(v_alts_3394_);
lean_dec(v_tail_3393_);
lean_dec_ref(v_heq_3391_);
lean_dec_ref(v_params_3388_);
lean_dec_ref(v___x_3385_);
lean_dec_ref(v___x_3384_);
lean_dec_ref(v_is_3383_);
lean_dec_ref(v_motive_3377_);
v_a_3514_ = lean_ctor_get(v___x_3434_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3434_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3434_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3434_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
else
{
lean_object* v_a_3523_; lean_object* v___x_3525_; uint8_t v_isShared_3526_; uint8_t v_isSharedCheck_3530_; 
lean_dec_ref(v_snd_3405_);
lean_dec(v_numParams_3404_);
lean_dec(v___x_3403_);
lean_dec(v_levelParams_3400_);
lean_dec(v_declName_3399_);
lean_dec_ref(v___x_3398_);
lean_dec_ref(v___x_3397_);
lean_dec_ref(v_alts_3394_);
lean_dec(v_tail_3393_);
lean_dec_ref(v_heq_3391_);
lean_dec_ref(v_params_3388_);
lean_dec(v___x_3387_);
lean_dec(v___x_3386_);
lean_dec_ref(v___x_3385_);
lean_dec_ref(v___x_3384_);
lean_dec_ref(v_is_3383_);
lean_dec_ref(v_motive_3377_);
v_a_3523_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3525_ = v___x_3418_;
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
else
{
lean_inc(v_a_3523_);
lean_dec(v___x_3418_);
v___x_3525_ = lean_box(0);
v_isShared_3526_ = v_isSharedCheck_3530_;
goto v_resetjp_3524_;
}
v_resetjp_3524_:
{
lean_object* v___x_3528_; 
if (v_isShared_3526_ == 0)
{
v___x_3528_ = v___x_3525_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_motive_3377_ = stack[0].m_obj;
lean_object* v___x_3378_ = stack[1].m_obj;
uint8_t v___x_3379_ = stack[2].m_num;
uint8_t v___x_3380_ = stack[3].m_num;
uint8_t v___x_3381_ = stack[4].m_num;
lean_object* v_ism1_x27_3382_ = stack[5].m_obj;
lean_object* v_is_3383_ = stack[6].m_obj;
lean_object* v___x_3384_ = stack[7].m_obj;
lean_object* v___x_3385_ = stack[8].m_obj;
lean_object* v___x_3386_ = stack[9].m_obj;
lean_object* v___x_3387_ = stack[10].m_obj;
lean_object* v_params_3388_ = stack[11].m_obj;
lean_object* v___x_3389_ = stack[12].m_obj;
lean_object* v___x_3390_ = stack[13].m_obj;
lean_object* v_heq_3391_ = stack[14].m_obj;
lean_object* v_val_3392_ = stack[15].m_obj;
lean_object* v_tail_3393_ = stack[16].m_obj;
lean_object* v_alts_3394_ = stack[17].m_obj;
size_t v_sz_3395_ = stack[18].m_num;
size_t v___x_3396_ = stack[19].m_num;
lean_object* v___x_3397_ = stack[20].m_obj;
lean_object* v___x_3398_ = stack[21].m_obj;
lean_object* v_declName_3399_ = stack[22].m_obj;
lean_object* v_levelParams_3400_ = stack[23].m_obj;
lean_object* v_numIndices_3401_ = stack[24].m_obj;
lean_object* v___x_3402_ = stack[25].m_obj;
lean_object* v___x_3403_ = stack[26].m_obj;
lean_object* v_numParams_3404_ = stack[27].m_obj;
lean_object* v_snd_3405_ = stack[28].m_obj;
lean_object* v_ism2_x27_3406_ = stack[29].m_obj;
lean_object* v_x_3407_ = stack[30].m_obj;
lean_object* v___y_3408_ = stack[31].m_obj;
lean_object* v___y_3409_ = stack[32].m_obj;
lean_object* v___y_3410_ = stack[33].m_obj;
lean_object* v___y_3411_ = stack[34].m_obj;
lean_object* v_res_3531_;
v_res_3531_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3377_, v___x_3378_, v___x_3379_, v___x_3380_, v___x_3381_, v_ism1_x27_3382_, v_is_3383_, v___x_3384_, v___x_3385_, v___x_3386_, v___x_3387_, v_params_3388_, v___x_3389_, v___x_3390_, v_heq_3391_, v_val_3392_, v_tail_3393_, v_alts_3394_, v_sz_3395_, v___x_3396_, v___x_3397_, v___x_3398_, v_declName_3399_, v_levelParams_3400_, v_numIndices_3401_, v___x_3402_, v___x_3403_, v_numParams_3404_, v_snd_3405_, v_ism2_x27_3406_, v_x_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
stack->m_obj
 = v_res_3531_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3532_ = _args[0];
lean_object* v___x_3533_ = _args[1];
lean_object* v___x_3534_ = _args[2];
lean_object* v___x_3535_ = _args[3];
lean_object* v___x_3536_ = _args[4];
lean_object* v_ism1_x27_3537_ = _args[5];
lean_object* v_is_3538_ = _args[6];
lean_object* v___x_3539_ = _args[7];
lean_object* v___x_3540_ = _args[8];
lean_object* v___x_3541_ = _args[9];
lean_object* v___x_3542_ = _args[10];
lean_object* v_params_3543_ = _args[11];
lean_object* v___x_3544_ = _args[12];
lean_object* v___x_3545_ = _args[13];
lean_object* v_heq_3546_ = _args[14];
lean_object* v_val_3547_ = _args[15];
lean_object* v_tail_3548_ = _args[16];
lean_object* v_alts_3549_ = _args[17];
lean_object* v_sz_3550_ = _args[18];
lean_object* v___x_3551_ = _args[19];
lean_object* v___x_3552_ = _args[20];
lean_object* v___x_3553_ = _args[21];
lean_object* v_declName_3554_ = _args[22];
lean_object* v_levelParams_3555_ = _args[23];
lean_object* v_numIndices_3556_ = _args[24];
lean_object* v___x_3557_ = _args[25];
lean_object* v___x_3558_ = _args[26];
lean_object* v_numParams_3559_ = _args[27];
lean_object* v_snd_3560_ = _args[28];
lean_object* v_ism2_x27_3561_ = _args[29];
lean_object* v_x_3562_ = _args[30];
lean_object* v___y_3563_ = _args[31];
lean_object* v___y_3564_ = _args[32];
lean_object* v___y_3565_ = _args[33];
lean_object* v___y_3566_ = _args[34];
lean_object* v___y_3567_ = _args[35];
_start:
{
uint8_t v___x_15845__boxed_3568_; uint8_t v___x_15846__boxed_3569_; uint8_t v___x_15847__boxed_3570_; size_t v_sz_boxed_3571_; size_t v___x_15856__boxed_3572_; lean_object* v_res_3573_; 
v___x_15845__boxed_3568_ = lean_unbox(v___x_3534_);
v___x_15846__boxed_3569_ = lean_unbox(v___x_3535_);
v___x_15847__boxed_3570_ = lean_unbox(v___x_3536_);
v_sz_boxed_3571_ = lean_unbox_usize(v_sz_3550_);
lean_dec(v_sz_3550_);
v___x_15856__boxed_3572_ = lean_unbox_usize(v___x_3551_);
lean_dec(v___x_3551_);
v_res_3573_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3532_, v___x_3533_, v___x_15845__boxed_3568_, v___x_15846__boxed_3569_, v___x_15847__boxed_3570_, v_ism1_x27_3537_, v_is_3538_, v___x_3539_, v___x_3540_, v___x_3541_, v___x_3542_, v_params_3543_, v___x_3544_, v___x_3545_, v_heq_3546_, v_val_3547_, v_tail_3548_, v_alts_3549_, v_sz_boxed_3571_, v___x_15856__boxed_3572_, v___x_3552_, v___x_3553_, v_declName_3554_, v_levelParams_3555_, v_numIndices_3556_, v___x_3557_, v___x_3558_, v_numParams_3559_, v_snd_3560_, v_ism2_x27_3561_, v_x_3562_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
lean_dec(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3563_);
lean_dec_ref(v_x_3562_);
lean_dec(v___x_3557_);
lean_dec(v_numIndices_3556_);
lean_dec_ref(v_val_3547_);
lean_dec_ref(v___x_3545_);
lean_dec_ref(v___x_3544_);
return v_res_3573_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3574_, lean_object* v___x_3575_, uint8_t v___x_3576_, uint8_t v___x_3577_, uint8_t v___x_3578_, lean_object* v_is_3579_, lean_object* v___x_3580_, lean_object* v___x_3581_, lean_object* v___x_3582_, lean_object* v___x_3583_, lean_object* v_params_3584_, lean_object* v___x_3585_, lean_object* v___x_3586_, lean_object* v_heq_3587_, lean_object* v_val_3588_, lean_object* v_tail_3589_, lean_object* v_alts_3590_, size_t v_sz_3591_, size_t v___x_3592_, lean_object* v___x_3593_, lean_object* v___x_3594_, lean_object* v_declName_3595_, lean_object* v_levelParams_3596_, lean_object* v_numIndices_3597_, lean_object* v___x_3598_, lean_object* v___x_3599_, lean_object* v_numParams_3600_, lean_object* v_snd_3601_, lean_object* v___x_3602_, lean_object* v___x_3603_, lean_object* v_ism1_x27_3604_, lean_object* v_x_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___f_3616_; lean_object* v___x_3617_; 
v___x_3611_ = lean_box(v___x_3576_);
v___x_3612_ = lean_box(v___x_3577_);
v___x_3613_ = lean_box(v___x_3578_);
v___x_3614_ = lean_box_usize(v_sz_3591_);
v___x_3615_ = lean_box_usize(v___x_3592_);
v___f_3616_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3616_, 0, v_motive_3574_);
lean_closure_set(v___f_3616_, 1, v___x_3575_);
lean_closure_set(v___f_3616_, 2, v___x_3611_);
lean_closure_set(v___f_3616_, 3, v___x_3612_);
lean_closure_set(v___f_3616_, 4, v___x_3613_);
lean_closure_set(v___f_3616_, 5, v_ism1_x27_3604_);
lean_closure_set(v___f_3616_, 6, v_is_3579_);
lean_closure_set(v___f_3616_, 7, v___x_3580_);
lean_closure_set(v___f_3616_, 8, v___x_3581_);
lean_closure_set(v___f_3616_, 9, v___x_3582_);
lean_closure_set(v___f_3616_, 10, v___x_3583_);
lean_closure_set(v___f_3616_, 11, v_params_3584_);
lean_closure_set(v___f_3616_, 12, v___x_3585_);
lean_closure_set(v___f_3616_, 13, v___x_3586_);
lean_closure_set(v___f_3616_, 14, v_heq_3587_);
lean_closure_set(v___f_3616_, 15, v_val_3588_);
lean_closure_set(v___f_3616_, 16, v_tail_3589_);
lean_closure_set(v___f_3616_, 17, v_alts_3590_);
lean_closure_set(v___f_3616_, 18, v___x_3614_);
lean_closure_set(v___f_3616_, 19, v___x_3615_);
lean_closure_set(v___f_3616_, 20, v___x_3593_);
lean_closure_set(v___f_3616_, 21, v___x_3594_);
lean_closure_set(v___f_3616_, 22, v_declName_3595_);
lean_closure_set(v___f_3616_, 23, v_levelParams_3596_);
lean_closure_set(v___f_3616_, 24, v_numIndices_3597_);
lean_closure_set(v___f_3616_, 25, v___x_3598_);
lean_closure_set(v___f_3616_, 26, v___x_3599_);
lean_closure_set(v___f_3616_, 27, v_numParams_3600_);
lean_closure_set(v___f_3616_, 28, v_snd_3601_);
v___x_3617_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3602_, v___x_3603_, v___f_3616_, v___x_3576_, v___x_3576_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
return v___x_3617_;
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_motive_3574_ = stack[0].m_obj;
lean_object* v___x_3575_ = stack[1].m_obj;
uint8_t v___x_3576_ = stack[2].m_num;
uint8_t v___x_3577_ = stack[3].m_num;
uint8_t v___x_3578_ = stack[4].m_num;
lean_object* v_is_3579_ = stack[5].m_obj;
lean_object* v___x_3580_ = stack[6].m_obj;
lean_object* v___x_3581_ = stack[7].m_obj;
lean_object* v___x_3582_ = stack[8].m_obj;
lean_object* v___x_3583_ = stack[9].m_obj;
lean_object* v_params_3584_ = stack[10].m_obj;
lean_object* v___x_3585_ = stack[11].m_obj;
lean_object* v___x_3586_ = stack[12].m_obj;
lean_object* v_heq_3587_ = stack[13].m_obj;
lean_object* v_val_3588_ = stack[14].m_obj;
lean_object* v_tail_3589_ = stack[15].m_obj;
lean_object* v_alts_3590_ = stack[16].m_obj;
size_t v_sz_3591_ = stack[17].m_num;
size_t v___x_3592_ = stack[18].m_num;
lean_object* v___x_3593_ = stack[19].m_obj;
lean_object* v___x_3594_ = stack[20].m_obj;
lean_object* v_declName_3595_ = stack[21].m_obj;
lean_object* v_levelParams_3596_ = stack[22].m_obj;
lean_object* v_numIndices_3597_ = stack[23].m_obj;
lean_object* v___x_3598_ = stack[24].m_obj;
lean_object* v___x_3599_ = stack[25].m_obj;
lean_object* v_numParams_3600_ = stack[26].m_obj;
lean_object* v_snd_3601_ = stack[27].m_obj;
lean_object* v___x_3602_ = stack[28].m_obj;
lean_object* v___x_3603_ = stack[29].m_obj;
lean_object* v_ism1_x27_3604_ = stack[30].m_obj;
lean_object* v_x_3605_ = stack[31].m_obj;
lean_object* v___y_3606_ = stack[32].m_obj;
lean_object* v___y_3607_ = stack[33].m_obj;
lean_object* v___y_3608_ = stack[34].m_obj;
lean_object* v___y_3609_ = stack[35].m_obj;
lean_object* v_res_3618_;
v_res_3618_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3574_, v___x_3575_, v___x_3576_, v___x_3577_, v___x_3578_, v_is_3579_, v___x_3580_, v___x_3581_, v___x_3582_, v___x_3583_, v_params_3584_, v___x_3585_, v___x_3586_, v_heq_3587_, v_val_3588_, v_tail_3589_, v_alts_3590_, v_sz_3591_, v___x_3592_, v___x_3593_, v___x_3594_, v_declName_3595_, v_levelParams_3596_, v_numIndices_3597_, v___x_3598_, v___x_3599_, v_numParams_3600_, v_snd_3601_, v___x_3602_, v___x_3603_, v_ism1_x27_3604_, v_x_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
stack->m_obj
 = v_res_3618_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3619_ = _args[0];
lean_object* v___x_3620_ = _args[1];
lean_object* v___x_3621_ = _args[2];
lean_object* v___x_3622_ = _args[3];
lean_object* v___x_3623_ = _args[4];
lean_object* v_is_3624_ = _args[5];
lean_object* v___x_3625_ = _args[6];
lean_object* v___x_3626_ = _args[7];
lean_object* v___x_3627_ = _args[8];
lean_object* v___x_3628_ = _args[9];
lean_object* v_params_3629_ = _args[10];
lean_object* v___x_3630_ = _args[11];
lean_object* v___x_3631_ = _args[12];
lean_object* v_heq_3632_ = _args[13];
lean_object* v_val_3633_ = _args[14];
lean_object* v_tail_3634_ = _args[15];
lean_object* v_alts_3635_ = _args[16];
lean_object* v_sz_3636_ = _args[17];
lean_object* v___x_3637_ = _args[18];
lean_object* v___x_3638_ = _args[19];
lean_object* v___x_3639_ = _args[20];
lean_object* v_declName_3640_ = _args[21];
lean_object* v_levelParams_3641_ = _args[22];
lean_object* v_numIndices_3642_ = _args[23];
lean_object* v___x_3643_ = _args[24];
lean_object* v___x_3644_ = _args[25];
lean_object* v_numParams_3645_ = _args[26];
lean_object* v_snd_3646_ = _args[27];
lean_object* v___x_3647_ = _args[28];
lean_object* v___x_3648_ = _args[29];
lean_object* v_ism1_x27_3649_ = _args[30];
lean_object* v_x_3650_ = _args[31];
lean_object* v___y_3651_ = _args[32];
lean_object* v___y_3652_ = _args[33];
lean_object* v___y_3653_ = _args[34];
lean_object* v___y_3654_ = _args[35];
lean_object* v___y_3655_ = _args[36];
_start:
{
uint8_t v___x_16336__boxed_3656_; uint8_t v___x_16337__boxed_3657_; uint8_t v___x_16338__boxed_3658_; size_t v_sz_boxed_3659_; size_t v___x_16347__boxed_3660_; lean_object* v_res_3661_; 
v___x_16336__boxed_3656_ = lean_unbox(v___x_3621_);
v___x_16337__boxed_3657_ = lean_unbox(v___x_3622_);
v___x_16338__boxed_3658_ = lean_unbox(v___x_3623_);
v_sz_boxed_3659_ = lean_unbox_usize(v_sz_3636_);
lean_dec(v_sz_3636_);
v___x_16347__boxed_3660_ = lean_unbox_usize(v___x_3637_);
lean_dec(v___x_3637_);
v_res_3661_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3619_, v___x_3620_, v___x_16336__boxed_3656_, v___x_16337__boxed_3657_, v___x_16338__boxed_3658_, v_is_3624_, v___x_3625_, v___x_3626_, v___x_3627_, v___x_3628_, v_params_3629_, v___x_3630_, v___x_3631_, v_heq_3632_, v_val_3633_, v_tail_3634_, v_alts_3635_, v_sz_boxed_3659_, v___x_16347__boxed_3660_, v___x_3638_, v___x_3639_, v_declName_3640_, v_levelParams_3641_, v_numIndices_3642_, v___x_3643_, v___x_3644_, v_numParams_3645_, v_snd_3646_, v___x_3647_, v___x_3648_, v_ism1_x27_3649_, v_x_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec_ref(v_x_3650_);
return v_res_3661_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3662_, lean_object* v___x_3663_, lean_object* v_motive_3664_, lean_object* v___x_3665_, uint8_t v___x_3666_, uint8_t v___x_3667_, uint8_t v___x_3668_, lean_object* v_is_3669_, lean_object* v___x_3670_, lean_object* v___x_3671_, lean_object* v___x_3672_, lean_object* v___x_3673_, lean_object* v_params_3674_, lean_object* v___x_3675_, lean_object* v___x_3676_, lean_object* v_heq_3677_, lean_object* v_val_3678_, lean_object* v_tail_3679_, size_t v_sz_3680_, size_t v___x_3681_, lean_object* v___x_3682_, lean_object* v___x_3683_, lean_object* v_declName_3684_, lean_object* v_levelParams_3685_, lean_object* v___x_3686_, lean_object* v___x_3687_, lean_object* v_numParams_3688_, lean_object* v_snd_3689_, lean_object* v___x_3690_, lean_object* v_alts_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___f_3704_; lean_object* v___x_3705_; 
v___x_3697_ = lean_nat_add(v_numIndices_3662_, v___x_3663_);
v___x_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
v___x_3699_ = lean_box(v___x_3666_);
v___x_3700_ = lean_box(v___x_3667_);
v___x_3701_ = lean_box(v___x_3668_);
v___x_3702_ = lean_box_usize(v_sz_3680_);
v___x_3703_ = lean_box_usize(v___x_3681_);
lean_inc_ref(v___x_3698_);
lean_inc_ref(v___x_3690_);
v___f_3704_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3704_, 0, v_motive_3664_);
lean_closure_set(v___f_3704_, 1, v___x_3665_);
lean_closure_set(v___f_3704_, 2, v___x_3699_);
lean_closure_set(v___f_3704_, 3, v___x_3700_);
lean_closure_set(v___f_3704_, 4, v___x_3701_);
lean_closure_set(v___f_3704_, 5, v_is_3669_);
lean_closure_set(v___f_3704_, 6, v___x_3670_);
lean_closure_set(v___f_3704_, 7, v___x_3671_);
lean_closure_set(v___f_3704_, 8, v___x_3672_);
lean_closure_set(v___f_3704_, 9, v___x_3673_);
lean_closure_set(v___f_3704_, 10, v_params_3674_);
lean_closure_set(v___f_3704_, 11, v___x_3675_);
lean_closure_set(v___f_3704_, 12, v___x_3676_);
lean_closure_set(v___f_3704_, 13, v_heq_3677_);
lean_closure_set(v___f_3704_, 14, v_val_3678_);
lean_closure_set(v___f_3704_, 15, v_tail_3679_);
lean_closure_set(v___f_3704_, 16, v_alts_3691_);
lean_closure_set(v___f_3704_, 17, v___x_3702_);
lean_closure_set(v___f_3704_, 18, v___x_3703_);
lean_closure_set(v___f_3704_, 19, v___x_3682_);
lean_closure_set(v___f_3704_, 20, v___x_3683_);
lean_closure_set(v___f_3704_, 21, v_declName_3684_);
lean_closure_set(v___f_3704_, 22, v_levelParams_3685_);
lean_closure_set(v___f_3704_, 23, v_numIndices_3662_);
lean_closure_set(v___f_3704_, 24, v___x_3686_);
lean_closure_set(v___f_3704_, 25, v___x_3687_);
lean_closure_set(v___f_3704_, 26, v_numParams_3688_);
lean_closure_set(v___f_3704_, 27, v_snd_3689_);
lean_closure_set(v___f_3704_, 28, v___x_3690_);
lean_closure_set(v___f_3704_, 29, v___x_3698_);
v___x_3705_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3690_, v___x_3698_, v___f_3704_, v___x_3666_, v___x_3666_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
return v___x_3705_;
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_numIndices_3662_ = stack[0].m_obj;
lean_object* v___x_3663_ = stack[1].m_obj;
lean_object* v_motive_3664_ = stack[2].m_obj;
lean_object* v___x_3665_ = stack[3].m_obj;
uint8_t v___x_3666_ = stack[4].m_num;
uint8_t v___x_3667_ = stack[5].m_num;
uint8_t v___x_3668_ = stack[6].m_num;
lean_object* v_is_3669_ = stack[7].m_obj;
lean_object* v___x_3670_ = stack[8].m_obj;
lean_object* v___x_3671_ = stack[9].m_obj;
lean_object* v___x_3672_ = stack[10].m_obj;
lean_object* v___x_3673_ = stack[11].m_obj;
lean_object* v_params_3674_ = stack[12].m_obj;
lean_object* v___x_3675_ = stack[13].m_obj;
lean_object* v___x_3676_ = stack[14].m_obj;
lean_object* v_heq_3677_ = stack[15].m_obj;
lean_object* v_val_3678_ = stack[16].m_obj;
lean_object* v_tail_3679_ = stack[17].m_obj;
size_t v_sz_3680_ = stack[18].m_num;
size_t v___x_3681_ = stack[19].m_num;
lean_object* v___x_3682_ = stack[20].m_obj;
lean_object* v___x_3683_ = stack[21].m_obj;
lean_object* v_declName_3684_ = stack[22].m_obj;
lean_object* v_levelParams_3685_ = stack[23].m_obj;
lean_object* v___x_3686_ = stack[24].m_obj;
lean_object* v___x_3687_ = stack[25].m_obj;
lean_object* v_numParams_3688_ = stack[26].m_obj;
lean_object* v_snd_3689_ = stack[27].m_obj;
lean_object* v___x_3690_ = stack[28].m_obj;
lean_object* v_alts_3691_ = stack[29].m_obj;
lean_object* v___y_3692_ = stack[30].m_obj;
lean_object* v___y_3693_ = stack[31].m_obj;
lean_object* v___y_3694_ = stack[32].m_obj;
lean_object* v___y_3695_ = stack[33].m_obj;
lean_object* v_res_3706_;
v_res_3706_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3662_, v___x_3663_, v_motive_3664_, v___x_3665_, v___x_3666_, v___x_3667_, v___x_3668_, v_is_3669_, v___x_3670_, v___x_3671_, v___x_3672_, v___x_3673_, v_params_3674_, v___x_3675_, v___x_3676_, v_heq_3677_, v_val_3678_, v_tail_3679_, v_sz_3680_, v___x_3681_, v___x_3682_, v___x_3683_, v_declName_3684_, v_levelParams_3685_, v___x_3686_, v___x_3687_, v_numParams_3688_, v_snd_3689_, v___x_3690_, v_alts_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
stack->m_obj
 = v_res_3706_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3707_ = _args[0];
lean_object* v___x_3708_ = _args[1];
lean_object* v_motive_3709_ = _args[2];
lean_object* v___x_3710_ = _args[3];
lean_object* v___x_3711_ = _args[4];
lean_object* v___x_3712_ = _args[5];
lean_object* v___x_3713_ = _args[6];
lean_object* v_is_3714_ = _args[7];
lean_object* v___x_3715_ = _args[8];
lean_object* v___x_3716_ = _args[9];
lean_object* v___x_3717_ = _args[10];
lean_object* v___x_3718_ = _args[11];
lean_object* v_params_3719_ = _args[12];
lean_object* v___x_3720_ = _args[13];
lean_object* v___x_3721_ = _args[14];
lean_object* v_heq_3722_ = _args[15];
lean_object* v_val_3723_ = _args[16];
lean_object* v_tail_3724_ = _args[17];
lean_object* v_sz_3725_ = _args[18];
lean_object* v___x_3726_ = _args[19];
lean_object* v___x_3727_ = _args[20];
lean_object* v___x_3728_ = _args[21];
lean_object* v_declName_3729_ = _args[22];
lean_object* v_levelParams_3730_ = _args[23];
lean_object* v___x_3731_ = _args[24];
lean_object* v___x_3732_ = _args[25];
lean_object* v_numParams_3733_ = _args[26];
lean_object* v_snd_3734_ = _args[27];
lean_object* v___x_3735_ = _args[28];
lean_object* v_alts_3736_ = _args[29];
lean_object* v___y_3737_ = _args[30];
lean_object* v___y_3738_ = _args[31];
lean_object* v___y_3739_ = _args[32];
lean_object* v___y_3740_ = _args[33];
lean_object* v___y_3741_ = _args[34];
_start:
{
uint8_t v___x_16488__boxed_3742_; uint8_t v___x_16489__boxed_3743_; uint8_t v___x_16490__boxed_3744_; size_t v_sz_boxed_3745_; size_t v___x_16499__boxed_3746_; lean_object* v_res_3747_; 
v___x_16488__boxed_3742_ = lean_unbox(v___x_3711_);
v___x_16489__boxed_3743_ = lean_unbox(v___x_3712_);
v___x_16490__boxed_3744_ = lean_unbox(v___x_3713_);
v_sz_boxed_3745_ = lean_unbox_usize(v_sz_3725_);
lean_dec(v_sz_3725_);
v___x_16499__boxed_3746_ = lean_unbox_usize(v___x_3726_);
lean_dec(v___x_3726_);
v_res_3747_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3707_, v___x_3708_, v_motive_3709_, v___x_3710_, v___x_16488__boxed_3742_, v___x_16489__boxed_3743_, v___x_16490__boxed_3744_, v_is_3714_, v___x_3715_, v___x_3716_, v___x_3717_, v___x_3718_, v_params_3719_, v___x_3720_, v___x_3721_, v_heq_3722_, v_val_3723_, v_tail_3724_, v_sz_boxed_3745_, v___x_16499__boxed_3746_, v___x_3727_, v___x_3728_, v_declName_3729_, v_levelParams_3730_, v___x_3731_, v___x_3732_, v_numParams_3733_, v_snd_3734_, v___x_3735_, v_alts_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___x_3708_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3748_, lean_object* v_declInfos_3749_, lean_object* v_k_3750_, lean_object* v_kind_3751_, lean_object* v_x_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
uint8_t v_kind_boxed_3758_; lean_object* v_res_3759_; 
v_kind_boxed_3758_ = lean_unbox(v_kind_3751_);
v_res_3759_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3748_, v_declInfos_3749_, v_k_3750_, v_kind_boxed_3758_, v_x_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
return v_res_3759_;
}
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3760_, lean_object* v_k_3761_, uint8_t v_kind_3762_, lean_object* v_acc_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
lean_object* v___x_3769_; lean_object* v_toApplicative_3770_; lean_object* v_toFunctor_3771_; lean_object* v_toSeq_3772_; lean_object* v_toSeqLeft_3773_; lean_object* v_toSeqRight_3774_; lean_object* v___f_3775_; lean_object* v___f_3776_; lean_object* v___f_3777_; lean_object* v___f_3778_; lean_object* v___x_3779_; lean_object* v___f_3780_; lean_object* v___f_3781_; lean_object* v___f_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v_toApplicative_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3844_; 
v___x_3769_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3770_ = lean_ctor_get(v___x_3769_, 0);
v_toFunctor_3771_ = lean_ctor_get(v_toApplicative_3770_, 0);
v_toSeq_3772_ = lean_ctor_get(v_toApplicative_3770_, 2);
v_toSeqLeft_3773_ = lean_ctor_get(v_toApplicative_3770_, 3);
v_toSeqRight_3774_ = lean_ctor_get(v_toApplicative_3770_, 4);
v___f_3775_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3776_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3771_, 2);
v___f_3777_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3777_, 0, v_toFunctor_3771_);
v___f_3778_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3778_, 0, v_toFunctor_3771_);
v___x_3779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___f_3777_);
lean_ctor_set(v___x_3779_, 1, v___f_3778_);
lean_inc(v_toSeqRight_3774_);
v___f_3780_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3780_, 0, v_toSeqRight_3774_);
lean_inc(v_toSeqLeft_3773_);
v___f_3781_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3781_, 0, v_toSeqLeft_3773_);
lean_inc(v_toSeq_3772_);
v___f_3782_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3782_, 0, v_toSeq_3772_);
v___x_3783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3779_);
lean_ctor_set(v___x_3783_, 1, v___f_3775_);
lean_ctor_set(v___x_3783_, 2, v___f_3782_);
lean_ctor_set(v___x_3783_, 3, v___f_3781_);
lean_ctor_set(v___x_3783_, 4, v___f_3780_);
v___x_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
lean_ctor_set(v___x_3784_, 1, v___f_3776_);
v___x_3785_ = l_StateRefT_x27_instMonad___redArg(v___x_3784_);
v_toApplicative_3786_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; 
v_unused_3845_ = lean_ctor_get(v___x_3785_, 1);
lean_dec(v_unused_3845_);
v___x_3788_ = v___x_3785_;
v_isShared_3789_ = v_isSharedCheck_3844_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_toApplicative_3786_);
lean_dec(v___x_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3844_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v_toFunctor_3790_; lean_object* v_toSeq_3791_; lean_object* v_toSeqLeft_3792_; lean_object* v_toSeqRight_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3842_; 
v_toFunctor_3790_ = lean_ctor_get(v_toApplicative_3786_, 0);
v_toSeq_3791_ = lean_ctor_get(v_toApplicative_3786_, 2);
v_toSeqLeft_3792_ = lean_ctor_get(v_toApplicative_3786_, 3);
v_toSeqRight_3793_ = lean_ctor_get(v_toApplicative_3786_, 4);
v_isSharedCheck_3842_ = !lean_is_exclusive(v_toApplicative_3786_);
if (v_isSharedCheck_3842_ == 0)
{
lean_object* v_unused_3843_; 
v_unused_3843_ = lean_ctor_get(v_toApplicative_3786_, 1);
lean_dec(v_unused_3843_);
v___x_3795_ = v_toApplicative_3786_;
v_isShared_3796_ = v_isSharedCheck_3842_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_toSeqRight_3793_);
lean_inc(v_toSeqLeft_3792_);
lean_inc(v_toSeq_3791_);
lean_inc(v_toFunctor_3790_);
lean_dec(v_toApplicative_3786_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3842_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___f_3797_; lean_object* v___f_3798_; lean_object* v___f_3799_; lean_object* v___f_3800_; lean_object* v___x_3801_; lean_object* v___f_3802_; lean_object* v___f_3803_; lean_object* v___f_3804_; lean_object* v___x_3806_; 
v___f_3797_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3798_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3790_);
v___f_3799_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3799_, 0, v_toFunctor_3790_);
v___f_3800_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3800_, 0, v_toFunctor_3790_);
v___x_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___f_3799_);
lean_ctor_set(v___x_3801_, 1, v___f_3800_);
v___f_3802_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3802_, 0, v_toSeqRight_3793_);
v___f_3803_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3803_, 0, v_toSeqLeft_3792_);
v___f_3804_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3804_, 0, v_toSeq_3791_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 4, v___f_3802_);
lean_ctor_set(v___x_3795_, 3, v___f_3803_);
lean_ctor_set(v___x_3795_, 2, v___f_3804_);
lean_ctor_set(v___x_3795_, 1, v___f_3797_);
lean_ctor_set(v___x_3795_, 0, v___x_3801_);
v___x_3806_ = v___x_3795_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3841_; 
v_reuseFailAlloc_3841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3841_, 0, v___x_3801_);
lean_ctor_set(v_reuseFailAlloc_3841_, 1, v___f_3797_);
lean_ctor_set(v_reuseFailAlloc_3841_, 2, v___f_3804_);
lean_ctor_set(v_reuseFailAlloc_3841_, 3, v___f_3803_);
lean_ctor_set(v_reuseFailAlloc_3841_, 4, v___f_3802_);
v___x_3806_ = v_reuseFailAlloc_3841_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3808_; 
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 1, v___f_3798_);
lean_ctor_set(v___x_3788_, 0, v___x_3806_);
v___x_3808_ = v___x_3788_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v___f_3798_);
v___x_3808_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v___x_3809_ = lean_array_get_size(v_acc_3763_);
v___x_3810_ = lean_array_get_size(v_declInfos_3760_);
v___x_3811_ = lean_nat_dec_lt(v___x_3809_, v___x_3810_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; 
lean_dec_ref(v___x_3808_);
lean_dec_ref(v_declInfos_3760_);
lean_inc(v___y_3767_);
lean_inc_ref(v___y_3766_);
lean_inc(v___y_3765_);
lean_inc_ref(v___y_3764_);
v___x_3812_ = lean_apply_6(v_k_3761_, v_acc_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, lean_box(0));
return v___x_3812_;
}
else
{
lean_object* v___x_3813_; uint8_t v___x_3814_; lean_object* v___x_3815_; lean_object* v___f_3816_; lean_object* v___f_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v_snd_3822_; lean_object* v_fst_3823_; lean_object* v_fst_3824_; lean_object* v_snd_3825_; lean_object* v___x_3826_; lean_object* v___f_3827_; lean_object* v___x_3828_; 
v___x_3813_ = lean_box(0);
v___x_3814_ = 0;
v___x_3815_ = l_Lean_instInhabitedExpr;
v___f_3816_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3816_, 0, v___x_3808_);
lean_closure_set(v___f_3816_, 1, v___x_3815_);
v___f_3817_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3817_, 0, v___f_3816_);
v___x_3818_ = lean_box(v___x_3814_);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3818_);
lean_ctor_set(v___x_3819_, 1, v___f_3817_);
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3813_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_array_get(v___x_3820_, v_declInfos_3760_, v___x_3809_);
lean_dec_ref_known(v___x_3820_, 2);
v_snd_3822_ = lean_ctor_get(v___x_3821_, 1);
lean_inc(v_snd_3822_);
v_fst_3823_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_fst_3823_);
lean_dec(v___x_3821_);
v_fst_3824_ = lean_ctor_get(v_snd_3822_, 0);
lean_inc(v_fst_3824_);
v_snd_3825_ = lean_ctor_get(v_snd_3822_, 1);
lean_inc(v_snd_3825_);
lean_dec(v_snd_3822_);
v___x_3826_ = lean_box(v_kind_3762_);
lean_inc_ref(v_acc_3763_);
v___f_3827_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3827_, 0, v_acc_3763_);
lean_closure_set(v___f_3827_, 1, v_declInfos_3760_);
lean_closure_set(v___f_3827_, 2, v_k_3761_);
lean_closure_set(v___f_3827_, 3, v___x_3826_);
lean_inc(v___y_3767_);
lean_inc_ref(v___y_3766_);
lean_inc(v___y_3765_);
lean_inc_ref(v___y_3764_);
v___x_3828_ = lean_apply_6(v_snd_3825_, v_acc_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, lean_box(0));
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; uint8_t v___x_3830_; lean_object* v___x_3831_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3828_, 1);
v___x_3830_ = lean_unbox(v_fst_3824_);
lean_dec(v_fst_3824_);
v___x_3831_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3823_, v___x_3830_, v_a_3829_, v___f_3827_, v_kind_3762_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
return v___x_3831_;
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref(v___f_3827_);
lean_dec(v_fst_3824_);
lean_dec(v_fst_3823_);
v_a_3832_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3828_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3828_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
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
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_3760_ = stack[0].m_obj;
lean_object* v_k_3761_ = stack[1].m_obj;
uint8_t v_kind_3762_ = stack[2].m_num;
lean_object* v_acc_3763_ = stack[3].m_obj;
lean_object* v___y_3764_ = stack[4].m_obj;
lean_object* v___y_3765_ = stack[5].m_obj;
lean_object* v___y_3766_ = stack[6].m_obj;
lean_object* v___y_3767_ = stack[7].m_obj;
lean_object* v_res_3846_;
v_res_3846_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3760_, v_k_3761_, v_kind_3762_, v_acc_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
stack->m_obj
 = v_res_3846_;
}
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3847_, lean_object* v_declInfos_3848_, lean_object* v_k_3849_, uint8_t v_kind_3850_, lean_object* v_x_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3857_ = lean_array_push(v_acc_3847_, v_x_3851_);
v___x_3858_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3848_, v_k_3849_, v_kind_3850_, v___x_3857_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
return v___x_3858_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_acc_3847_ = stack[0].m_obj;
lean_object* v_declInfos_3848_ = stack[1].m_obj;
lean_object* v_k_3849_ = stack[2].m_obj;
uint8_t v_kind_3850_ = stack[3].m_num;
lean_object* v_x_3851_ = stack[4].m_obj;
lean_object* v___y_3852_ = stack[5].m_obj;
lean_object* v___y_3853_ = stack[6].m_obj;
lean_object* v___y_3854_ = stack[7].m_obj;
lean_object* v___y_3855_ = stack[8].m_obj;
lean_object* v_res_3859_;
v_res_3859_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3847_, v_declInfos_3848_, v_k_3849_, v_kind_3850_, v_x_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
stack->m_obj
 = v_res_3859_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3860_, lean_object* v_k_3861_, lean_object* v_kind_3862_, lean_object* v_acc_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
uint8_t v_kind_boxed_3869_; lean_object* v_res_3870_; 
v_kind_boxed_3869_ = lean_unbox(v_kind_3862_);
v_res_3870_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3860_, v_k_3861_, v_kind_boxed_3869_, v_acc_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
return v_res_3870_;
}
}
lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3871_, lean_object* v_k_3872_, uint8_t v_kind_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3879_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3880_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3871_, v_k_3872_, v_kind_3873_, v___x_3879_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
return v___x_3880_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_3871_ = stack[0].m_obj;
lean_object* v_k_3872_ = stack[1].m_obj;
uint8_t v_kind_3873_ = stack[2].m_num;
lean_object* v___y_3874_ = stack[3].m_obj;
lean_object* v___y_3875_ = stack[4].m_obj;
lean_object* v___y_3876_ = stack[5].m_obj;
lean_object* v___y_3877_ = stack[6].m_obj;
lean_object* v_res_3881_;
v_res_3881_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3871_, v_k_3872_, v_kind_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
stack->m_obj
 = v_res_3881_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3882_, lean_object* v_k_3883_, lean_object* v_kind_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
uint8_t v_kind_boxed_3890_; lean_object* v_res_3891_; 
v_kind_boxed_3890_ = lean_unbox(v_kind_3884_);
v_res_3891_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3882_, v_k_3883_, v_kind_boxed_3890_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_);
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3887_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
return v_res_3891_;
}
}
lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3892_, lean_object* v_k_3893_, uint8_t v_kind_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
size_t v_sz_3900_; size_t v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; 
v_sz_3900_ = lean_array_size(v_declInfos_3892_);
v___x_3901_ = ((size_t)0ULL);
v___x_3902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3900_, v___x_3901_, v_declInfos_3892_);
v___x_3903_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3902_, v_k_3893_, v_kind_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
return v___x_3903_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_3892_ = stack[0].m_obj;
lean_object* v_k_3893_ = stack[1].m_obj;
uint8_t v_kind_3894_ = stack[2].m_num;
lean_object* v___y_3895_ = stack[3].m_obj;
lean_object* v___y_3896_ = stack[4].m_obj;
lean_object* v___y_3897_ = stack[5].m_obj;
lean_object* v___y_3898_ = stack[6].m_obj;
lean_object* v_res_3904_;
v_res_3904_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3892_, v_k_3893_, v_kind_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
stack->m_obj
 = v_res_3904_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3905_, lean_object* v_k_3906_, lean_object* v_kind_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
uint8_t v_kind_boxed_3913_; lean_object* v_res_3914_; 
v_kind_boxed_3913_ = lean_unbox(v_kind_3907_);
v_res_3914_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3905_, v_k_3906_, v_kind_boxed_3913_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
lean_dec(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
return v_res_3914_;
}
}
lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3915_, lean_object* v_k_3916_, uint8_t v_kind_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_){
_start:
{
size_t v_sz_3923_; size_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_sz_3923_ = lean_array_size(v_declInfos_3915_);
v___x_3924_ = ((size_t)0ULL);
v___x_3925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3923_, v___x_3924_, v_declInfos_3915_);
v___x_3926_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3925_, v_k_3916_, v_kind_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
return v___x_3926_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declInfos_3915_ = stack[0].m_obj;
lean_object* v_k_3916_ = stack[1].m_obj;
uint8_t v_kind_3917_ = stack[2].m_num;
lean_object* v___y_3918_ = stack[3].m_obj;
lean_object* v___y_3919_ = stack[4].m_obj;
lean_object* v___y_3920_ = stack[5].m_obj;
lean_object* v___y_3921_ = stack[6].m_obj;
lean_object* v_res_3927_;
v_res_3927_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3915_, v_k_3916_, v_kind_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
stack->m_obj
 = v_res_3927_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3928_, lean_object* v_k_3929_, lean_object* v_kind_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
uint8_t v_kind_boxed_3936_; lean_object* v_res_3937_; 
v_kind_boxed_3936_ = lean_unbox(v_kind_3930_);
v_res_3937_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3928_, v_k_3929_, v_kind_boxed_3936_, v___y_3931_, v___y_3932_, v___y_3933_, v___y_3934_);
lean_dec(v___y_3934_);
lean_dec_ref(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
return v_res_3937_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v___x_3940_ = lean_box(0);
v___x_3941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3942_ = l_Lean_mkConst(v___x_3941_, v___x_3940_);
return v___x_3942_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3943_, lean_object* v_v_3944_, lean_object* v___x_3945_, lean_object* v___x_3946_, lean_object* v___x_3947_, lean_object* v_motive_3948_, uint8_t v___x_3949_, uint8_t v___x_3950_, uint8_t v___x_3951_, lean_object* v_zs12_3952_, lean_object* v_is_3953_, lean_object* v_fields1_3954_, lean_object* v_fields2_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v_e_3971_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
lean_inc_ref(v___x_3947_);
v___x_3981_ = l_Lean_mkAppN(v___x_3947_, v_fields1_3954_);
v___x_3982_ = l_Lean_mkAppN(v___x_3947_, v_fields2_3955_);
lean_inc(v___x_3945_);
v___x_3983_ = l_Lean_mkNatLit(v___x_3945_);
v___x_3984_ = l_Lean_Meta_mkEqRefl(v___x_3983_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3986_ = lean_unsigned_to_nat(3u);
v___x_3987_ = lean_mk_empty_array_with_capacity(v___x_3986_);
v___x_3988_ = lean_array_push(v___x_3987_, v___x_3981_);
v___x_3989_ = lean_array_push(v___x_3988_, v___x_3982_);
v___x_3990_ = lean_array_push(v___x_3989_, v_a_3985_);
v___x_3991_ = l_Array_append___redArg(v_is_3953_, v___x_3990_);
lean_dec_ref(v___x_3990_);
v___x_3992_ = l_Lean_mkAppN(v_motive_3948_, v___x_3991_);
lean_dec_ref(v___x_3991_);
v___x_3993_ = l_Lean_Meta_mkForallFVars(v_zs12_3952_, v___x_3992_, v___x_3949_, v___x_3950_, v___x_3950_, v___x_3951_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_3993_) == 0)
{
lean_object* v_a_3994_; lean_object* v___x_3995_; uint8_t v___x_3996_; 
v_a_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_a_3994_);
lean_dec_ref_known(v___x_3993_, 1);
v___x_3995_ = lean_array_get_size(v_zs12_3952_);
v___x_3996_ = lean_nat_dec_eq(v___x_3995_, v___x_3943_);
if (v___x_3996_ == 0)
{
v_e_3971_ = v_a_3994_;
goto v___jp_3970_;
}
else
{
lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3997_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3998_ = l_Lean_mkArrow(v___x_3997_, v_a_3994_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v_e_3971_ = v_a_3999_;
goto v___jp_3970_;
}
else
{
lean_object* v_a_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4007_; 
lean_dec(v___x_3945_);
lean_dec(v_v_3944_);
lean_dec(v___x_3943_);
v_a_4000_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_4002_ = v___x_3998_;
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_a_4000_);
lean_dec(v___x_3998_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4007_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4005_; 
if (v_isShared_4003_ == 0)
{
v___x_4005_ = v___x_4002_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec(v___x_3945_);
lean_dec(v_v_3944_);
lean_dec(v___x_3943_);
v_a_4008_ = lean_ctor_get(v___x_3993_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3993_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_3993_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_3993_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec_ref(v___x_3982_);
lean_dec_ref(v___x_3981_);
lean_dec_ref(v_is_3953_);
lean_dec_ref(v_motive_3948_);
lean_dec(v___x_3945_);
lean_dec(v_v_3944_);
lean_dec(v___x_3943_);
v_a_4016_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_3984_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_3984_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
v___jp_3961_:
{
lean_object* v___x_3964_; uint8_t v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3964_ = lean_array_get_size(v_zs12_3952_);
v___x_3965_ = lean_nat_dec_eq(v___x_3964_, v___x_3943_);
v___x_3966_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3966_, 0, v___x_3964_);
lean_ctor_set(v___x_3966_, 1, v___x_3943_);
lean_ctor_set_uint8(v___x_3966_, sizeof(void*)*2, v___x_3965_);
v___x_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___y_3963_);
lean_ctor_set(v___x_3967_, 1, v___y_3962_);
v___x_3968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
lean_ctor_set(v___x_3968_, 1, v___x_3966_);
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
return v___x_3969_;
}
v___jp_3970_:
{
if (lean_obj_tag(v_v_3944_) == 1)
{
lean_object* v_str_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
lean_dec(v___x_3945_);
v_str_3972_ = lean_ctor_get(v_v_3944_, 1);
lean_inc_ref(v_str_3972_);
lean_dec_ref_known(v_v_3944_, 2);
v___x_3973_ = lean_box(0);
v___x_3974_ = l_Lean_Name_str___override(v___x_3973_, v_str_3972_);
v___y_3962_ = v_e_3971_;
v___y_3963_ = v___x_3974_;
goto v___jp_3961_;
}
else
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
lean_dec(v_v_3944_);
v___x_3975_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3976_ = lean_nat_add(v___x_3945_, v___x_3946_);
lean_dec(v___x_3945_);
v___x_3977_ = l_Nat_reprFast(v___x_3976_);
v___x_3978_ = lean_string_append(v___x_3975_, v___x_3977_);
lean_dec_ref(v___x_3977_);
v___x_3979_ = lean_box(0);
v___x_3980_ = l_Lean_Name_str___override(v___x_3979_, v___x_3978_);
v___y_3962_ = v_e_3971_;
v___y_3963_ = v___x_3980_;
goto v___jp_3961_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3943_ = stack[0].m_obj;
lean_object* v_v_3944_ = stack[1].m_obj;
lean_object* v___x_3945_ = stack[2].m_obj;
lean_object* v___x_3946_ = stack[3].m_obj;
lean_object* v___x_3947_ = stack[4].m_obj;
lean_object* v_motive_3948_ = stack[5].m_obj;
uint8_t v___x_3949_ = stack[6].m_num;
uint8_t v___x_3950_ = stack[7].m_num;
uint8_t v___x_3951_ = stack[8].m_num;
lean_object* v_zs12_3952_ = stack[9].m_obj;
lean_object* v_is_3953_ = stack[10].m_obj;
lean_object* v_fields1_3954_ = stack[11].m_obj;
lean_object* v_fields2_3955_ = stack[12].m_obj;
lean_object* v___y_3956_ = stack[13].m_obj;
lean_object* v___y_3957_ = stack[14].m_obj;
lean_object* v___y_3958_ = stack[15].m_obj;
lean_object* v___y_3959_ = stack[16].m_obj;
lean_object* v_res_4024_;
v_res_4024_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3943_, v_v_3944_, v___x_3945_, v___x_3946_, v___x_3947_, v_motive_3948_, v___x_3949_, v___x_3950_, v___x_3951_, v_zs12_3952_, v_is_3953_, v_fields1_3954_, v_fields2_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
stack->m_obj
 = v_res_4024_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_4025_ = _args[0];
lean_object* v_v_4026_ = _args[1];
lean_object* v___x_4027_ = _args[2];
lean_object* v___x_4028_ = _args[3];
lean_object* v___x_4029_ = _args[4];
lean_object* v_motive_4030_ = _args[5];
lean_object* v___x_4031_ = _args[6];
lean_object* v___x_4032_ = _args[7];
lean_object* v___x_4033_ = _args[8];
lean_object* v_zs12_4034_ = _args[9];
lean_object* v_is_4035_ = _args[10];
lean_object* v_fields1_4036_ = _args[11];
lean_object* v_fields2_4037_ = _args[12];
lean_object* v___y_4038_ = _args[13];
lean_object* v___y_4039_ = _args[14];
lean_object* v___y_4040_ = _args[15];
lean_object* v___y_4041_ = _args[16];
lean_object* v___y_4042_ = _args[17];
_start:
{
uint8_t v___x_17021__boxed_4043_; uint8_t v___x_17022__boxed_4044_; uint8_t v___x_17023__boxed_4045_; lean_object* v_res_4046_; 
v___x_17021__boxed_4043_ = lean_unbox(v___x_4031_);
v___x_17022__boxed_4044_ = lean_unbox(v___x_4032_);
v___x_17023__boxed_4045_ = lean_unbox(v___x_4033_);
v_res_4046_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_4025_, v_v_4026_, v___x_4027_, v___x_4028_, v___x_4029_, v_motive_4030_, v___x_17021__boxed_4043_, v___x_17022__boxed_4044_, v___x_17023__boxed_4045_, v_zs12_4034_, v_is_4035_, v_fields1_4036_, v_fields2_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
lean_dec_ref(v_fields2_4037_);
lean_dec_ref(v_fields1_4036_);
lean_dec_ref(v_zs12_4034_);
lean_dec(v___x_4028_);
return v_res_4046_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_4047_, lean_object* v_params_4048_, lean_object* v_motive_4049_, size_t v_sz_4050_, size_t v_i_4051_, lean_object* v_bs_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_){
_start:
{
uint8_t v___x_4058_; 
v___x_4058_ = lean_usize_dec_lt(v_i_4051_, v_sz_4050_);
if (v___x_4058_ == 0)
{
lean_object* v___x_4059_; 
lean_dec_ref(v_motive_4049_);
lean_dec(v_tail_4047_);
v___x_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4059_, 0, v_bs_4052_);
return v___x_4059_;
}
else
{
lean_object* v___x_4060_; lean_object* v___x_4061_; uint8_t v___x_4062_; uint8_t v___x_4063_; lean_object* v_v_4064_; lean_object* v_bs_x27_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___f_4072_; lean_object* v___x_4073_; 
v___x_4060_ = lean_unsigned_to_nat(0u);
v___x_4061_ = lean_unsigned_to_nat(1u);
v___x_4062_ = 0;
v___x_4063_ = 1;
v_v_4064_ = lean_array_uget(v_bs_4052_, v_i_4051_);
v_bs_x27_4065_ = lean_array_uset(v_bs_4052_, v_i_4051_, v___x_4060_);
v___x_4066_ = lean_usize_to_nat(v_i_4051_);
lean_inc(v_tail_4047_);
lean_inc(v_v_4064_);
v___x_4067_ = l_Lean_mkConst(v_v_4064_, v_tail_4047_);
v___x_4068_ = l_Lean_mkAppN(v___x_4067_, v_params_4048_);
v___x_4069_ = lean_box(v___x_4062_);
v___x_4070_ = lean_box(v___x_4058_);
v___x_4071_ = lean_box(v___x_4063_);
lean_inc_ref(v_motive_4049_);
lean_inc_ref(v___x_4068_);
v___f_4072_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_4072_, 0, v___x_4060_);
lean_closure_set(v___f_4072_, 1, v_v_4064_);
lean_closure_set(v___f_4072_, 2, v___x_4066_);
lean_closure_set(v___f_4072_, 3, v___x_4061_);
lean_closure_set(v___f_4072_, 4, v___x_4068_);
lean_closure_set(v___f_4072_, 5, v_motive_4049_);
lean_closure_set(v___f_4072_, 6, v___x_4069_);
lean_closure_set(v___f_4072_, 7, v___x_4070_);
lean_closure_set(v___f_4072_, 8, v___x_4071_);
v___x_4073_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_4068_, v___f_4072_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; size_t v___x_4075_; size_t v___x_4076_; lean_object* v___x_4077_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4073_, 1);
v___x_4075_ = ((size_t)1ULL);
v___x_4076_ = lean_usize_add(v_i_4051_, v___x_4075_);
v___x_4077_ = lean_array_uset(v_bs_x27_4065_, v_i_4051_, v_a_4074_);
v_i_4051_ = v___x_4076_;
v_bs_4052_ = v___x_4077_;
goto _start;
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec_ref(v_bs_x27_4065_);
lean_dec_ref(v_motive_4049_);
lean_dec(v_tail_4047_);
v_a_4079_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4073_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4073_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_4047_ = stack[0].m_obj;
lean_object* v_params_4048_ = stack[1].m_obj;
lean_object* v_motive_4049_ = stack[2].m_obj;
size_t v_sz_4050_ = stack[3].m_num;
size_t v_i_4051_ = stack[4].m_num;
lean_object* v_bs_4052_ = stack[5].m_obj;
lean_object* v___y_4053_ = stack[6].m_obj;
lean_object* v___y_4054_ = stack[7].m_obj;
lean_object* v___y_4055_ = stack[8].m_obj;
lean_object* v___y_4056_ = stack[9].m_obj;
lean_object* v_res_4087_;
v_res_4087_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4047_, v_params_4048_, v_motive_4049_, v_sz_4050_, v_i_4051_, v_bs_4052_, v___y_4053_, v___y_4054_, v___y_4055_, v___y_4056_);
stack->m_obj
 = v_res_4087_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_4088_, lean_object* v_params_4089_, lean_object* v_motive_4090_, lean_object* v_sz_4091_, lean_object* v_i_4092_, lean_object* v_bs_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
size_t v_sz_boxed_4099_; size_t v_i_boxed_4100_; lean_object* v_res_4101_; 
v_sz_boxed_4099_ = lean_unbox_usize(v_sz_4091_);
lean_dec(v_sz_4091_);
v_i_boxed_4100_ = lean_unbox_usize(v_i_4092_);
lean_dec(v_i_4092_);
v_res_4101_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4088_, v_params_4089_, v_motive_4090_, v_sz_boxed_4099_, v_i_boxed_4100_, v_bs_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec_ref(v_params_4089_);
return v_res_4101_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_4104_, lean_object* v_tail_4105_, lean_object* v_params_4106_, lean_object* v_numIndices_4107_, lean_object* v___x_4108_, lean_object* v___x_4109_, uint8_t v___x_4110_, uint8_t v___x_4111_, uint8_t v___x_4112_, lean_object* v_is_4113_, lean_object* v___x_4114_, lean_object* v___x_4115_, lean_object* v___x_4116_, lean_object* v___x_4117_, lean_object* v___x_4118_, lean_object* v___x_4119_, lean_object* v_heq_4120_, lean_object* v_val_4121_, lean_object* v___x_4122_, lean_object* v_declName_4123_, lean_object* v_levelParams_4124_, lean_object* v___x_4125_, lean_object* v___x_4126_, lean_object* v_numParams_4127_, lean_object* v___x_4128_, lean_object* v_motive_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___x_4135_; size_t v_sz_4136_; size_t v___x_4137_; lean_object* v___x_4138_; 
v___x_4135_ = lean_array_mk(v_ctors_4104_);
v_sz_4136_ = lean_array_size(v___x_4135_);
v___x_4137_ = ((size_t)0ULL);
lean_inc_ref(v___x_4135_);
lean_inc_ref(v_motive_4129_);
lean_inc(v_tail_4105_);
v___x_4138_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4105_, v_params_4106_, v_motive_4129_, v_sz_4136_, v___x_4137_, v___x_4135_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4140_; lean_object* v_fst_4141_; lean_object* v_snd_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___f_4148_; uint8_t v___x_4149_; lean_object* v___x_4150_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v___x_4140_ = l_Array_unzip___redArg(v_a_4139_);
lean_dec(v_a_4139_);
v_fst_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_fst_4141_);
v_snd_4142_ = lean_ctor_get(v___x_4140_, 1);
lean_inc(v_snd_4142_);
lean_dec_ref(v___x_4140_);
v___x_4143_ = lean_box(v___x_4110_);
v___x_4144_ = lean_box(v___x_4111_);
v___x_4145_ = lean_box(v___x_4112_);
v___x_4146_ = lean_box_usize(v_sz_4136_);
v___x_4147_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4148_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4148_, 0, v_numIndices_4107_);
lean_closure_set(v___f_4148_, 1, v___x_4108_);
lean_closure_set(v___f_4148_, 2, v_motive_4129_);
lean_closure_set(v___f_4148_, 3, v___x_4109_);
lean_closure_set(v___f_4148_, 4, v___x_4143_);
lean_closure_set(v___f_4148_, 5, v___x_4144_);
lean_closure_set(v___f_4148_, 6, v___x_4145_);
lean_closure_set(v___f_4148_, 7, v_is_4113_);
lean_closure_set(v___f_4148_, 8, v___x_4114_);
lean_closure_set(v___f_4148_, 9, v___x_4115_);
lean_closure_set(v___f_4148_, 10, v___x_4116_);
lean_closure_set(v___f_4148_, 11, v___x_4117_);
lean_closure_set(v___f_4148_, 12, v_params_4106_);
lean_closure_set(v___f_4148_, 13, v___x_4118_);
lean_closure_set(v___f_4148_, 14, v___x_4119_);
lean_closure_set(v___f_4148_, 15, v_heq_4120_);
lean_closure_set(v___f_4148_, 16, v_val_4121_);
lean_closure_set(v___f_4148_, 17, v_tail_4105_);
lean_closure_set(v___f_4148_, 18, v___x_4146_);
lean_closure_set(v___f_4148_, 19, v___x_4147_);
lean_closure_set(v___f_4148_, 20, v___x_4135_);
lean_closure_set(v___f_4148_, 21, v___x_4122_);
lean_closure_set(v___f_4148_, 22, v_declName_4123_);
lean_closure_set(v___f_4148_, 23, v_levelParams_4124_);
lean_closure_set(v___f_4148_, 24, v___x_4125_);
lean_closure_set(v___f_4148_, 25, v___x_4126_);
lean_closure_set(v___f_4148_, 26, v_numParams_4127_);
lean_closure_set(v___f_4148_, 27, v_snd_4142_);
lean_closure_set(v___f_4148_, 28, v___x_4128_);
v___x_4149_ = 0;
v___x_4150_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_4141_, v___f_4148_, v___x_4149_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
return v___x_4150_;
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
lean_dec_ref(v___x_4135_);
lean_dec_ref(v_motive_4129_);
lean_dec_ref(v___x_4128_);
lean_dec(v_numParams_4127_);
lean_dec(v___x_4126_);
lean_dec(v___x_4125_);
lean_dec(v_levelParams_4124_);
lean_dec(v_declName_4123_);
lean_dec_ref(v___x_4122_);
lean_dec_ref(v_val_4121_);
lean_dec_ref(v_heq_4120_);
lean_dec_ref(v___x_4119_);
lean_dec_ref(v___x_4118_);
lean_dec(v___x_4117_);
lean_dec(v___x_4116_);
lean_dec_ref(v___x_4115_);
lean_dec_ref(v___x_4114_);
lean_dec_ref(v_is_4113_);
lean_dec_ref(v___x_4109_);
lean_dec(v___x_4108_);
lean_dec(v_numIndices_4107_);
lean_dec_ref(v_params_4106_);
lean_dec(v_tail_4105_);
v_a_4151_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4138_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4138_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctors_4104_ = stack[0].m_obj;
lean_object* v_tail_4105_ = stack[1].m_obj;
lean_object* v_params_4106_ = stack[2].m_obj;
lean_object* v_numIndices_4107_ = stack[3].m_obj;
lean_object* v___x_4108_ = stack[4].m_obj;
lean_object* v___x_4109_ = stack[5].m_obj;
uint8_t v___x_4110_ = stack[6].m_num;
uint8_t v___x_4111_ = stack[7].m_num;
uint8_t v___x_4112_ = stack[8].m_num;
lean_object* v_is_4113_ = stack[9].m_obj;
lean_object* v___x_4114_ = stack[10].m_obj;
lean_object* v___x_4115_ = stack[11].m_obj;
lean_object* v___x_4116_ = stack[12].m_obj;
lean_object* v___x_4117_ = stack[13].m_obj;
lean_object* v___x_4118_ = stack[14].m_obj;
lean_object* v___x_4119_ = stack[15].m_obj;
lean_object* v_heq_4120_ = stack[16].m_obj;
lean_object* v_val_4121_ = stack[17].m_obj;
lean_object* v___x_4122_ = stack[18].m_obj;
lean_object* v_declName_4123_ = stack[19].m_obj;
lean_object* v_levelParams_4124_ = stack[20].m_obj;
lean_object* v___x_4125_ = stack[21].m_obj;
lean_object* v___x_4126_ = stack[22].m_obj;
lean_object* v_numParams_4127_ = stack[23].m_obj;
lean_object* v___x_4128_ = stack[24].m_obj;
lean_object* v_motive_4129_ = stack[25].m_obj;
lean_object* v___y_4130_ = stack[26].m_obj;
lean_object* v___y_4131_ = stack[27].m_obj;
lean_object* v___y_4132_ = stack[28].m_obj;
lean_object* v___y_4133_ = stack[29].m_obj;
lean_object* v_res_4159_;
v_res_4159_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4104_, v_tail_4105_, v_params_4106_, v_numIndices_4107_, v___x_4108_, v___x_4109_, v___x_4110_, v___x_4111_, v___x_4112_, v_is_4113_, v___x_4114_, v___x_4115_, v___x_4116_, v___x_4117_, v___x_4118_, v___x_4119_, v_heq_4120_, v_val_4121_, v___x_4122_, v_declName_4123_, v_levelParams_4124_, v___x_4125_, v___x_4126_, v_numParams_4127_, v___x_4128_, v_motive_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
stack->m_obj
 = v_res_4159_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4160_ = _args[0];
lean_object* v_tail_4161_ = _args[1];
lean_object* v_params_4162_ = _args[2];
lean_object* v_numIndices_4163_ = _args[3];
lean_object* v___x_4164_ = _args[4];
lean_object* v___x_4165_ = _args[5];
lean_object* v___x_4166_ = _args[6];
lean_object* v___x_4167_ = _args[7];
lean_object* v___x_4168_ = _args[8];
lean_object* v_is_4169_ = _args[9];
lean_object* v___x_4170_ = _args[10];
lean_object* v___x_4171_ = _args[11];
lean_object* v___x_4172_ = _args[12];
lean_object* v___x_4173_ = _args[13];
lean_object* v___x_4174_ = _args[14];
lean_object* v___x_4175_ = _args[15];
lean_object* v_heq_4176_ = _args[16];
lean_object* v_val_4177_ = _args[17];
lean_object* v___x_4178_ = _args[18];
lean_object* v_declName_4179_ = _args[19];
lean_object* v_levelParams_4180_ = _args[20];
lean_object* v___x_4181_ = _args[21];
lean_object* v___x_4182_ = _args[22];
lean_object* v_numParams_4183_ = _args[23];
lean_object* v___x_4184_ = _args[24];
lean_object* v_motive_4185_ = _args[25];
lean_object* v___y_4186_ = _args[26];
lean_object* v___y_4187_ = _args[27];
lean_object* v___y_4188_ = _args[28];
lean_object* v___y_4189_ = _args[29];
lean_object* v___y_4190_ = _args[30];
_start:
{
uint8_t v___x_17388__boxed_4191_; uint8_t v___x_17389__boxed_4192_; uint8_t v___x_17390__boxed_4193_; lean_object* v_res_4194_; 
v___x_17388__boxed_4191_ = lean_unbox(v___x_4166_);
v___x_17389__boxed_4192_ = lean_unbox(v___x_4167_);
v___x_17390__boxed_4193_ = lean_unbox(v___x_4168_);
v_res_4194_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4160_, v_tail_4161_, v_params_4162_, v_numIndices_4163_, v___x_4164_, v___x_4165_, v___x_17388__boxed_4191_, v___x_17389__boxed_4192_, v___x_17390__boxed_4193_, v_is_4169_, v___x_4170_, v___x_4171_, v___x_4172_, v___x_4173_, v___x_4174_, v___x_4175_, v_heq_4176_, v_val_4177_, v___x_4178_, v_declName_4179_, v_levelParams_4180_, v___x_4181_, v___x_4182_, v_numParams_4183_, v___x_4184_, v_motive_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
return v_res_4194_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4195_, lean_object* v___x_4196_, lean_object* v_is_4197_, lean_object* v_head_4198_, lean_object* v_ctors_4199_, lean_object* v_tail_4200_, lean_object* v_params_4201_, lean_object* v_numIndices_4202_, lean_object* v___x_4203_, lean_object* v___x_4204_, lean_object* v___x_4205_, lean_object* v___x_4206_, lean_object* v___x_4207_, lean_object* v_val_4208_, lean_object* v___x_4209_, lean_object* v_declName_4210_, lean_object* v_levelParams_4211_, lean_object* v___x_4212_, lean_object* v_numParams_4213_, lean_object* v___x_4214_, lean_object* v_heq_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; uint8_t v___x_4228_; uint8_t v___x_4229_; uint8_t v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___f_4234_; lean_object* v___x_4235_; 
v___x_4221_ = lean_unsigned_to_nat(3u);
v___x_4222_ = lean_mk_empty_array_with_capacity(v___x_4221_);
lean_inc_ref(v___x_4195_);
v___x_4223_ = lean_array_push(v___x_4222_, v___x_4195_);
lean_inc_ref(v___x_4196_);
v___x_4224_ = lean_array_push(v___x_4223_, v___x_4196_);
lean_inc_ref(v_heq_4215_);
v___x_4225_ = lean_array_push(v___x_4224_, v_heq_4215_);
lean_inc_ref(v_is_4197_);
v___x_4226_ = l_Array_append___redArg(v_is_4197_, v___x_4225_);
lean_dec_ref(v___x_4225_);
v___x_4227_ = l_Lean_mkSort(v_head_4198_);
v___x_4228_ = 0;
v___x_4229_ = 1;
v___x_4230_ = 1;
v___x_4231_ = lean_box(v___x_4228_);
v___x_4232_ = lean_box(v___x_4229_);
v___x_4233_ = lean_box(v___x_4230_);
lean_inc_ref(v___x_4226_);
v___f_4234_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4234_, 0, v_ctors_4199_);
lean_closure_set(v___f_4234_, 1, v_tail_4200_);
lean_closure_set(v___f_4234_, 2, v_params_4201_);
lean_closure_set(v___f_4234_, 3, v_numIndices_4202_);
lean_closure_set(v___f_4234_, 4, v___x_4203_);
lean_closure_set(v___f_4234_, 5, v___x_4226_);
lean_closure_set(v___f_4234_, 6, v___x_4231_);
lean_closure_set(v___f_4234_, 7, v___x_4232_);
lean_closure_set(v___f_4234_, 8, v___x_4233_);
lean_closure_set(v___f_4234_, 9, v_is_4197_);
lean_closure_set(v___f_4234_, 10, v___x_4196_);
lean_closure_set(v___f_4234_, 11, v___x_4195_);
lean_closure_set(v___f_4234_, 12, v___x_4204_);
lean_closure_set(v___f_4234_, 13, v___x_4205_);
lean_closure_set(v___f_4234_, 14, v___x_4206_);
lean_closure_set(v___f_4234_, 15, v___x_4207_);
lean_closure_set(v___f_4234_, 16, v_heq_4215_);
lean_closure_set(v___f_4234_, 17, v_val_4208_);
lean_closure_set(v___f_4234_, 18, v___x_4209_);
lean_closure_set(v___f_4234_, 19, v_declName_4210_);
lean_closure_set(v___f_4234_, 20, v_levelParams_4211_);
lean_closure_set(v___f_4234_, 21, v___x_4221_);
lean_closure_set(v___f_4234_, 22, v___x_4212_);
lean_closure_set(v___f_4234_, 23, v_numParams_4213_);
lean_closure_set(v___f_4234_, 24, v___x_4214_);
v___x_4235_ = l_Lean_Meta_mkForallFVars(v___x_4226_, v___x_4227_, v___x_4228_, v___x_4229_, v___x_4229_, v___x_4230_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
lean_dec_ref(v___x_4226_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; lean_object* v___x_4239_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4235_, 1);
v___x_4237_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4238_ = 0;
v___x_4239_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4237_, v___x_4230_, v_a_4236_, v___f_4234_, v___x_4238_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
return v___x_4239_;
}
else
{
lean_object* v_a_4240_; lean_object* v___x_4242_; uint8_t v_isShared_4243_; uint8_t v_isSharedCheck_4247_; 
lean_dec_ref(v___f_4234_);
v_a_4240_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4247_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4247_ == 0)
{
v___x_4242_ = v___x_4235_;
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
else
{
lean_inc(v_a_4240_);
lean_dec(v___x_4235_);
v___x_4242_ = lean_box(0);
v_isShared_4243_ = v_isSharedCheck_4247_;
goto v_resetjp_4241_;
}
v_resetjp_4241_:
{
lean_object* v___x_4245_; 
if (v_isShared_4243_ == 0)
{
v___x_4245_ = v___x_4242_;
goto v_reusejp_4244_;
}
else
{
lean_object* v_reuseFailAlloc_4246_; 
v_reuseFailAlloc_4246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_a_4240_);
v___x_4245_ = v_reuseFailAlloc_4246_;
goto v_reusejp_4244_;
}
v_reusejp_4244_:
{
return v___x_4245_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4195_ = stack[0].m_obj;
lean_object* v___x_4196_ = stack[1].m_obj;
lean_object* v_is_4197_ = stack[2].m_obj;
lean_object* v_head_4198_ = stack[3].m_obj;
lean_object* v_ctors_4199_ = stack[4].m_obj;
lean_object* v_tail_4200_ = stack[5].m_obj;
lean_object* v_params_4201_ = stack[6].m_obj;
lean_object* v_numIndices_4202_ = stack[7].m_obj;
lean_object* v___x_4203_ = stack[8].m_obj;
lean_object* v___x_4204_ = stack[9].m_obj;
lean_object* v___x_4205_ = stack[10].m_obj;
lean_object* v___x_4206_ = stack[11].m_obj;
lean_object* v___x_4207_ = stack[12].m_obj;
lean_object* v_val_4208_ = stack[13].m_obj;
lean_object* v___x_4209_ = stack[14].m_obj;
lean_object* v_declName_4210_ = stack[15].m_obj;
lean_object* v_levelParams_4211_ = stack[16].m_obj;
lean_object* v___x_4212_ = stack[17].m_obj;
lean_object* v_numParams_4213_ = stack[18].m_obj;
lean_object* v___x_4214_ = stack[19].m_obj;
lean_object* v_heq_4215_ = stack[20].m_obj;
lean_object* v___y_4216_ = stack[21].m_obj;
lean_object* v___y_4217_ = stack[22].m_obj;
lean_object* v___y_4218_ = stack[23].m_obj;
lean_object* v___y_4219_ = stack[24].m_obj;
lean_object* v_res_4248_;
v_res_4248_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4195_, v___x_4196_, v_is_4197_, v_head_4198_, v_ctors_4199_, v_tail_4200_, v_params_4201_, v_numIndices_4202_, v___x_4203_, v___x_4204_, v___x_4205_, v___x_4206_, v___x_4207_, v_val_4208_, v___x_4209_, v_declName_4210_, v_levelParams_4211_, v___x_4212_, v_numParams_4213_, v___x_4214_, v_heq_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
stack->m_obj
 = v_res_4248_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4249_ = _args[0];
lean_object* v___x_4250_ = _args[1];
lean_object* v_is_4251_ = _args[2];
lean_object* v_head_4252_ = _args[3];
lean_object* v_ctors_4253_ = _args[4];
lean_object* v_tail_4254_ = _args[5];
lean_object* v_params_4255_ = _args[6];
lean_object* v_numIndices_4256_ = _args[7];
lean_object* v___x_4257_ = _args[8];
lean_object* v___x_4258_ = _args[9];
lean_object* v___x_4259_ = _args[10];
lean_object* v___x_4260_ = _args[11];
lean_object* v___x_4261_ = _args[12];
lean_object* v_val_4262_ = _args[13];
lean_object* v___x_4263_ = _args[14];
lean_object* v_declName_4264_ = _args[15];
lean_object* v_levelParams_4265_ = _args[16];
lean_object* v___x_4266_ = _args[17];
lean_object* v_numParams_4267_ = _args[18];
lean_object* v___x_4268_ = _args[19];
lean_object* v_heq_4269_ = _args[20];
lean_object* v___y_4270_ = _args[21];
lean_object* v___y_4271_ = _args[22];
lean_object* v___y_4272_ = _args[23];
lean_object* v___y_4273_ = _args[24];
lean_object* v___y_4274_ = _args[25];
_start:
{
lean_object* v_res_4275_; 
v_res_4275_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4249_, v___x_4250_, v_is_4251_, v_head_4252_, v_ctors_4253_, v_tail_4254_, v_params_4255_, v_numIndices_4256_, v___x_4257_, v___x_4258_, v___x_4259_, v___x_4260_, v___x_4261_, v_val_4262_, v___x_4263_, v_declName_4264_, v_levelParams_4265_, v___x_4266_, v_numParams_4267_, v___x_4268_, v_heq_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
return v_res_4275_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4276_, lean_object* v_x1_4277_, lean_object* v_indName_4278_, lean_object* v_tail_4279_, lean_object* v_params_4280_, lean_object* v_is_4281_, lean_object* v___x_4282_, lean_object* v_head_4283_, lean_object* v_ctors_4284_, lean_object* v_numIndices_4285_, lean_object* v___x_4286_, lean_object* v___x_4287_, lean_object* v_val_4288_, lean_object* v_declName_4289_, lean_object* v_levelParams_4290_, lean_object* v_numParams_4291_, lean_object* v___x_4292_, lean_object* v_x2_4293_, lean_object* v_x_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___f_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4300_ = lean_unsigned_to_nat(0u);
v___x_4301_ = lean_array_get_borrowed(v___x_4276_, v_x1_4277_, v___x_4300_);
v___x_4302_ = lean_array_get_borrowed(v___x_4276_, v_x2_4293_, v___x_4300_);
v___x_4303_ = l_Lean_mkCtorIdxName(v_indName_4278_);
lean_inc(v_tail_4279_);
v___x_4304_ = l_Lean_mkConst(v___x_4303_, v_tail_4279_);
lean_inc_ref(v_params_4280_);
v___x_4305_ = l_Array_append___redArg(v_params_4280_, v_is_4281_);
v___x_4306_ = lean_mk_empty_array_with_capacity(v___x_4282_);
lean_inc_n(v___x_4301_, 2);
lean_inc_ref_n(v___x_4306_, 2);
v___x_4307_ = lean_array_push(v___x_4306_, v___x_4301_);
lean_inc_ref(v___x_4305_);
v___x_4308_ = l_Array_append___redArg(v___x_4305_, v___x_4307_);
lean_inc_ref(v___x_4304_);
v___x_4309_ = l_Lean_mkAppN(v___x_4304_, v___x_4308_);
lean_dec_ref(v___x_4308_);
lean_inc_n(v___x_4302_, 2);
v___x_4310_ = lean_array_push(v___x_4306_, v___x_4302_);
lean_inc_ref(v___x_4310_);
v___f_4311_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4311_, 0, v___x_4301_);
lean_closure_set(v___f_4311_, 1, v___x_4302_);
lean_closure_set(v___f_4311_, 2, v_is_4281_);
lean_closure_set(v___f_4311_, 3, v_head_4283_);
lean_closure_set(v___f_4311_, 4, v_ctors_4284_);
lean_closure_set(v___f_4311_, 5, v_tail_4279_);
lean_closure_set(v___f_4311_, 6, v_params_4280_);
lean_closure_set(v___f_4311_, 7, v_numIndices_4285_);
lean_closure_set(v___f_4311_, 8, v___x_4282_);
lean_closure_set(v___f_4311_, 9, v___x_4286_);
lean_closure_set(v___f_4311_, 10, v___x_4287_);
lean_closure_set(v___f_4311_, 11, v___x_4307_);
lean_closure_set(v___f_4311_, 12, v___x_4310_);
lean_closure_set(v___f_4311_, 13, v_val_4288_);
lean_closure_set(v___f_4311_, 14, v___x_4306_);
lean_closure_set(v___f_4311_, 15, v_declName_4289_);
lean_closure_set(v___f_4311_, 16, v_levelParams_4290_);
lean_closure_set(v___f_4311_, 17, v___x_4300_);
lean_closure_set(v___f_4311_, 18, v_numParams_4291_);
lean_closure_set(v___f_4311_, 19, v___x_4292_);
v___x_4312_ = l_Array_append___redArg(v___x_4305_, v___x_4310_);
lean_dec_ref(v___x_4310_);
v___x_4313_ = l_Lean_mkAppN(v___x_4304_, v___x_4312_);
lean_dec_ref(v___x_4312_);
v___x_4314_ = l_Lean_Meta_mkEq(v___x_4309_, v___x_4313_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4317_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4316_, v_a_4315_, v___f_4311_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
return v___x_4317_;
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_dec_ref(v___f_4311_);
v_a_4318_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4314_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4314_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4276_ = stack[0].m_obj;
lean_object* v_x1_4277_ = stack[1].m_obj;
lean_object* v_indName_4278_ = stack[2].m_obj;
lean_object* v_tail_4279_ = stack[3].m_obj;
lean_object* v_params_4280_ = stack[4].m_obj;
lean_object* v_is_4281_ = stack[5].m_obj;
lean_object* v___x_4282_ = stack[6].m_obj;
lean_object* v_head_4283_ = stack[7].m_obj;
lean_object* v_ctors_4284_ = stack[8].m_obj;
lean_object* v_numIndices_4285_ = stack[9].m_obj;
lean_object* v___x_4286_ = stack[10].m_obj;
lean_object* v___x_4287_ = stack[11].m_obj;
lean_object* v_val_4288_ = stack[12].m_obj;
lean_object* v_declName_4289_ = stack[13].m_obj;
lean_object* v_levelParams_4290_ = stack[14].m_obj;
lean_object* v_numParams_4291_ = stack[15].m_obj;
lean_object* v___x_4292_ = stack[16].m_obj;
lean_object* v_x2_4293_ = stack[17].m_obj;
lean_object* v_x_4294_ = stack[18].m_obj;
lean_object* v___y_4295_ = stack[19].m_obj;
lean_object* v___y_4296_ = stack[20].m_obj;
lean_object* v___y_4297_ = stack[21].m_obj;
lean_object* v___y_4298_ = stack[22].m_obj;
lean_object* v_res_4326_;
v_res_4326_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4276_, v_x1_4277_, v_indName_4278_, v_tail_4279_, v_params_4280_, v_is_4281_, v___x_4282_, v_head_4283_, v_ctors_4284_, v_numIndices_4285_, v___x_4286_, v___x_4287_, v_val_4288_, v_declName_4289_, v_levelParams_4290_, v_numParams_4291_, v___x_4292_, v_x2_4293_, v_x_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
stack->m_obj
 = v_res_4326_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4327_ = _args[0];
lean_object* v_x1_4328_ = _args[1];
lean_object* v_indName_4329_ = _args[2];
lean_object* v_tail_4330_ = _args[3];
lean_object* v_params_4331_ = _args[4];
lean_object* v_is_4332_ = _args[5];
lean_object* v___x_4333_ = _args[6];
lean_object* v_head_4334_ = _args[7];
lean_object* v_ctors_4335_ = _args[8];
lean_object* v_numIndices_4336_ = _args[9];
lean_object* v___x_4337_ = _args[10];
lean_object* v___x_4338_ = _args[11];
lean_object* v_val_4339_ = _args[12];
lean_object* v_declName_4340_ = _args[13];
lean_object* v_levelParams_4341_ = _args[14];
lean_object* v_numParams_4342_ = _args[15];
lean_object* v___x_4343_ = _args[16];
lean_object* v_x2_4344_ = _args[17];
lean_object* v_x_4345_ = _args[18];
lean_object* v___y_4346_ = _args[19];
lean_object* v___y_4347_ = _args[20];
lean_object* v___y_4348_ = _args[21];
lean_object* v___y_4349_ = _args[22];
lean_object* v___y_4350_ = _args[23];
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4327_, v_x1_4328_, v_indName_4329_, v_tail_4330_, v_params_4331_, v_is_4332_, v___x_4333_, v_head_4334_, v_ctors_4335_, v_numIndices_4336_, v___x_4337_, v___x_4338_, v_val_4339_, v_declName_4340_, v_levelParams_4341_, v_numParams_4342_, v___x_4343_, v_x2_4344_, v_x_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec_ref(v_x_4345_);
lean_dec_ref(v_x2_4344_);
lean_dec_ref(v_x1_4328_);
lean_dec_ref(v___x_4327_);
return v_res_4351_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4352_, lean_object* v_indName_4353_, lean_object* v_tail_4354_, lean_object* v_params_4355_, lean_object* v_is_4356_, lean_object* v___x_4357_, lean_object* v_head_4358_, lean_object* v_ctors_4359_, lean_object* v_numIndices_4360_, lean_object* v___x_4361_, lean_object* v___x_4362_, lean_object* v_val_4363_, lean_object* v_declName_4364_, lean_object* v_levelParams_4365_, lean_object* v_numParams_4366_, lean_object* v___x_4367_, lean_object* v_t_4368_, lean_object* v___x_4369_, lean_object* v_x1_4370_, lean_object* v_x_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v___f_4377_; uint8_t v___x_4378_; lean_object* v___x_4379_; 
v___f_4377_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4377_, 0, v___x_4352_);
lean_closure_set(v___f_4377_, 1, v_x1_4370_);
lean_closure_set(v___f_4377_, 2, v_indName_4353_);
lean_closure_set(v___f_4377_, 3, v_tail_4354_);
lean_closure_set(v___f_4377_, 4, v_params_4355_);
lean_closure_set(v___f_4377_, 5, v_is_4356_);
lean_closure_set(v___f_4377_, 6, v___x_4357_);
lean_closure_set(v___f_4377_, 7, v_head_4358_);
lean_closure_set(v___f_4377_, 8, v_ctors_4359_);
lean_closure_set(v___f_4377_, 9, v_numIndices_4360_);
lean_closure_set(v___f_4377_, 10, v___x_4361_);
lean_closure_set(v___f_4377_, 11, v___x_4362_);
lean_closure_set(v___f_4377_, 12, v_val_4363_);
lean_closure_set(v___f_4377_, 13, v_declName_4364_);
lean_closure_set(v___f_4377_, 14, v_levelParams_4365_);
lean_closure_set(v___f_4377_, 15, v_numParams_4366_);
lean_closure_set(v___f_4377_, 16, v___x_4367_);
v___x_4378_ = 0;
v___x_4379_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4368_, v___x_4369_, v___f_4377_, v___x_4378_, v___x_4378_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
return v___x_4379_;
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4352_ = stack[0].m_obj;
lean_object* v_indName_4353_ = stack[1].m_obj;
lean_object* v_tail_4354_ = stack[2].m_obj;
lean_object* v_params_4355_ = stack[3].m_obj;
lean_object* v_is_4356_ = stack[4].m_obj;
lean_object* v___x_4357_ = stack[5].m_obj;
lean_object* v_head_4358_ = stack[6].m_obj;
lean_object* v_ctors_4359_ = stack[7].m_obj;
lean_object* v_numIndices_4360_ = stack[8].m_obj;
lean_object* v___x_4361_ = stack[9].m_obj;
lean_object* v___x_4362_ = stack[10].m_obj;
lean_object* v_val_4363_ = stack[11].m_obj;
lean_object* v_declName_4364_ = stack[12].m_obj;
lean_object* v_levelParams_4365_ = stack[13].m_obj;
lean_object* v_numParams_4366_ = stack[14].m_obj;
lean_object* v___x_4367_ = stack[15].m_obj;
lean_object* v_t_4368_ = stack[16].m_obj;
lean_object* v___x_4369_ = stack[17].m_obj;
lean_object* v_x1_4370_ = stack[18].m_obj;
lean_object* v_x_4371_ = stack[19].m_obj;
lean_object* v___y_4372_ = stack[20].m_obj;
lean_object* v___y_4373_ = stack[21].m_obj;
lean_object* v___y_4374_ = stack[22].m_obj;
lean_object* v___y_4375_ = stack[23].m_obj;
lean_object* v_res_4380_;
v_res_4380_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4352_, v_indName_4353_, v_tail_4354_, v_params_4355_, v_is_4356_, v___x_4357_, v_head_4358_, v_ctors_4359_, v_numIndices_4360_, v___x_4361_, v___x_4362_, v_val_4363_, v_declName_4364_, v_levelParams_4365_, v_numParams_4366_, v___x_4367_, v_t_4368_, v___x_4369_, v_x1_4370_, v_x_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
stack->m_obj
 = v_res_4380_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4381_ = _args[0];
lean_object* v_indName_4382_ = _args[1];
lean_object* v_tail_4383_ = _args[2];
lean_object* v_params_4384_ = _args[3];
lean_object* v_is_4385_ = _args[4];
lean_object* v___x_4386_ = _args[5];
lean_object* v_head_4387_ = _args[6];
lean_object* v_ctors_4388_ = _args[7];
lean_object* v_numIndices_4389_ = _args[8];
lean_object* v___x_4390_ = _args[9];
lean_object* v___x_4391_ = _args[10];
lean_object* v_val_4392_ = _args[11];
lean_object* v_declName_4393_ = _args[12];
lean_object* v_levelParams_4394_ = _args[13];
lean_object* v_numParams_4395_ = _args[14];
lean_object* v___x_4396_ = _args[15];
lean_object* v_t_4397_ = _args[16];
lean_object* v___x_4398_ = _args[17];
lean_object* v_x1_4399_ = _args[18];
lean_object* v_x_4400_ = _args[19];
lean_object* v___y_4401_ = _args[20];
lean_object* v___y_4402_ = _args[21];
lean_object* v___y_4403_ = _args[22];
lean_object* v___y_4404_ = _args[23];
lean_object* v___y_4405_ = _args[24];
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4381_, v_indName_4382_, v_tail_4383_, v_params_4384_, v_is_4385_, v___x_4386_, v_head_4387_, v_ctors_4388_, v_numIndices_4389_, v___x_4390_, v___x_4391_, v_val_4392_, v_declName_4393_, v_levelParams_4394_, v_numParams_4395_, v___x_4396_, v_t_4397_, v___x_4398_, v_x1_4399_, v_x_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec_ref(v_x_4400_);
return v_res_4406_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4407_, lean_object* v_indName_4408_, lean_object* v_tail_4409_, lean_object* v_params_4410_, lean_object* v_head_4411_, lean_object* v_ctors_4412_, lean_object* v_numIndices_4413_, lean_object* v___x_4414_, lean_object* v___x_4415_, lean_object* v_val_4416_, lean_object* v_declName_4417_, lean_object* v_levelParams_4418_, lean_object* v_numParams_4419_, lean_object* v___x_4420_, lean_object* v_is_4421_, lean_object* v_t_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___f_4430_; uint8_t v___x_4431_; lean_object* v___x_4432_; 
v___x_4428_ = lean_unsigned_to_nat(1u);
v___x_4429_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4422_);
v___f_4430_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4430_, 0, v___x_4407_);
lean_closure_set(v___f_4430_, 1, v_indName_4408_);
lean_closure_set(v___f_4430_, 2, v_tail_4409_);
lean_closure_set(v___f_4430_, 3, v_params_4410_);
lean_closure_set(v___f_4430_, 4, v_is_4421_);
lean_closure_set(v___f_4430_, 5, v___x_4428_);
lean_closure_set(v___f_4430_, 6, v_head_4411_);
lean_closure_set(v___f_4430_, 7, v_ctors_4412_);
lean_closure_set(v___f_4430_, 8, v_numIndices_4413_);
lean_closure_set(v___f_4430_, 9, v___x_4414_);
lean_closure_set(v___f_4430_, 10, v___x_4415_);
lean_closure_set(v___f_4430_, 11, v_val_4416_);
lean_closure_set(v___f_4430_, 12, v_declName_4417_);
lean_closure_set(v___f_4430_, 13, v_levelParams_4418_);
lean_closure_set(v___f_4430_, 14, v_numParams_4419_);
lean_closure_set(v___f_4430_, 15, v___x_4420_);
lean_closure_set(v___f_4430_, 16, v_t_4422_);
lean_closure_set(v___f_4430_, 17, v___x_4429_);
v___x_4431_ = 0;
v___x_4432_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4422_, v___x_4429_, v___f_4430_, v___x_4431_, v___x_4431_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
return v___x_4432_;
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4407_ = stack[0].m_obj;
lean_object* v_indName_4408_ = stack[1].m_obj;
lean_object* v_tail_4409_ = stack[2].m_obj;
lean_object* v_params_4410_ = stack[3].m_obj;
lean_object* v_head_4411_ = stack[4].m_obj;
lean_object* v_ctors_4412_ = stack[5].m_obj;
lean_object* v_numIndices_4413_ = stack[6].m_obj;
lean_object* v___x_4414_ = stack[7].m_obj;
lean_object* v___x_4415_ = stack[8].m_obj;
lean_object* v_val_4416_ = stack[9].m_obj;
lean_object* v_declName_4417_ = stack[10].m_obj;
lean_object* v_levelParams_4418_ = stack[11].m_obj;
lean_object* v_numParams_4419_ = stack[12].m_obj;
lean_object* v___x_4420_ = stack[13].m_obj;
lean_object* v_is_4421_ = stack[14].m_obj;
lean_object* v_t_4422_ = stack[15].m_obj;
lean_object* v___y_4423_ = stack[16].m_obj;
lean_object* v___y_4424_ = stack[17].m_obj;
lean_object* v___y_4425_ = stack[18].m_obj;
lean_object* v___y_4426_ = stack[19].m_obj;
lean_object* v_res_4433_;
v_res_4433_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4407_, v_indName_4408_, v_tail_4409_, v_params_4410_, v_head_4411_, v_ctors_4412_, v_numIndices_4413_, v___x_4414_, v___x_4415_, v_val_4416_, v_declName_4417_, v_levelParams_4418_, v_numParams_4419_, v___x_4420_, v_is_4421_, v_t_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
stack->m_obj
 = v_res_4433_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4434_ = _args[0];
lean_object* v_indName_4435_ = _args[1];
lean_object* v_tail_4436_ = _args[2];
lean_object* v_params_4437_ = _args[3];
lean_object* v_head_4438_ = _args[4];
lean_object* v_ctors_4439_ = _args[5];
lean_object* v_numIndices_4440_ = _args[6];
lean_object* v___x_4441_ = _args[7];
lean_object* v___x_4442_ = _args[8];
lean_object* v_val_4443_ = _args[9];
lean_object* v_declName_4444_ = _args[10];
lean_object* v_levelParams_4445_ = _args[11];
lean_object* v_numParams_4446_ = _args[12];
lean_object* v___x_4447_ = _args[13];
lean_object* v_is_4448_ = _args[14];
lean_object* v_t_4449_ = _args[15];
lean_object* v___y_4450_ = _args[16];
lean_object* v___y_4451_ = _args[17];
lean_object* v___y_4452_ = _args[18];
lean_object* v___y_4453_ = _args[19];
lean_object* v___y_4454_ = _args[20];
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4434_, v_indName_4435_, v_tail_4436_, v_params_4437_, v_head_4438_, v_ctors_4439_, v_numIndices_4440_, v___x_4441_, v___x_4442_, v_val_4443_, v_declName_4444_, v_levelParams_4445_, v_numParams_4446_, v___x_4447_, v_is_4448_, v_t_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
return v_res_4455_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4456_, lean_object* v_indName_4457_, lean_object* v_tail_4458_, lean_object* v_head_4459_, lean_object* v_ctors_4460_, lean_object* v_numIndices_4461_, lean_object* v___x_4462_, lean_object* v___x_4463_, lean_object* v_val_4464_, lean_object* v_declName_4465_, lean_object* v_levelParams_4466_, lean_object* v_numParams_4467_, lean_object* v_params_4468_, lean_object* v_t_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v___x_4475_; lean_object* v___f_4476_; lean_object* v___x_4477_; uint8_t v___x_4478_; lean_object* v___x_4479_; 
v___x_4475_ = l_Lean_Expr_bindingBody_x21(v_t_4469_);
lean_inc_ref(v___x_4475_);
lean_inc(v_numIndices_4461_);
v___f_4476_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4476_, 0, v___x_4456_);
lean_closure_set(v___f_4476_, 1, v_indName_4457_);
lean_closure_set(v___f_4476_, 2, v_tail_4458_);
lean_closure_set(v___f_4476_, 3, v_params_4468_);
lean_closure_set(v___f_4476_, 4, v_head_4459_);
lean_closure_set(v___f_4476_, 5, v_ctors_4460_);
lean_closure_set(v___f_4476_, 6, v_numIndices_4461_);
lean_closure_set(v___f_4476_, 7, v___x_4462_);
lean_closure_set(v___f_4476_, 8, v___x_4463_);
lean_closure_set(v___f_4476_, 9, v_val_4464_);
lean_closure_set(v___f_4476_, 10, v_declName_4465_);
lean_closure_set(v___f_4476_, 11, v_levelParams_4466_);
lean_closure_set(v___f_4476_, 12, v_numParams_4467_);
lean_closure_set(v___f_4476_, 13, v___x_4475_);
v___x_4477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4477_, 0, v_numIndices_4461_);
v___x_4478_ = 0;
v___x_4479_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4475_, v___x_4477_, v___f_4476_, v___x_4478_, v___x_4478_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
return v___x_4479_;
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_4456_ = stack[0].m_obj;
lean_object* v_indName_4457_ = stack[1].m_obj;
lean_object* v_tail_4458_ = stack[2].m_obj;
lean_object* v_head_4459_ = stack[3].m_obj;
lean_object* v_ctors_4460_ = stack[4].m_obj;
lean_object* v_numIndices_4461_ = stack[5].m_obj;
lean_object* v___x_4462_ = stack[6].m_obj;
lean_object* v___x_4463_ = stack[7].m_obj;
lean_object* v_val_4464_ = stack[8].m_obj;
lean_object* v_declName_4465_ = stack[9].m_obj;
lean_object* v_levelParams_4466_ = stack[10].m_obj;
lean_object* v_numParams_4467_ = stack[11].m_obj;
lean_object* v_params_4468_ = stack[12].m_obj;
lean_object* v_t_4469_ = stack[13].m_obj;
lean_object* v___y_4470_ = stack[14].m_obj;
lean_object* v___y_4471_ = stack[15].m_obj;
lean_object* v___y_4472_ = stack[16].m_obj;
lean_object* v___y_4473_ = stack[17].m_obj;
lean_object* v_res_4480_;
v_res_4480_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4456_, v_indName_4457_, v_tail_4458_, v_head_4459_, v_ctors_4460_, v_numIndices_4461_, v___x_4462_, v___x_4463_, v_val_4464_, v_declName_4465_, v_levelParams_4466_, v_numParams_4467_, v_params_4468_, v_t_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
stack->m_obj
 = v_res_4480_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4481_ = _args[0];
lean_object* v_indName_4482_ = _args[1];
lean_object* v_tail_4483_ = _args[2];
lean_object* v_head_4484_ = _args[3];
lean_object* v_ctors_4485_ = _args[4];
lean_object* v_numIndices_4486_ = _args[5];
lean_object* v___x_4487_ = _args[6];
lean_object* v___x_4488_ = _args[7];
lean_object* v_val_4489_ = _args[8];
lean_object* v_declName_4490_ = _args[9];
lean_object* v_levelParams_4491_ = _args[10];
lean_object* v_numParams_4492_ = _args[11];
lean_object* v_params_4493_ = _args[12];
lean_object* v_t_4494_ = _args[13];
lean_object* v___y_4495_ = _args[14];
lean_object* v___y_4496_ = _args[15];
lean_object* v___y_4497_ = _args[16];
lean_object* v___y_4498_ = _args[17];
lean_object* v___y_4499_ = _args[18];
_start:
{
lean_object* v_res_4500_; 
v_res_4500_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4481_, v_indName_4482_, v_tail_4483_, v_head_4484_, v_ctors_4485_, v_numIndices_4486_, v___x_4487_, v___x_4488_, v_val_4489_, v_declName_4490_, v_levelParams_4491_, v_numParams_4492_, v_params_4493_, v_t_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
lean_dec(v___y_4498_);
lean_dec_ref(v___y_4497_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec_ref(v_t_4494_);
return v_res_4500_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v___x_4505_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4506_ = lean_unsigned_to_nat(58u);
v___x_4507_ = lean_unsigned_to_nat(142u);
v___x_4508_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4509_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4510_ = l_mkPanicMessageWithDecl(v___x_4509_, v___x_4508_, v___x_4507_, v___x_4506_, v___x_4505_);
return v___x_4510_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; 
v___x_4511_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4512_ = lean_unsigned_to_nat(60u);
v___x_4513_ = lean_unsigned_to_nat(136u);
v___x_4514_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4515_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4516_ = l_mkPanicMessageWithDecl(v___x_4515_, v___x_4514_, v___x_4513_, v___x_4512_, v___x_4511_);
return v___x_4516_;
}
}
lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4517_, lean_object* v_indName_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4524_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_4518_);
v___x_4525_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v_a_4526_; 
v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
lean_inc(v_a_4526_);
lean_dec_ref_known(v___x_4525_, 1);
if (lean_obj_tag(v_a_4526_) == 5)
{
lean_object* v_val_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; 
v_val_4527_ = lean_ctor_get(v_a_4526_, 0);
lean_inc_ref(v_val_4527_);
lean_dec_ref_known(v_a_4526_, 1);
v___x_4528_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4517_);
v___x_4529_ = l_Lean_Name_append(v_declName_4517_, v___x_4528_);
lean_inc(v_indName_4518_);
lean_inc(v___x_4529_);
v___x_4530_ = l_Lean_mkCasesOnSameCtorHet(v___x_4529_, v_indName_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4562_; 
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4562_ == 0)
{
lean_object* v_unused_4563_; 
v_unused_4563_ = lean_ctor_get(v___x_4530_, 0);
lean_dec(v_unused_4563_);
v___x_4532_ = v___x_4530_;
v_isShared_4533_ = v_isSharedCheck_4562_;
goto v_resetjp_4531_;
}
else
{
lean_dec(v___x_4530_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4562_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; 
lean_inc(v_indName_4518_);
v___x_4534_ = l_Lean_mkCasesOnName(v_indName_4518_);
v___x_4535_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4534_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_object* v_a_4536_; lean_object* v_levelParams_4537_; lean_object* v_type_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4535_, 1);
v_levelParams_4537_ = lean_ctor_get(v_a_4536_, 1);
lean_inc_n(v_levelParams_4537_, 2);
v_type_4538_ = lean_ctor_get(v_a_4536_, 2);
lean_inc_ref(v_type_4538_);
lean_dec(v_a_4536_);
v___x_4539_ = lean_box(0);
v___x_4540_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4537_, v___x_4539_);
if (lean_obj_tag(v___x_4540_) == 1)
{
lean_object* v_head_4541_; lean_object* v_tail_4542_; lean_object* v_numParams_4543_; lean_object* v_numIndices_4544_; lean_object* v_ctors_4545_; lean_object* v___f_4546_; lean_object* v___x_4548_; 
v_head_4541_ = lean_ctor_get(v___x_4540_, 0);
lean_inc(v_head_4541_);
v_tail_4542_ = lean_ctor_get(v___x_4540_, 1);
lean_inc(v_tail_4542_);
v_numParams_4543_ = lean_ctor_get(v_val_4527_, 1);
lean_inc_n(v_numParams_4543_, 2);
v_numIndices_4544_ = lean_ctor_get(v_val_4527_, 2);
lean_inc(v_numIndices_4544_);
v_ctors_4545_ = lean_ctor_get(v_val_4527_, 4);
lean_inc(v_ctors_4545_);
v___f_4546_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4546_, 0, v___x_4524_);
lean_closure_set(v___f_4546_, 1, v_indName_4518_);
lean_closure_set(v___f_4546_, 2, v_tail_4542_);
lean_closure_set(v___f_4546_, 3, v_head_4541_);
lean_closure_set(v___f_4546_, 4, v_ctors_4545_);
lean_closure_set(v___f_4546_, 5, v_numIndices_4544_);
lean_closure_set(v___f_4546_, 6, v___x_4529_);
lean_closure_set(v___f_4546_, 7, v___x_4540_);
lean_closure_set(v___f_4546_, 8, v_val_4527_);
lean_closure_set(v___f_4546_, 9, v_declName_4517_);
lean_closure_set(v___f_4546_, 10, v_levelParams_4537_);
lean_closure_set(v___f_4546_, 11, v_numParams_4543_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set_tag(v___x_4532_, 1);
lean_ctor_set(v___x_4532_, 0, v_numParams_4543_);
v___x_4548_ = v___x_4532_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_numParams_4543_);
v___x_4548_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
uint8_t v___x_4549_; lean_object* v___x_4550_; 
v___x_4549_ = 0;
v___x_4550_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4538_, v___x_4548_, v___f_4546_, v___x_4549_, v___x_4549_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
return v___x_4550_;
}
}
else
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
lean_dec(v___x_4540_);
lean_dec_ref(v_type_4538_);
lean_dec(v_levelParams_4537_);
lean_del_object(v___x_4532_);
lean_dec(v___x_4529_);
lean_dec_ref(v_val_4527_);
lean_dec(v_indName_4518_);
lean_dec(v_declName_4517_);
v___x_4552_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4553_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4552_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
return v___x_4553_;
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_del_object(v___x_4532_);
lean_dec(v___x_4529_);
lean_dec_ref(v_val_4527_);
lean_dec(v_indName_4518_);
lean_dec(v_declName_4517_);
v_a_4554_ = lean_ctor_get(v___x_4535_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4535_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4535_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4535_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
else
{
lean_dec(v___x_4529_);
lean_dec_ref(v_val_4527_);
lean_dec(v_indName_4518_);
lean_dec(v_declName_4517_);
return v___x_4530_;
}
}
else
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
lean_dec(v_a_4526_);
lean_dec(v_indName_4518_);
lean_dec(v_declName_4517_);
v___x_4564_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4565_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4564_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
return v___x_4565_;
}
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec(v_indName_4518_);
lean_dec(v_declName_4517_);
v_a_4566_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4525_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4525_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_mkCasesOnSameCtor_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_4517_ = stack[0].m_obj;
lean_object* v_indName_4518_ = stack[1].m_obj;
lean_object* v_a_4519_ = stack[2].m_obj;
lean_object* v_a_4520_ = stack[3].m_obj;
lean_object* v_a_4521_ = stack[4].m_obj;
lean_object* v_a_4522_ = stack[5].m_obj;
lean_object* v_res_4574_;
v_res_4574_ = l_Lean_mkCasesOnSameCtor(v_declName_4517_, v_indName_4518_, v_a_4519_, v_a_4520_, v_a_4521_, v_a_4522_);
stack->m_obj
 = v_res_4574_;
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4575_, lean_object* v_indName_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_Lean_mkCasesOnSameCtor(v_declName_4575_, v_indName_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_);
lean_dec(v_a_4580_);
lean_dec_ref(v_a_4579_);
lean_dec(v_a_4578_);
lean_dec_ref(v_a_4577_);
return v_res_4582_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4583_, lean_object* v_params_4584_, lean_object* v_motive_4585_, lean_object* v_as_4586_, size_t v_sz_4587_, size_t v_i_4588_, lean_object* v_bs_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
lean_object* v___x_4595_; 
v___x_4595_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4583_, v_params_4584_, v_motive_4585_, v_sz_4587_, v_i_4588_, v_bs_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
return v___x_4595_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_4583_ = stack[0].m_obj;
lean_object* v_params_4584_ = stack[1].m_obj;
lean_object* v_motive_4585_ = stack[2].m_obj;
lean_object* v_as_4586_ = stack[3].m_obj;
size_t v_sz_4587_ = stack[4].m_num;
size_t v_i_4588_ = stack[5].m_num;
lean_object* v_bs_4589_ = stack[6].m_obj;
lean_object* v___y_4590_ = stack[7].m_obj;
lean_object* v___y_4591_ = stack[8].m_obj;
lean_object* v___y_4592_ = stack[9].m_obj;
lean_object* v___y_4593_ = stack[10].m_obj;
lean_object* v_res_4596_;
v_res_4596_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4583_, v_params_4584_, v_motive_4585_, v_as_4586_, v_sz_4587_, v_i_4588_, v_bs_4589_, v___y_4590_, v___y_4591_, v___y_4592_, v___y_4593_);
stack->m_obj
 = v_res_4596_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4597_, lean_object* v_params_4598_, lean_object* v_motive_4599_, lean_object* v_as_4600_, lean_object* v_sz_4601_, lean_object* v_i_4602_, lean_object* v_bs_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
size_t v_sz_boxed_4609_; size_t v_i_boxed_4610_; lean_object* v_res_4611_; 
v_sz_boxed_4609_ = lean_unbox_usize(v_sz_4601_);
lean_dec(v_sz_4601_);
v_i_boxed_4610_ = lean_unbox_usize(v_i_4602_);
lean_dec(v_i_4602_);
v_res_4611_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4597_, v_params_4598_, v_motive_4599_, v_as_4600_, v_sz_boxed_4609_, v_i_boxed_4610_, v_bs_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_);
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec_ref(v_as_4600_);
lean_dec_ref(v_params_4598_);
return v_res_4611_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4612_, lean_object* v_params_4613_, lean_object* v_a_4614_, lean_object* v_snd_4615_, lean_object* v_alts_4616_, lean_object* v_as_4617_, size_t v_sz_4618_, size_t v_i_4619_, lean_object* v_bs_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v___x_4626_; 
v___x_4626_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4612_, v_params_4613_, v_a_4614_, v_snd_4615_, v_alts_4616_, v_sz_4618_, v_i_4619_, v_bs_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
return v___x_4626_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_tail_4612_ = stack[0].m_obj;
lean_object* v_params_4613_ = stack[1].m_obj;
lean_object* v_a_4614_ = stack[2].m_obj;
lean_object* v_snd_4615_ = stack[3].m_obj;
lean_object* v_alts_4616_ = stack[4].m_obj;
lean_object* v_as_4617_ = stack[5].m_obj;
size_t v_sz_4618_ = stack[6].m_num;
size_t v_i_4619_ = stack[7].m_num;
lean_object* v_bs_4620_ = stack[8].m_obj;
lean_object* v___y_4621_ = stack[9].m_obj;
lean_object* v___y_4622_ = stack[10].m_obj;
lean_object* v___y_4623_ = stack[11].m_obj;
lean_object* v___y_4624_ = stack[12].m_obj;
lean_object* v_res_4627_;
v_res_4627_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4612_, v_params_4613_, v_a_4614_, v_snd_4615_, v_alts_4616_, v_as_4617_, v_sz_4618_, v_i_4619_, v_bs_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
stack->m_obj
 = v_res_4627_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4628_, lean_object* v_params_4629_, lean_object* v_a_4630_, lean_object* v_snd_4631_, lean_object* v_alts_4632_, lean_object* v_as_4633_, lean_object* v_sz_4634_, lean_object* v_i_4635_, lean_object* v_bs_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
size_t v_sz_boxed_4642_; size_t v_i_boxed_4643_; lean_object* v_res_4644_; 
v_sz_boxed_4642_ = lean_unbox_usize(v_sz_4634_);
lean_dec(v_sz_4634_);
v_i_boxed_4643_ = lean_unbox_usize(v_i_4635_);
lean_dec(v_i_4635_);
v_res_4644_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4628_, v_params_4629_, v_a_4630_, v_snd_4631_, v_alts_4632_, v_as_4633_, v_sz_boxed_4642_, v_i_boxed_4643_, v_bs_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec_ref(v_as_4633_);
lean_dec_ref(v_params_4629_);
return v_res_4644_;
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
