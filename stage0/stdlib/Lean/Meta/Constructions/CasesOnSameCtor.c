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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
lean_object* lean_array_get_size(lean_object*);
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18;
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
v_isModule_349_ = lean_ctor_get_uint8(v___x_348_, sizeof(void*)*7 + 4);
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
uint8_t v___x_20811__boxed_561_; uint8_t v___x_20812__boxed_562_; uint8_t v___x_20813__boxed_563_; lean_object* v_res_564_; 
v___x_20811__boxed_561_ = lean_unbox(v___x_542_);
v___x_20812__boxed_562_ = lean_unbox(v___x_543_);
v___x_20813__boxed_563_ = lean_unbox(v___x_544_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_539_, v_ism2_540_, v_motive_541_, v___x_20811__boxed_561_, v___x_20812__boxed_562_, v___x_20813__boxed_563_, v_a_545_, v___f_546_, v_zs1_547_, v_val_548_, v___x_549_, v_indName_550_, v_v_551_, v___x_552_, v_params_553_, v___x_554_, v_h_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
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
uint8_t v___x_20923__boxed_597_; uint8_t v___x_20924__boxed_598_; uint8_t v___x_20925__boxed_599_; lean_object* v_res_600_; 
v___x_20923__boxed_597_ = lean_unbox(v___x_587_);
v___x_20924__boxed_598_ = lean_unbox(v___x_588_);
v___x_20925__boxed_599_ = lean_unbox(v___x_589_);
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_583_, v_alts_584_, v___x_585_, v_zs1_586_, v___x_20923__boxed_597_, v___x_20924__boxed_598_, v___x_20925__boxed_599_, v_zs2_590_, v_x_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
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
uint8_t v___x_20984__boxed_695_; uint8_t v___x_20985__boxed_696_; uint8_t v___x_20986__boxed_697_; lean_object* v_res_698_; 
v___x_20984__boxed_695_ = lean_unbox(v___x_671_);
v___x_20985__boxed_696_ = lean_unbox(v___x_672_);
v___x_20986__boxed_697_ = lean_unbox(v___x_673_);
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_668_, v_alts_669_, v___x_670_, v___x_20984__boxed_695_, v___x_20985__boxed_696_, v___x_20986__boxed_697_, v___x_674_, v___x_675_, v___x_676_, v_ism2_677_, v_motive_678_, v_a_679_, v_val_680_, v_indName_681_, v_v_682_, v___x_683_, v_params_684_, v___x_685_, v___x_686_, v___x_687_, v_zs1_688_, v_ctorRet1_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
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
uint8_t v___x_21215__boxed_864_; uint8_t v___x_21216__boxed_865_; uint8_t v___x_21217__boxed_866_; lean_object* v_res_867_; 
v___x_21215__boxed_864_ = lean_unbox(v___x_842_);
v___x_21216__boxed_865_ = lean_unbox(v___x_843_);
v___x_21217__boxed_866_ = lean_unbox(v___x_844_);
v_res_867_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_838_, v___x_839_, v_a_840_, v_ism1_841_, v___x_21215__boxed_864_, v___x_21216__boxed_865_, v___x_21217__boxed_866_, v_name_845_, v___x_846_, v_params_847_, v___x_848_, v_tail_849_, v_alts_850_, v_numParams_851_, v_ism2_852_, v_val_853_, v_indName_854_, v___x_855_, v___x_856_, v___x_857_, v_heq_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
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
uint8_t v___x_21338__boxed_930_; uint8_t v___x_21339__boxed_931_; uint8_t v___x_21340__boxed_932_; lean_object* v_res_933_; 
v___x_21338__boxed_930_ = lean_unbox(v___x_914_);
v___x_21339__boxed_931_ = lean_unbox(v___x_915_);
v___x_21340__boxed_932_ = lean_unbox(v___x_916_);
v_res_933_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_907_, v_tail_908_, v_params_909_, v_ism1_910_, v_ism2_911_, v_motive_912_, v___x_913_, v___x_21338__boxed_930_, v___x_21339__boxed_931_, v___x_21340__boxed_932_, v_name_917_, v___x_918_, v___x_919_, v_numParams_920_, v_val_921_, v___x_922_, v___x_923_, v_alts_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
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
lean_object* v___x_20222__overap_985_; lean_object* v___x_986_; 
v___x_20222__overap_985_ = l_instInhabitedOfMonad___redArg(v___x_977_, v___x_978_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
v___x_986_ = lean_apply_5(v___x_20222__overap_985_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, lean_box(0));
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
uint8_t v___x_21777__boxed_1301_; uint8_t v___x_21778__boxed_1302_; uint8_t v___x_21779__boxed_1303_; lean_object* v_res_1304_; 
v___x_21777__boxed_1301_ = lean_unbox(v___x_1289_);
v___x_21778__boxed_1302_ = lean_unbox(v___x_1290_);
v___x_21779__boxed_1303_ = lean_unbox(v___x_1291_);
v_res_1304_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1282_, v_dummy_1283_, v___x_1284_, v___x_1285_, v___x_1286_, v_motive_1287_, v_zs1_1288_, v___x_21777__boxed_1301_, v___x_21778__boxed_1302_, v___x_21779__boxed_1303_, v_v_1292_, v___x_1293_, v_zs2_1294_, v_ctorRet2_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
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
uint8_t v___x_21918__boxed_1364_; uint8_t v___x_21919__boxed_1365_; uint8_t v___x_21920__boxed_1366_; lean_object* v_res_1367_; 
v___x_21918__boxed_1364_ = lean_unbox(v___x_1351_);
v___x_21919__boxed_1365_ = lean_unbox(v___x_1352_);
v___x_21920__boxed_1366_ = lean_unbox(v___x_1353_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1347_, v___x_1348_, v___x_1349_, v_motive_1350_, v___x_21918__boxed_1364_, v___x_21919__boxed_1365_, v___x_21920__boxed_1366_, v_v_1354_, v___x_1355_, v_a_1356_, v_zs1_1357_, v_ctorRet1_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
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
uint8_t v___x_22098__boxed_1497_; uint8_t v___x_22099__boxed_1498_; uint8_t v___x_22100__boxed_1499_; lean_object* v_res_1500_; 
v___x_22098__boxed_1497_ = lean_unbox(v___x_1482_);
v___x_22099__boxed_1498_ = lean_unbox(v___x_1483_);
v___x_22100__boxed_1499_ = lean_unbox(v___x_1484_);
v_res_1500_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1475_, v_indName_1476_, v_tail_1477_, v_params_1478_, v_ism1_1479_, v_ism2_1480_, v___x_1481_, v___x_22098__boxed_1497_, v___x_22099__boxed_1498_, v___x_22100__boxed_1499_, v_name_1485_, v___x_1486_, v_numParams_1487_, v_val_1488_, v___x_1489_, v___x_1490_, v_motive_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
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
uint8_t v___x_22386__boxed_1726_; lean_object* v_res_1727_; 
v___x_22386__boxed_1726_ = lean_unbox(v___x_1720_);
v_res_1727_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1717_, v_declName_1718_, v_levelParams_1719_, v___x_22386__boxed_1726_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
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
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1819_, 0, v___x_1818_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
lean_ctor_set(v___x_1819_, 2, v___x_1818_);
lean_ctor_set(v___x_1819_, 3, v___x_1818_);
lean_ctor_set(v___x_1819_, 4, v___x_1817_);
lean_ctor_set(v___x_1819_, 5, v___x_1817_);
lean_ctor_set(v___x_1819_, 6, v___x_1817_);
lean_ctor_set(v___x_1819_, 7, v___x_1817_);
lean_ctor_set(v___x_1819_, 8, v___x_1817_);
lean_ctor_set(v___x_1819_, 9, v___x_1817_);
lean_ctor_set(v___x_1819_, 10, v___x_1817_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = lean_unsigned_to_nat(32u);
v___x_1821_ = lean_mk_empty_array_with_capacity(v___x_1820_);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
size_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1823_ = ((size_t)5ULL);
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = lean_unsigned_to_nat(32u);
v___x_1826_ = lean_mk_empty_array_with_capacity(v___x_1825_);
v___x_1827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1828_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1826_);
lean_ctor_set(v___x_1828_, 2, v___x_1824_);
lean_ctor_set(v___x_1828_, 3, v___x_1824_);
lean_ctor_set_usize(v___x_1828_, 4, v___x_1823_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1829_ = lean_box(1);
v___x_1830_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1832_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v___x_1830_);
lean_ctor_set(v___x_1832_, 2, v___x_1829_);
return v___x_1832_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1834_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5));
v___x_1835_ = l_Lean_stringToMessageData(v___x_1834_);
return v___x_1835_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7));
v___x_1838_ = l_Lean_stringToMessageData(v___x_1837_);
return v___x_1838_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9));
v___x_1841_ = l_Lean_stringToMessageData(v___x_1840_);
return v___x_1841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13));
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15));
v___x_1850_ = l_Lean_stringToMessageData(v___x_1849_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17));
v___x_1853_ = l_Lean_stringToMessageData(v___x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1854_, lean_object* v_declHint_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v_env_1860_; uint8_t v___x_1861_; 
v___x_1858_ = lean_box(0);
v___x_1859_ = lean_st_ref_get(v___y_1856_);
v_env_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc_ref(v_env_1860_);
lean_dec(v___x_1859_);
v___x_1861_ = l_Lean_Name_isAnonymous(v_declHint_1855_);
if (v___x_1861_ == 0)
{
uint8_t v_isExporting_1862_; 
v_isExporting_1862_ = lean_ctor_get_uint8(v_env_1860_, sizeof(void*)*13);
if (v_isExporting_1862_ == 0)
{
lean_object* v___x_1863_; 
lean_dec_ref(v_env_1860_);
lean_dec(v_declHint_1855_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_msg_1854_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
lean_inc_ref(v_env_1860_);
v___x_1864_ = l_Lean_Environment_setExporting(v_env_1860_, v___x_1861_);
lean_inc(v_declHint_1855_);
lean_inc_ref(v___x_1864_);
v___x_1865_ = l_Lean_Environment_contains(v___x_1864_, v_declHint_1855_, v_isExporting_1862_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
lean_dec_ref(v___x_1864_);
lean_dec_ref(v_env_1860_);
lean_dec(v_declHint_1855_);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_msg_1854_);
return v___x_1866_;
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v_c_1872_; lean_object* v___x_1873_; 
v___x_1867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1869_ = l_Lean_Options_empty;
v___x_1870_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1864_);
lean_ctor_set(v___x_1870_, 1, v___x_1867_);
lean_ctor_set(v___x_1870_, 2, v___x_1868_);
lean_ctor_set(v___x_1870_, 3, v___x_1869_);
lean_inc(v_declHint_1855_);
v___x_1871_ = l_Lean_MessageData_ofConstName(v_declHint_1855_, v___x_1861_);
v_c_1872_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1872_, 0, v___x_1870_);
lean_ctor_set(v_c_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1860_, v_declHint_1855_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_dec_ref(v_env_1860_);
lean_dec(v_declHint_1855_);
v___x_1874_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v_c_1872_);
v___x_1876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = l_Lean_MessageData_note(v___x_1877_);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v_msg_1854_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
return v___x_1880_;
}
else
{
lean_object* v_val_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1915_; 
v_val_1881_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1883_ = v___x_1873_;
v_isShared_1884_ = v_isSharedCheck_1915_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_val_1881_);
lean_dec(v___x_1873_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1915_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v_mod_1887_; uint8_t v___x_1888_; 
v___x_1885_ = l_Lean_Environment_header(v_env_1860_);
lean_dec_ref(v_env_1860_);
v___x_1886_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1885_);
v_mod_1887_ = lean_array_get(v___x_1858_, v___x_1886_, v_val_1881_);
lean_dec(v_val_1881_);
lean_dec_ref(v___x_1886_);
v___x_1888_ = l_Lean_isPrivateName(v_declHint_1855_);
lean_dec(v_declHint_1855_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
lean_ctor_set(v___x_1890_, 1, v_c_1872_);
v___x_1891_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = l_Lean_MessageData_ofName(v_mod_1887_);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = l_Lean_MessageData_note(v___x_1896_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v_msg_1854_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1898_);
v___x_1900_ = v___x_1883_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
else
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
lean_ctor_set(v___x_1903_, 1, v_c_1872_);
v___x_1904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = l_Lean_MessageData_ofName(v_mod_1887_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = l_Lean_MessageData_note(v___x_1909_);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_msg_1854_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set_tag(v___x_1883_, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1911_);
v___x_1913_ = v___x_1883_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1916_; 
lean_dec_ref(v_env_1860_);
lean_dec(v_declHint_1855_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v_msg_1854_);
return v___x_1916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1917_, lean_object* v_declHint_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1917_, v_declHint_1918_, v___y_1919_);
lean_dec(v___y_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1922_, lean_object* v_declHint_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v___x_1929_; lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1939_; 
v___x_1929_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1922_, v_declHint_1923_, v___y_1927_);
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1929_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1932_ = v___x_1929_;
v_isShared_1933_ = v_isSharedCheck_1939_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1929_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1939_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1934_ = l_Lean_unknownIdentifierMessageTag;
v___x_1935_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
lean_ctor_set(v___x_1935_, 1, v_a_1930_);
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 0, v___x_1935_);
v___x_1937_ = v___x_1932_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1940_, lean_object* v_declHint_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1940_, v_declHint_1941_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1948_, lean_object* v_msg_1949_, lean_object* v_declHint_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; lean_object* v_a_1957_; lean_object* v___x_1958_; 
v___x_1956_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1949_, v_declHint_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref(v___x_1956_);
v___x_1958_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1948_, v_a_1957_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1959_, lean_object* v_msg_1960_, lean_object* v_declHint_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1959_, v_msg_1960_, v_declHint_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v_ref_1959_);
return v_res_1967_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1969_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_1970_ = l_Lean_stringToMessageData(v___x_1969_);
return v___x_1970_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_1973_ = l_Lean_stringToMessageData(v___x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_1974_, lean_object* v_constName_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v___x_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1981_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_1982_ = 0;
lean_inc(v_constName_1975_);
v___x_1983_ = l_Lean_MessageData_ofConstName(v_constName_1975_, v___x_1982_);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1981_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1974_, v___x_1986_, v_constName_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_1988_, lean_object* v_constName_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1988_, v_constName_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
lean_dec(v___y_1993_);
lean_dec_ref(v___y_1992_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v_ref_1988_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_ref_2002_; lean_object* v___x_2003_; 
v_ref_2002_ = lean_ctor_get(v___y_1999_, 2);
v___x_2003_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2002_, v_constName_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
lean_dec(v___y_2008_);
lean_dec_ref(v___y_2007_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; lean_object* v_env_2018_; uint8_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2017_ = lean_st_ref_get(v___y_2015_);
v_env_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc_ref(v_env_2018_);
lean_dec(v___x_2017_);
v___x_2019_ = 0;
lean_inc(v_constName_2011_);
v___x_2020_ = l_Lean_Environment_findConstVal_x3f(v_env_2018_, v_constName_2011_, v___x_2019_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
return v___x_2021_;
}
else
{
lean_object* v_val_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
lean_dec(v_constName_2011_);
v_val_2022_ = lean_ctor_get(v___x_2020_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2020_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2024_ = v___x_2020_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_val_2022_);
lean_dec(v___x_2020_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set_tag(v___x_2024_, 0);
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_val_2022_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2037_, uint8_t v_s_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v_env_2043_; lean_object* v_nextMacroScope_2044_; lean_object* v_ngen_2045_; lean_object* v_auxDeclNGen_2046_; lean_object* v_traceState_2047_; lean_object* v_recordedDeps_2048_; lean_object* v_messages_2049_; lean_object* v_infoState_2050_; lean_object* v_snapshotTasks_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2080_; 
v___x_2042_ = lean_st_ref_take(v___y_2040_);
v_env_2043_ = lean_ctor_get(v___x_2042_, 0);
v_nextMacroScope_2044_ = lean_ctor_get(v___x_2042_, 1);
v_ngen_2045_ = lean_ctor_get(v___x_2042_, 2);
v_auxDeclNGen_2046_ = lean_ctor_get(v___x_2042_, 3);
v_traceState_2047_ = lean_ctor_get(v___x_2042_, 4);
v_recordedDeps_2048_ = lean_ctor_get(v___x_2042_, 6);
v_messages_2049_ = lean_ctor_get(v___x_2042_, 7);
v_infoState_2050_ = lean_ctor_get(v___x_2042_, 8);
v_snapshotTasks_2051_ = lean_ctor_get(v___x_2042_, 9);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v___x_2042_, 5);
lean_dec(v_unused_2081_);
v___x_2053_ = v___x_2042_;
v_isShared_2054_ = v_isSharedCheck_2080_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_snapshotTasks_2051_);
lean_inc(v_infoState_2050_);
lean_inc(v_messages_2049_);
lean_inc(v_recordedDeps_2048_);
lean_inc(v_traceState_2047_);
lean_inc(v_auxDeclNGen_2046_);
lean_inc(v_ngen_2045_);
lean_inc(v_nextMacroScope_2044_);
lean_inc(v_env_2043_);
lean_dec(v___x_2042_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2080_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
uint8_t v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2055_ = 0;
v___x_2056_ = lean_box(0);
v___x_2057_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2043_, v_declName_2037_, v_s_2038_, v___x_2055_, v___x_2056_);
v___x_2058_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 5, v___x_2058_);
lean_ctor_set(v___x_2053_, 0, v___x_2057_);
v___x_2060_ = v___x_2053_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2057_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_nextMacroScope_2044_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_ngen_2045_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_auxDeclNGen_2046_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_traceState_2047_);
lean_ctor_set(v_reuseFailAlloc_2079_, 5, v___x_2058_);
lean_ctor_set(v_reuseFailAlloc_2079_, 6, v_recordedDeps_2048_);
lean_ctor_set(v_reuseFailAlloc_2079_, 7, v_messages_2049_);
lean_ctor_set(v_reuseFailAlloc_2079_, 8, v_infoState_2050_);
lean_ctor_set(v_reuseFailAlloc_2079_, 9, v_snapshotTasks_2051_);
v___x_2060_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v_mctx_2063_; lean_object* v_zetaDeltaFVarIds_2064_; lean_object* v_postponed_2065_; lean_object* v_diag_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2077_; 
v___x_2061_ = lean_st_ref_put(v___y_2040_, v___x_2060_);
v___x_2062_ = lean_st_ref_take(v___y_2039_);
v_mctx_2063_ = lean_ctor_get(v___x_2062_, 0);
v_zetaDeltaFVarIds_2064_ = lean_ctor_get(v___x_2062_, 2);
v_postponed_2065_ = lean_ctor_get(v___x_2062_, 3);
v_diag_2066_ = lean_ctor_get(v___x_2062_, 4);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; 
v_unused_2078_ = lean_ctor_get(v___x_2062_, 1);
lean_dec(v_unused_2078_);
v___x_2068_ = v___x_2062_;
v_isShared_2069_ = v_isSharedCheck_2077_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_diag_2066_);
lean_inc(v_postponed_2065_);
lean_inc(v_zetaDeltaFVarIds_2064_);
lean_inc(v_mctx_2063_);
lean_dec(v___x_2062_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2077_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2070_ = lean_box(0);
v___x_2071_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 1, v___x_2071_);
v___x_2073_ = v___x_2068_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_mctx_2063_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_zetaDeltaFVarIds_2064_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_postponed_2065_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_diag_2066_);
v___x_2073_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2074_ = lean_st_ref_put(v___y_2039_, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2070_);
return v___x_2075_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2082_, lean_object* v_s_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
uint8_t v_s_boxed_2087_; lean_object* v_res_2088_; 
v_s_boxed_2087_ = lean_unbox(v_s_2083_);
v_res_2088_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2082_, v_s_boxed_2087_, v___y_2084_, v___y_2085_);
lean_dec(v___y_2085_);
lean_dec(v___y_2084_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = 0;
v___x_2096_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2089_, v___x_2095_, v___y_2091_, v___y_2093_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
return v_res_2103_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2106_ = l_Lean_stringToMessageData(v___x_2105_);
return v___x_2106_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2109_ = l_Lean_stringToMessageData(v___x_2108_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2112_ = l_Lean_stringToMessageData(v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2113_, lean_object* v_declName_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2120_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2121_ = l_Lean_MessageData_ofName(v_attrName_2113_);
v___x_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = 0;
v___x_2126_ = l_Lean_MessageData_ofConstName(v_declName_2114_, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2124_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2129_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2131_, lean_object* v_declName_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2131_, v_declName_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0(lean_object* v_addEntryFn_2139_, lean_object* v_decl_2140_, lean_object* v_s_2141_){
_start:
{
lean_object* v_importedEntries_2142_; lean_object* v_state_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2151_; 
v_importedEntries_2142_ = lean_ctor_get(v_s_2141_, 0);
v_state_2143_ = lean_ctor_get(v_s_2141_, 1);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_s_2141_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2145_ = v_s_2141_;
v_isShared_2146_ = v_isSharedCheck_2151_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_state_2143_);
lean_inc(v_importedEntries_2142_);
lean_dec(v_s_2141_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2151_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v_state_2147_; lean_object* v___x_2149_; 
v_state_2147_ = lean_apply_2(v_addEntryFn_2139_, v_state_2143_, v_decl_2140_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 1, v_state_2147_);
v___x_2149_ = v___x_2145_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_importedEntries_2142_);
lean_ctor_set(v_reuseFailAlloc_2150_, 1, v_state_2147_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2154_ = l_Lean_stringToMessageData(v___x_2153_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2157_ = l_Lean_stringToMessageData(v___x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2158_, lean_object* v_declName_2159_, lean_object* v_asyncPrefix_x3f_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___y_2167_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2160_) == 0)
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_MessageData_nil;
v___y_2167_ = v___x_2180_;
goto v___jp_2166_;
}
else
{
lean_object* v_val_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_val_2181_ = lean_ctor_get(v_asyncPrefix_x3f_2160_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v_asyncPrefix_x3f_2160_, 1);
v___x_2182_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2183_ = l_Lean_MessageData_ofName(v_val_2181_);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2184_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___y_2167_ = v___x_2186_;
goto v___jp_2166_;
}
v___jp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2168_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2169_ = l_Lean_MessageData_ofName(v_attrName_2158_);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = 0;
v___x_2174_ = l_Lean_MessageData_ofConstName(v_declName_2159_, v___x_2173_);
v___x_2175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2172_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
v___x_2176_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
lean_ctor_set(v___x_2178_, 1, v___y_2167_);
v___x_2179_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2178_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v___x_2179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2187_, lean_object* v_declName_2188_, lean_object* v_asyncPrefix_x3f_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2187_, v_declName_2188_, v_asyncPrefix_x3f_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2196_, lean_object* v_decl_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___x_2258_; lean_object* v_env_2259_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___x_2274_; 
v___x_2258_ = lean_st_ref_get(v___y_2201_);
v_env_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc_ref(v_env_2259_);
lean_dec(v___x_2258_);
v___x_2274_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2259_, v_decl_2197_);
if (lean_obj_tag(v___x_2274_) == 0)
{
v___y_2261_ = v___y_2198_;
v___y_2262_ = v___y_2199_;
v___y_2263_ = v___y_2200_;
v___y_2264_ = v___y_2201_;
goto v___jp_2260_;
}
else
{
lean_object* v_attr_2275_; lean_object* v_toAttributeImplCore_2276_; lean_object* v_name_2277_; lean_object* v___x_2278_; 
lean_dec_ref_known(v___x_2274_, 1);
lean_dec_ref(v_env_2259_);
v_attr_2275_ = lean_ctor_get(v_attr_2196_, 0);
lean_inc_ref(v_attr_2275_);
lean_dec_ref(v_attr_2196_);
v_toAttributeImplCore_2276_ = lean_ctor_get(v_attr_2275_, 0);
lean_inc_ref(v_toAttributeImplCore_2276_);
lean_dec_ref(v_attr_2275_);
v_name_2277_ = lean_ctor_get(v_toAttributeImplCore_2276_, 1);
lean_inc(v_name_2277_);
lean_dec_ref(v_toAttributeImplCore_2276_);
v___x_2278_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2277_, v_decl_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
return v___x_2278_;
}
v___jp_2203_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_mctx_2219_; lean_object* v_zetaDeltaFVarIds_2220_; lean_object* v_postponed_2221_; lean_object* v_diag_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2233_; 
v___x_2215_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
v___x_2216_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2216_, 0, v___y_2214_);
lean_ctor_set(v___x_2216_, 1, v___y_2207_);
lean_ctor_set(v___x_2216_, 2, v___y_2204_);
lean_ctor_set(v___x_2216_, 3, v___y_2210_);
lean_ctor_set(v___x_2216_, 4, v___y_2208_);
lean_ctor_set(v___x_2216_, 5, v___x_2215_);
lean_ctor_set(v___x_2216_, 6, v___y_2205_);
lean_ctor_set(v___x_2216_, 7, v___y_2213_);
lean_ctor_set(v___x_2216_, 8, v___y_2209_);
lean_ctor_set(v___x_2216_, 9, v___y_2212_);
v___x_2217_ = lean_st_ref_put(v___y_2206_, v___x_2216_);
v___x_2218_ = lean_st_ref_take(v___y_2211_);
v_mctx_2219_ = lean_ctor_get(v___x_2218_, 0);
v_zetaDeltaFVarIds_2220_ = lean_ctor_get(v___x_2218_, 2);
v_postponed_2221_ = lean_ctor_get(v___x_2218_, 3);
v_diag_2222_ = lean_ctor_get(v___x_2218_, 4);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2233_ == 0)
{
lean_object* v_unused_2234_; 
v_unused_2234_ = lean_ctor_get(v___x_2218_, 1);
lean_dec(v_unused_2234_);
v___x_2224_ = v___x_2218_;
v_isShared_2225_ = v_isSharedCheck_2233_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_diag_2222_);
lean_inc(v_postponed_2221_);
lean_inc(v_zetaDeltaFVarIds_2220_);
lean_inc(v_mctx_2219_);
lean_dec(v___x_2218_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2233_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2226_ = lean_box(0);
v___x_2227_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 1, v___x_2227_);
v___x_2229_ = v___x_2224_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_mctx_2219_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v___x_2227_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v_zetaDeltaFVarIds_2220_);
lean_ctor_set(v_reuseFailAlloc_2232_, 3, v_postponed_2221_);
lean_ctor_set(v_reuseFailAlloc_2232_, 4, v_diag_2222_);
v___x_2229_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = lean_st_ref_put(v___y_2211_, v___x_2229_);
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2226_);
return v___x_2231_;
}
}
}
v___jp_2235_:
{
lean_object* v___x_2238_; lean_object* v_ext_2239_; lean_object* v_toEnvExtension_2240_; lean_object* v_env_2241_; lean_object* v_nextMacroScope_2242_; lean_object* v_ngen_2243_; lean_object* v_auxDeclNGen_2244_; lean_object* v_traceState_2245_; lean_object* v_recordedDeps_2246_; lean_object* v_messages_2247_; lean_object* v_infoState_2248_; lean_object* v_snapshotTasks_2249_; lean_object* v_addEntryFn_2250_; lean_object* v_asyncMode_2251_; uint8_t v_logWrites_2252_; lean_object* v___f_2253_; uint8_t v___x_2254_; 
v___x_2238_ = lean_st_ref_take(v___y_2237_);
v_ext_2239_ = lean_ctor_get(v_attr_2196_, 1);
lean_inc_ref(v_ext_2239_);
lean_dec_ref(v_attr_2196_);
v_toEnvExtension_2240_ = lean_ctor_get(v_ext_2239_, 0);
lean_inc_ref(v_toEnvExtension_2240_);
v_env_2241_ = lean_ctor_get(v___x_2238_, 0);
lean_inc_ref(v_env_2241_);
v_nextMacroScope_2242_ = lean_ctor_get(v___x_2238_, 1);
lean_inc(v_nextMacroScope_2242_);
v_ngen_2243_ = lean_ctor_get(v___x_2238_, 2);
lean_inc_ref(v_ngen_2243_);
v_auxDeclNGen_2244_ = lean_ctor_get(v___x_2238_, 3);
lean_inc_ref(v_auxDeclNGen_2244_);
v_traceState_2245_ = lean_ctor_get(v___x_2238_, 4);
lean_inc_ref(v_traceState_2245_);
v_recordedDeps_2246_ = lean_ctor_get(v___x_2238_, 6);
lean_inc_ref(v_recordedDeps_2246_);
v_messages_2247_ = lean_ctor_get(v___x_2238_, 7);
lean_inc_ref(v_messages_2247_);
v_infoState_2248_ = lean_ctor_get(v___x_2238_, 8);
lean_inc_ref(v_infoState_2248_);
v_snapshotTasks_2249_ = lean_ctor_get(v___x_2238_, 9);
lean_inc_ref(v_snapshotTasks_2249_);
lean_dec(v___x_2238_);
v_addEntryFn_2250_ = lean_ctor_get(v_ext_2239_, 3);
lean_inc(v_addEntryFn_2250_);
lean_dec_ref(v_ext_2239_);
v_asyncMode_2251_ = lean_ctor_get(v_toEnvExtension_2240_, 2);
lean_inc(v_asyncMode_2251_);
v_logWrites_2252_ = lean_ctor_get_uint8(v_toEnvExtension_2240_, sizeof(void*)*6);
lean_inc(v_decl_2197_);
v___f_2253_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0), 3, 2);
lean_closure_set(v___f_2253_, 0, v_addEntryFn_2250_);
lean_closure_set(v___f_2253_, 1, v_decl_2197_);
v___x_2254_ = 1;
if (v_logWrites_2252_ == 0)
{
lean_object* v___x_2255_; 
v___x_2255_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2240_, v_env_2241_, v___f_2253_, v_asyncMode_2251_, v_decl_2197_, v___x_2254_);
lean_dec(v_asyncMode_2251_);
v___y_2204_ = v_ngen_2243_;
v___y_2205_ = v_recordedDeps_2246_;
v___y_2206_ = v___y_2237_;
v___y_2207_ = v_nextMacroScope_2242_;
v___y_2208_ = v_traceState_2245_;
v___y_2209_ = v_infoState_2248_;
v___y_2210_ = v_auxDeclNGen_2244_;
v___y_2211_ = v___y_2236_;
v___y_2212_ = v_snapshotTasks_2249_;
v___y_2213_ = v_messages_2247_;
v___y_2214_ = v___x_2255_;
goto v___jp_2203_;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
lean_inc_ref(v_toEnvExtension_2240_);
v___x_2256_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2240_, v_env_2241_);
lean_dec_ref(v_env_2241_);
v___x_2257_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2240_, v___x_2256_, v___f_2253_, v_asyncMode_2251_, v_decl_2197_, v___x_2254_);
lean_dec(v_asyncMode_2251_);
v___y_2204_ = v_ngen_2243_;
v___y_2205_ = v_recordedDeps_2246_;
v___y_2206_ = v___y_2237_;
v___y_2207_ = v_nextMacroScope_2242_;
v___y_2208_ = v_traceState_2245_;
v___y_2209_ = v_infoState_2248_;
v___y_2210_ = v_auxDeclNGen_2244_;
v___y_2211_ = v___y_2236_;
v___y_2212_ = v_snapshotTasks_2249_;
v___y_2213_ = v_messages_2247_;
v___y_2214_ = v___x_2257_;
goto v___jp_2203_;
}
}
v___jp_2260_:
{
lean_object* v_ext_2265_; lean_object* v_toEnvExtension_2266_; lean_object* v_attr_2267_; lean_object* v_asyncMode_2268_; uint8_t v___x_2269_; 
v_ext_2265_ = lean_ctor_get(v_attr_2196_, 1);
v_toEnvExtension_2266_ = lean_ctor_get(v_ext_2265_, 0);
v_attr_2267_ = lean_ctor_get(v_attr_2196_, 0);
v_asyncMode_2268_ = lean_ctor_get(v_toEnvExtension_2266_, 2);
lean_inc(v_decl_2197_);
lean_inc_ref(v_env_2259_);
v___x_2269_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2259_, v_decl_2197_, v_asyncMode_2268_);
if (v___x_2269_ == 0)
{
lean_object* v_toAttributeImplCore_2270_; lean_object* v_name_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_inc_ref(v_attr_2267_);
lean_dec_ref(v_attr_2196_);
v_toAttributeImplCore_2270_ = lean_ctor_get(v_attr_2267_, 0);
lean_inc_ref(v_toAttributeImplCore_2270_);
lean_dec_ref(v_attr_2267_);
v_name_2271_ = lean_ctor_get(v_toAttributeImplCore_2270_, 1);
lean_inc(v_name_2271_);
lean_dec_ref(v_toAttributeImplCore_2270_);
v___x_2272_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2259_);
v___x_2273_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2271_, v_decl_2197_, v___x_2272_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
return v___x_2273_;
}
else
{
lean_dec_ref(v_env_2259_);
v___y_2236_ = v___y_2262_;
v___y_2237_ = v___y_2264_;
goto v___jp_2235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2279_, lean_object* v_decl_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2279_, v_decl_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v_env_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; 
v___x_2293_ = lean_st_ref_get(v___y_2291_);
v_env_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc_ref(v_env_2294_);
lean_dec(v___x_2293_);
v___x_2295_ = 0;
lean_inc(v_constName_2287_);
v___x_2296_ = l_Lean_Environment_find_x3f(v_env_2294_, v_constName_2287_, v___x_2295_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
return v___x_2297_;
}
else
{
lean_object* v_val_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_dec(v_constName_2287_);
v_val_2298_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2296_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_val_2298_);
lean_dec(v___x_2296_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 0);
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_val_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
return v_res_2312_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2316_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2317_ = lean_unsigned_to_nat(58u);
v___x_2318_ = lean_unsigned_to_nat(33u);
v___x_2319_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2320_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2321_ = l_mkPanicMessageWithDecl(v___x_2320_, v___x_2319_, v___x_2318_, v___x_2317_, v___x_2316_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2323_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2324_ = lean_unsigned_to_nat(60u);
v___x_2325_ = lean_unsigned_to_nat(30u);
v___x_2326_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2327_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2328_ = l_mkPanicMessageWithDecl(v___x_2327_, v___x_2326_, v___x_2325_, v___x_2324_, v___x_2323_);
return v___x_2328_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2329_, lean_object* v_indName_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v___x_2336_; 
lean_inc(v_indName_2330_);
v___x_2336_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v_a_2337_; 
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc(v_a_2337_);
lean_dec_ref_known(v___x_2336_, 1);
if (lean_obj_tag(v_a_2337_) == 5)
{
lean_object* v_val_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2528_; 
v_val_2338_ = lean_ctor_get(v_a_2337_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_a_2337_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2340_ = v_a_2337_;
v_isShared_2341_ = v_isSharedCheck_2528_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_val_2338_);
lean_dec(v_a_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2528_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_inc(v_indName_2330_);
v___x_2342_ = l_Lean_mkCasesOnName(v_indName_2330_);
lean_inc(v___x_2342_);
v___x_2343_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2342_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v_name_2345_; lean_object* v_levelParams_2346_; lean_object* v_type_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v_name_2345_ = lean_ctor_get(v_a_2344_, 0);
lean_inc(v_name_2345_);
v_levelParams_2346_ = lean_ctor_get(v_a_2344_, 1);
lean_inc_n(v_levelParams_2346_, 2);
v_type_2347_ = lean_ctor_get(v_a_2344_, 2);
lean_inc_ref(v_type_2347_);
lean_dec(v_a_2344_);
v___x_2348_ = lean_box(0);
v___x_2349_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2346_, v___x_2348_);
if (lean_obj_tag(v___x_2349_) == 1)
{
lean_object* v_head_2350_; lean_object* v_tail_2351_; lean_object* v_numParams_2352_; lean_object* v_numIndices_2353_; lean_object* v_ctors_2354_; lean_object* v___f_2355_; lean_object* v___x_2357_; 
v_head_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_head_2350_);
v_tail_2351_ = lean_ctor_get(v___x_2349_, 1);
lean_inc(v_tail_2351_);
v_numParams_2352_ = lean_ctor_get(v_val_2338_, 1);
lean_inc_n(v_numParams_2352_, 2);
v_numIndices_2353_ = lean_ctor_get(v_val_2338_, 2);
lean_inc(v_numIndices_2353_);
v_ctors_2354_ = lean_ctor_get(v_val_2338_, 4);
lean_inc(v_ctors_2354_);
v___f_2355_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2355_, 0, v_numIndices_2353_);
lean_closure_set(v___f_2355_, 1, v_head_2350_);
lean_closure_set(v___f_2355_, 2, v_ctors_2354_);
lean_closure_set(v___f_2355_, 3, v_indName_2330_);
lean_closure_set(v___f_2355_, 4, v_tail_2351_);
lean_closure_set(v___f_2355_, 5, v_name_2345_);
lean_closure_set(v___f_2355_, 6, v___x_2349_);
lean_closure_set(v___f_2355_, 7, v_numParams_2352_);
lean_closure_set(v___f_2355_, 8, v_val_2338_);
lean_closure_set(v___f_2355_, 9, v___x_2342_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set_tag(v___x_2340_, 1);
lean_ctor_set(v___x_2340_, 0, v_numParams_2352_);
v___x_2357_ = v___x_2340_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_numParams_2352_);
v___x_2357_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
uint8_t v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = 0;
v___x_2359_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2347_, v___x_2357_, v___f_2355_, v___x_2358_, v___x_2358_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v___x_2361_; lean_object* v___f_2362_; uint8_t v___y_2364_; uint8_t v___x_2507_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v___x_2361_ = lean_box(v___x_2358_);
lean_inc(v_declName_2329_);
v___f_2362_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2362_, 0, v_a_2360_);
lean_closure_set(v___f_2362_, 1, v_declName_2329_);
lean_closure_set(v___f_2362_, 2, v_levelParams_2346_);
lean_closure_set(v___f_2362_, 3, v___x_2361_);
v___x_2507_ = l_Lean_isPrivateName(v_declName_2329_);
if (v___x_2507_ == 0)
{
uint8_t v___x_2508_; 
v___x_2508_ = 1;
v___y_2364_ = v___x_2508_;
goto v___jp_2363_;
}
else
{
v___y_2364_ = v___x_2358_;
goto v___jp_2363_;
}
v___jp_2363_:
{
lean_object* v___x_2365_; 
v___x_2365_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2362_, v___y_2364_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v___x_2366_; lean_object* v_env_2367_; lean_object* v_nextMacroScope_2368_; lean_object* v_ngen_2369_; lean_object* v_auxDeclNGen_2370_; lean_object* v_traceState_2371_; lean_object* v_recordedDeps_2372_; lean_object* v_messages_2373_; lean_object* v_infoState_2374_; lean_object* v_snapshotTasks_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2505_; 
lean_dec_ref_known(v___x_2365_, 1);
v___x_2366_ = lean_st_ref_take(v_a_2334_);
v_env_2367_ = lean_ctor_get(v___x_2366_, 0);
v_nextMacroScope_2368_ = lean_ctor_get(v___x_2366_, 1);
v_ngen_2369_ = lean_ctor_get(v___x_2366_, 2);
v_auxDeclNGen_2370_ = lean_ctor_get(v___x_2366_, 3);
v_traceState_2371_ = lean_ctor_get(v___x_2366_, 4);
v_recordedDeps_2372_ = lean_ctor_get(v___x_2366_, 6);
v_messages_2373_ = lean_ctor_get(v___x_2366_, 7);
v_infoState_2374_ = lean_ctor_get(v___x_2366_, 8);
v_snapshotTasks_2375_ = lean_ctor_get(v___x_2366_, 9);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v___x_2366_, 5);
lean_dec(v_unused_2506_);
v___x_2377_ = v___x_2366_;
v_isShared_2378_ = v_isSharedCheck_2505_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_snapshotTasks_2375_);
lean_inc(v_infoState_2374_);
lean_inc(v_messages_2373_);
lean_inc(v_recordedDeps_2372_);
lean_inc(v_traceState_2371_);
lean_inc(v_auxDeclNGen_2370_);
lean_inc(v_ngen_2369_);
lean_inc(v_nextMacroScope_2368_);
lean_inc(v_env_2367_);
lean_dec(v___x_2366_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2505_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
lean_inc(v_declName_2329_);
v___x_2379_ = l_Lean_Meta_markMatcherLike(v_env_2367_, v_declName_2329_);
v___x_2380_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 5, v___x_2380_);
lean_ctor_set(v___x_2377_, 0, v___x_2379_);
v___x_2382_ = v___x_2377_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2379_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_nextMacroScope_2368_);
lean_ctor_set(v_reuseFailAlloc_2504_, 2, v_ngen_2369_);
lean_ctor_set(v_reuseFailAlloc_2504_, 3, v_auxDeclNGen_2370_);
lean_ctor_set(v_reuseFailAlloc_2504_, 4, v_traceState_2371_);
lean_ctor_set(v_reuseFailAlloc_2504_, 5, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2504_, 6, v_recordedDeps_2372_);
lean_ctor_set(v_reuseFailAlloc_2504_, 7, v_messages_2373_);
lean_ctor_set(v_reuseFailAlloc_2504_, 8, v_infoState_2374_);
lean_ctor_set(v_reuseFailAlloc_2504_, 9, v_snapshotTasks_2375_);
v___x_2382_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v_mctx_2385_; lean_object* v_zetaDeltaFVarIds_2386_; lean_object* v_postponed_2387_; lean_object* v_diag_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2502_; 
v___x_2383_ = lean_st_ref_put(v_a_2334_, v___x_2382_);
v___x_2384_ = lean_st_ref_take(v_a_2332_);
v_mctx_2385_ = lean_ctor_get(v___x_2384_, 0);
v_zetaDeltaFVarIds_2386_ = lean_ctor_get(v___x_2384_, 2);
v_postponed_2387_ = lean_ctor_get(v___x_2384_, 3);
v_diag_2388_ = lean_ctor_get(v___x_2384_, 4);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; 
v_unused_2503_ = lean_ctor_get(v___x_2384_, 1);
lean_dec(v_unused_2503_);
v___x_2390_ = v___x_2384_;
v_isShared_2391_ = v_isSharedCheck_2502_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_diag_2388_);
lean_inc(v_postponed_2387_);
lean_inc(v_zetaDeltaFVarIds_2386_);
lean_inc(v_mctx_2385_);
lean_dec(v___x_2384_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2502_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v___x_2392_);
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_mctx_2385_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_zetaDeltaFVarIds_2386_);
lean_ctor_set(v_reuseFailAlloc_2501_, 3, v_postponed_2387_);
lean_ctor_set(v_reuseFailAlloc_2501_, 4, v_diag_2388_);
v___x_2394_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v_env_2397_; lean_object* v_nextMacroScope_2398_; lean_object* v_ngen_2399_; lean_object* v_auxDeclNGen_2400_; lean_object* v_traceState_2401_; lean_object* v_recordedDeps_2402_; lean_object* v_messages_2403_; lean_object* v_infoState_2404_; lean_object* v_snapshotTasks_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2499_; 
v___x_2395_ = lean_st_ref_put(v_a_2332_, v___x_2394_);
v___x_2396_ = lean_st_ref_take(v_a_2334_);
v_env_2397_ = lean_ctor_get(v___x_2396_, 0);
v_nextMacroScope_2398_ = lean_ctor_get(v___x_2396_, 1);
v_ngen_2399_ = lean_ctor_get(v___x_2396_, 2);
v_auxDeclNGen_2400_ = lean_ctor_get(v___x_2396_, 3);
v_traceState_2401_ = lean_ctor_get(v___x_2396_, 4);
v_recordedDeps_2402_ = lean_ctor_get(v___x_2396_, 6);
v_messages_2403_ = lean_ctor_get(v___x_2396_, 7);
v_infoState_2404_ = lean_ctor_get(v___x_2396_, 8);
v_snapshotTasks_2405_ = lean_ctor_get(v___x_2396_, 9);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2499_ == 0)
{
lean_object* v_unused_2500_; 
v_unused_2500_ = lean_ctor_get(v___x_2396_, 5);
lean_dec(v_unused_2500_);
v___x_2407_ = v___x_2396_;
v_isShared_2408_ = v_isSharedCheck_2499_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_snapshotTasks_2405_);
lean_inc(v_infoState_2404_);
lean_inc(v_messages_2403_);
lean_inc(v_recordedDeps_2402_);
lean_inc(v_traceState_2401_);
lean_inc(v_auxDeclNGen_2400_);
lean_inc(v_ngen_2399_);
lean_inc(v_nextMacroScope_2398_);
lean_inc(v_env_2397_);
lean_dec(v___x_2396_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2499_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2409_; lean_object* v___x_2411_; 
lean_inc(v_declName_2329_);
v___x_2409_ = l_Lean_markAuxRecursor(v_env_2397_, v_declName_2329_);
if (v_isShared_2408_ == 0)
{
lean_ctor_set(v___x_2407_, 5, v___x_2380_);
lean_ctor_set(v___x_2407_, 0, v___x_2409_);
v___x_2411_ = v___x_2407_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2409_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_nextMacroScope_2398_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_ngen_2399_);
lean_ctor_set(v_reuseFailAlloc_2498_, 3, v_auxDeclNGen_2400_);
lean_ctor_set(v_reuseFailAlloc_2498_, 4, v_traceState_2401_);
lean_ctor_set(v_reuseFailAlloc_2498_, 5, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2498_, 6, v_recordedDeps_2402_);
lean_ctor_set(v_reuseFailAlloc_2498_, 7, v_messages_2403_);
lean_ctor_set(v_reuseFailAlloc_2498_, 8, v_infoState_2404_);
lean_ctor_set(v_reuseFailAlloc_2498_, 9, v_snapshotTasks_2405_);
v___x_2411_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v_mctx_2414_; lean_object* v_zetaDeltaFVarIds_2415_; lean_object* v_postponed_2416_; lean_object* v_diag_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2496_; 
v___x_2412_ = lean_st_ref_put(v_a_2334_, v___x_2411_);
v___x_2413_ = lean_st_ref_take(v_a_2332_);
v_mctx_2414_ = lean_ctor_get(v___x_2413_, 0);
v_zetaDeltaFVarIds_2415_ = lean_ctor_get(v___x_2413_, 2);
v_postponed_2416_ = lean_ctor_get(v___x_2413_, 3);
v_diag_2417_ = lean_ctor_get(v___x_2413_, 4);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; 
v_unused_2497_ = lean_ctor_get(v___x_2413_, 1);
lean_dec(v_unused_2497_);
v___x_2419_ = v___x_2413_;
v_isShared_2420_ = v_isSharedCheck_2496_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_diag_2417_);
lean_inc(v_postponed_2416_);
lean_inc(v_zetaDeltaFVarIds_2415_);
lean_inc(v_mctx_2414_);
lean_dec(v___x_2413_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2496_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
lean_ctor_set(v___x_2419_, 1, v___x_2392_);
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_mctx_2414_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_zetaDeltaFVarIds_2415_);
lean_ctor_set(v_reuseFailAlloc_2495_, 3, v_postponed_2416_);
lean_ctor_set(v_reuseFailAlloc_2495_, 4, v_diag_2417_);
v___x_2422_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_env_2425_; lean_object* v_nextMacroScope_2426_; lean_object* v_ngen_2427_; lean_object* v_auxDeclNGen_2428_; lean_object* v_traceState_2429_; lean_object* v_recordedDeps_2430_; lean_object* v_messages_2431_; lean_object* v_infoState_2432_; lean_object* v_snapshotTasks_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2493_; 
v___x_2423_ = lean_st_ref_put(v_a_2332_, v___x_2422_);
v___x_2424_ = lean_st_ref_take(v_a_2334_);
v_env_2425_ = lean_ctor_get(v___x_2424_, 0);
v_nextMacroScope_2426_ = lean_ctor_get(v___x_2424_, 1);
v_ngen_2427_ = lean_ctor_get(v___x_2424_, 2);
v_auxDeclNGen_2428_ = lean_ctor_get(v___x_2424_, 3);
v_traceState_2429_ = lean_ctor_get(v___x_2424_, 4);
v_recordedDeps_2430_ = lean_ctor_get(v___x_2424_, 6);
v_messages_2431_ = lean_ctor_get(v___x_2424_, 7);
v_infoState_2432_ = lean_ctor_get(v___x_2424_, 8);
v_snapshotTasks_2433_ = lean_ctor_get(v___x_2424_, 9);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v___x_2424_, 5);
lean_dec(v_unused_2494_);
v___x_2435_ = v___x_2424_;
v_isShared_2436_ = v_isSharedCheck_2493_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_snapshotTasks_2433_);
lean_inc(v_infoState_2432_);
lean_inc(v_messages_2431_);
lean_inc(v_recordedDeps_2430_);
lean_inc(v_traceState_2429_);
lean_inc(v_auxDeclNGen_2428_);
lean_inc(v_ngen_2427_);
lean_inc(v_nextMacroScope_2426_);
lean_inc(v_env_2425_);
lean_dec(v___x_2424_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2493_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2437_; lean_object* v___x_2439_; 
lean_inc(v_declName_2329_);
v___x_2437_ = l_Lean_Meta_addToCompletionBlackList(v_env_2425_, v_declName_2329_);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 5, v___x_2380_);
lean_ctor_set(v___x_2435_, 0, v___x_2437_);
v___x_2439_ = v___x_2435_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_nextMacroScope_2426_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_ngen_2427_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_auxDeclNGen_2428_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_traceState_2429_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_recordedDeps_2430_);
lean_ctor_set(v_reuseFailAlloc_2492_, 7, v_messages_2431_);
lean_ctor_set(v_reuseFailAlloc_2492_, 8, v_infoState_2432_);
lean_ctor_set(v_reuseFailAlloc_2492_, 9, v_snapshotTasks_2433_);
v___x_2439_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v_mctx_2442_; lean_object* v_zetaDeltaFVarIds_2443_; lean_object* v_postponed_2444_; lean_object* v_diag_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2490_; 
v___x_2440_ = lean_st_ref_put(v_a_2334_, v___x_2439_);
v___x_2441_ = lean_st_ref_take(v_a_2332_);
v_mctx_2442_ = lean_ctor_get(v___x_2441_, 0);
v_zetaDeltaFVarIds_2443_ = lean_ctor_get(v___x_2441_, 2);
v_postponed_2444_ = lean_ctor_get(v___x_2441_, 3);
v_diag_2445_ = lean_ctor_get(v___x_2441_, 4);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v___x_2441_, 1);
lean_dec(v_unused_2491_);
v___x_2447_ = v___x_2441_;
v_isShared_2448_ = v_isSharedCheck_2490_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_diag_2445_);
lean_inc(v_postponed_2444_);
lean_inc(v_zetaDeltaFVarIds_2443_);
lean_inc(v_mctx_2442_);
lean_dec(v___x_2441_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2490_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 1, v___x_2392_);
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_mctx_2442_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_zetaDeltaFVarIds_2443_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_postponed_2444_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_diag_2445_);
v___x_2450_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v_env_2453_; lean_object* v_nextMacroScope_2454_; lean_object* v_ngen_2455_; lean_object* v_auxDeclNGen_2456_; lean_object* v_traceState_2457_; lean_object* v_recordedDeps_2458_; lean_object* v_messages_2459_; lean_object* v_infoState_2460_; lean_object* v_snapshotTasks_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2487_; 
v___x_2451_ = lean_st_ref_put(v_a_2332_, v___x_2450_);
v___x_2452_ = lean_st_ref_take(v_a_2334_);
v_env_2453_ = lean_ctor_get(v___x_2452_, 0);
v_nextMacroScope_2454_ = lean_ctor_get(v___x_2452_, 1);
v_ngen_2455_ = lean_ctor_get(v___x_2452_, 2);
v_auxDeclNGen_2456_ = lean_ctor_get(v___x_2452_, 3);
v_traceState_2457_ = lean_ctor_get(v___x_2452_, 4);
v_recordedDeps_2458_ = lean_ctor_get(v___x_2452_, 6);
v_messages_2459_ = lean_ctor_get(v___x_2452_, 7);
v_infoState_2460_ = lean_ctor_get(v___x_2452_, 8);
v_snapshotTasks_2461_ = lean_ctor_get(v___x_2452_, 9);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2487_ == 0)
{
lean_object* v_unused_2488_; 
v_unused_2488_ = lean_ctor_get(v___x_2452_, 5);
lean_dec(v_unused_2488_);
v___x_2463_ = v___x_2452_;
v_isShared_2464_ = v_isSharedCheck_2487_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_snapshotTasks_2461_);
lean_inc(v_infoState_2460_);
lean_inc(v_messages_2459_);
lean_inc(v_recordedDeps_2458_);
lean_inc(v_traceState_2457_);
lean_inc(v_auxDeclNGen_2456_);
lean_inc(v_ngen_2455_);
lean_inc(v_nextMacroScope_2454_);
lean_inc(v_env_2453_);
lean_dec(v___x_2452_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2487_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_inc(v_declName_2329_);
v___x_2465_ = l_Lean_addProtected(v_env_2453_, v_declName_2329_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 5, v___x_2380_);
lean_ctor_set(v___x_2463_, 0, v___x_2465_);
v___x_2467_ = v___x_2463_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2465_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_nextMacroScope_2454_);
lean_ctor_set(v_reuseFailAlloc_2486_, 2, v_ngen_2455_);
lean_ctor_set(v_reuseFailAlloc_2486_, 3, v_auxDeclNGen_2456_);
lean_ctor_set(v_reuseFailAlloc_2486_, 4, v_traceState_2457_);
lean_ctor_set(v_reuseFailAlloc_2486_, 5, v___x_2380_);
lean_ctor_set(v_reuseFailAlloc_2486_, 6, v_recordedDeps_2458_);
lean_ctor_set(v_reuseFailAlloc_2486_, 7, v_messages_2459_);
lean_ctor_set(v_reuseFailAlloc_2486_, 8, v_infoState_2460_);
lean_ctor_set(v_reuseFailAlloc_2486_, 9, v_snapshotTasks_2461_);
v___x_2467_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_mctx_2470_; lean_object* v_zetaDeltaFVarIds_2471_; lean_object* v_postponed_2472_; lean_object* v_diag_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2484_; 
v___x_2468_ = lean_st_ref_put(v_a_2334_, v___x_2467_);
v___x_2469_ = lean_st_ref_take(v_a_2332_);
v_mctx_2470_ = lean_ctor_get(v___x_2469_, 0);
v_zetaDeltaFVarIds_2471_ = lean_ctor_get(v___x_2469_, 2);
v_postponed_2472_ = lean_ctor_get(v___x_2469_, 3);
v_diag_2473_ = lean_ctor_get(v___x_2469_, 4);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v___x_2469_, 1);
lean_dec(v_unused_2485_);
v___x_2475_ = v___x_2469_;
v_isShared_2476_ = v_isSharedCheck_2484_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_diag_2473_);
lean_inc(v_postponed_2472_);
lean_inc(v_zetaDeltaFVarIds_2471_);
lean_inc(v_mctx_2470_);
lean_dec(v___x_2469_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2484_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 1, v___x_2392_);
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_mctx_2470_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_zetaDeltaFVarIds_2471_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_postponed_2472_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_diag_2473_);
v___x_2478_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_st_ref_put(v_a_2332_, v___x_2478_);
v___x_2480_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2329_);
v___x_2481_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2480_, v_declName_2329_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v___x_2482_; 
lean_dec_ref_known(v___x_2481_, 1);
v___x_2482_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2329_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
return v___x_2482_;
}
else
{
lean_dec(v_declName_2329_);
return v___x_2481_;
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
lean_dec(v_declName_2329_);
return v___x_2365_;
}
}
}
else
{
lean_object* v_a_2509_; lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
lean_dec(v_levelParams_2346_);
lean_dec(v_declName_2329_);
v_a_2509_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2516_ == 0)
{
v___x_2511_ = v___x_2359_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_inc(v_a_2509_);
lean_dec(v___x_2359_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
}
else
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec(v___x_2349_);
lean_dec_ref(v_type_2347_);
lean_dec(v_levelParams_2346_);
lean_dec(v_name_2345_);
lean_dec(v___x_2342_);
lean_del_object(v___x_2340_);
lean_dec_ref(v_val_2338_);
lean_dec(v_indName_2330_);
lean_dec(v_declName_2329_);
v___x_2518_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2519_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2518_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
return v___x_2519_;
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec(v___x_2342_);
lean_del_object(v___x_2340_);
lean_dec_ref(v_val_2338_);
lean_dec(v_indName_2330_);
lean_dec(v_declName_2329_);
v_a_2520_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2343_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2343_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec(v_a_2337_);
lean_dec(v_indName_2330_);
lean_dec(v_declName_2329_);
v___x_2529_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2530_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2529_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
return v___x_2530_;
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec(v_indName_2330_);
lean_dec(v_declName_2329_);
v_a_2531_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2336_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2336_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2539_, lean_object* v_indName_2540_, lean_object* v_a_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2539_, v_indName_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
lean_dec(v_a_2542_);
lean_dec_ref(v_a_2541_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2547_, lean_object* v_name_2548_, lean_object* v_type_2549_, lean_object* v_k_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_){
_start:
{
lean_object* v___x_2556_; 
v___x_2556_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2548_, v_type_2549_, v_k_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2557_, lean_object* v_name_2558_, lean_object* v_type_2559_, lean_object* v_k_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2557_, v_name_2558_, v_type_2559_, v_k_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec_ref(v___y_2561_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2567_, lean_object* v_params_2568_, lean_object* v_alts_2569_, lean_object* v___x_2570_, lean_object* v_ism2_2571_, lean_object* v_motive_2572_, lean_object* v_val_2573_, lean_object* v_indName_2574_, lean_object* v___x_2575_, lean_object* v___x_2576_, lean_object* v___x_2577_, lean_object* v_as_2578_, size_t v_sz_2579_, size_t v_i_2580_, lean_object* v_bs_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2567_, v_params_2568_, v_alts_2569_, v___x_2570_, v_ism2_2571_, v_motive_2572_, v_val_2573_, v_indName_2574_, v___x_2575_, v___x_2576_, v___x_2577_, v_sz_2579_, v_i_2580_, v_bs_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2588_ = _args[0];
lean_object* v_params_2589_ = _args[1];
lean_object* v_alts_2590_ = _args[2];
lean_object* v___x_2591_ = _args[3];
lean_object* v_ism2_2592_ = _args[4];
lean_object* v_motive_2593_ = _args[5];
lean_object* v_val_2594_ = _args[6];
lean_object* v_indName_2595_ = _args[7];
lean_object* v___x_2596_ = _args[8];
lean_object* v___x_2597_ = _args[9];
lean_object* v___x_2598_ = _args[10];
lean_object* v_as_2599_ = _args[11];
lean_object* v_sz_2600_ = _args[12];
lean_object* v_i_2601_ = _args[13];
lean_object* v_bs_2602_ = _args[14];
lean_object* v___y_2603_ = _args[15];
lean_object* v___y_2604_ = _args[16];
lean_object* v___y_2605_ = _args[17];
lean_object* v___y_2606_ = _args[18];
lean_object* v___y_2607_ = _args[19];
_start:
{
size_t v_sz_boxed_2608_; size_t v_i_boxed_2609_; lean_object* v_res_2610_; 
v_sz_boxed_2608_ = lean_unbox_usize(v_sz_2600_);
lean_dec(v_sz_2600_);
v_i_boxed_2609_ = lean_unbox_usize(v_i_2601_);
lean_dec(v_i_2601_);
v_res_2610_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2588_, v_params_2589_, v_alts_2590_, v___x_2591_, v_ism2_2592_, v_motive_2593_, v_val_2594_, v_indName_2595_, v___x_2596_, v___x_2597_, v___x_2598_, v_as_2599_, v_sz_boxed_2608_, v_i_boxed_2609_, v_bs_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_as_2599_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2611_, lean_object* v_params_2612_, lean_object* v___x_2613_, lean_object* v_motive_2614_, lean_object* v_as_2615_, size_t v_sz_2616_, size_t v_i_2617_, lean_object* v_bs_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2611_, v_params_2612_, v___x_2613_, v_motive_2614_, v_sz_2616_, v_i_2617_, v_bs_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2625_, lean_object* v_params_2626_, lean_object* v___x_2627_, lean_object* v_motive_2628_, lean_object* v_as_2629_, lean_object* v_sz_2630_, lean_object* v_i_2631_, lean_object* v_bs_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
size_t v_sz_boxed_2638_; size_t v_i_boxed_2639_; lean_object* v_res_2640_; 
v_sz_boxed_2638_ = lean_unbox_usize(v_sz_2630_);
lean_dec(v_sz_2630_);
v_i_boxed_2639_ = lean_unbox_usize(v_i_2631_);
lean_dec(v_i_2631_);
v_res_2640_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2625_, v_params_2626_, v___x_2627_, v_motive_2628_, v_as_2629_, v_sz_boxed_2638_, v_i_boxed_2639_, v_bs_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec_ref(v_as_2629_);
lean_dec_ref(v_params_2626_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2641_, uint8_t v_s_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2641_, v_s_2642_, v___y_2644_, v___y_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2649_, lean_object* v_s_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
uint8_t v_s_boxed_2656_; lean_object* v_res_2657_; 
v_s_boxed_2656_ = lean_unbox(v_s_2650_);
v_res_2657_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2649_, v_s_boxed_2656_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2658_, lean_object* v_constName_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2666_, lean_object* v_constName_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2666_, v_constName_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2674_, lean_object* v_attrName_2675_, lean_object* v_declName_2676_, lean_object* v_asyncPrefix_x3f_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
lean_object* v___x_2683_; 
v___x_2683_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2675_, v_declName_2676_, v_asyncPrefix_x3f_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2684_, lean_object* v_attrName_2685_, lean_object* v_declName_2686_, lean_object* v_asyncPrefix_x3f_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2684_, v_attrName_2685_, v_declName_2686_, v_asyncPrefix_x3f_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2694_, lean_object* v_attrName_2695_, lean_object* v_declName_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2695_, v_declName_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2703_, lean_object* v_attrName_2704_, lean_object* v_declName_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2703_, v_attrName_2704_, v_declName_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2712_, lean_object* v_ref_2713_, lean_object* v_constName_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2713_, v_constName_2714_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2721_, lean_object* v_ref_2722_, lean_object* v_constName_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2721_, v_ref_2722_, v_constName_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v_ref_2722_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2730_, lean_object* v_msg_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2738_, lean_object* v_msg_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2738_, v_msg_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2746_, lean_object* v_ref_2747_, lean_object* v_msg_2748_, lean_object* v_declHint_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2747_, v_msg_2748_, v_declHint_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2756_, lean_object* v_ref_2757_, lean_object* v_msg_2758_, lean_object* v_declHint_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2756_, v_ref_2757_, v_msg_2758_, v_declHint_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_ref_2757_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2766_, lean_object* v_declHint_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2766_, v_declHint_2767_, v___y_2771_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2774_, lean_object* v_declHint_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2774_, v_declHint_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2782_, lean_object* v_ref_2783_, lean_object* v_msg_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2783_, v_msg_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2791_, lean_object* v_ref_2792_, lean_object* v_msg_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2791_, v_ref_2792_, v_msg_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v_ref_2792_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2800_, lean_object* v___y_2801_){
_start:
{
uint8_t v___x_2803_; 
v___x_2803_ = l_Lean_Expr_hasMVar(v_e_2800_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2804_, 0, v_e_2800_);
return v___x_2804_;
}
else
{
lean_object* v___x_2805_; lean_object* v_mctx_2806_; lean_object* v___x_2807_; lean_object* v_fst_2808_; lean_object* v_snd_2809_; lean_object* v___x_2810_; lean_object* v_cache_2811_; lean_object* v_zetaDeltaFVarIds_2812_; lean_object* v_postponed_2813_; lean_object* v_diag_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2823_; 
v___x_2805_ = lean_st_ref_get(v___y_2801_);
v_mctx_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc_ref(v_mctx_2806_);
lean_dec(v___x_2805_);
v___x_2807_ = l_Lean_instantiateMVarsCore(v_mctx_2806_, v_e_2800_);
v_fst_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_fst_2808_);
v_snd_2809_ = lean_ctor_get(v___x_2807_, 1);
lean_inc(v_snd_2809_);
lean_dec_ref(v___x_2807_);
v___x_2810_ = lean_st_ref_take(v___y_2801_);
v_cache_2811_ = lean_ctor_get(v___x_2810_, 1);
v_zetaDeltaFVarIds_2812_ = lean_ctor_get(v___x_2810_, 2);
v_postponed_2813_ = lean_ctor_get(v___x_2810_, 3);
v_diag_2814_ = lean_ctor_get(v___x_2810_, 4);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v___x_2810_, 0);
lean_dec(v_unused_2824_);
v___x_2816_ = v___x_2810_;
v_isShared_2817_ = v_isSharedCheck_2823_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_diag_2814_);
lean_inc(v_postponed_2813_);
lean_inc(v_zetaDeltaFVarIds_2812_);
lean_inc(v_cache_2811_);
lean_dec(v___x_2810_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2823_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 0, v_snd_2809_);
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_snd_2809_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v_cache_2811_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_zetaDeltaFVarIds_2812_);
lean_ctor_set(v_reuseFailAlloc_2822_, 3, v_postponed_2813_);
lean_ctor_set(v_reuseFailAlloc_2822_, 4, v_diag_2814_);
v___x_2819_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_st_ref_put(v___y_2801_, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2821_, 0, v_fst_2808_);
return v___x_2821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2825_, v___y_2826_);
lean_dec(v___y_2826_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2829_, v___y_2831_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_){
_start:
{
lean_object* v_res_2842_; 
v_res_2842_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2843_, lean_object* v_info_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; lean_object* v_env_2849_; lean_object* v_nextMacroScope_2850_; lean_object* v_ngen_2851_; lean_object* v_auxDeclNGen_2852_; lean_object* v_traceState_2853_; lean_object* v_recordedDeps_2854_; lean_object* v_messages_2855_; lean_object* v_infoState_2856_; lean_object* v_snapshotTasks_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2884_; 
v___x_2848_ = lean_st_ref_take(v___y_2846_);
v_env_2849_ = lean_ctor_get(v___x_2848_, 0);
v_nextMacroScope_2850_ = lean_ctor_get(v___x_2848_, 1);
v_ngen_2851_ = lean_ctor_get(v___x_2848_, 2);
v_auxDeclNGen_2852_ = lean_ctor_get(v___x_2848_, 3);
v_traceState_2853_ = lean_ctor_get(v___x_2848_, 4);
v_recordedDeps_2854_ = lean_ctor_get(v___x_2848_, 6);
v_messages_2855_ = lean_ctor_get(v___x_2848_, 7);
v_infoState_2856_ = lean_ctor_get(v___x_2848_, 8);
v_snapshotTasks_2857_ = lean_ctor_get(v___x_2848_, 9);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v___x_2848_, 5);
lean_dec(v_unused_2885_);
v___x_2859_ = v___x_2848_;
v_isShared_2860_ = v_isSharedCheck_2884_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_snapshotTasks_2857_);
lean_inc(v_infoState_2856_);
lean_inc(v_messages_2855_);
lean_inc(v_recordedDeps_2854_);
lean_inc(v_traceState_2853_);
lean_inc(v_auxDeclNGen_2852_);
lean_inc(v_ngen_2851_);
lean_inc(v_nextMacroScope_2850_);
lean_inc(v_env_2849_);
lean_dec(v___x_2848_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2884_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2861_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2849_, v_matcherName_2843_, v_info_2844_);
v___x_2862_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 5, v___x_2862_);
lean_ctor_set(v___x_2859_, 0, v___x_2861_);
v___x_2864_ = v___x_2859_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_nextMacroScope_2850_);
lean_ctor_set(v_reuseFailAlloc_2883_, 2, v_ngen_2851_);
lean_ctor_set(v_reuseFailAlloc_2883_, 3, v_auxDeclNGen_2852_);
lean_ctor_set(v_reuseFailAlloc_2883_, 4, v_traceState_2853_);
lean_ctor_set(v_reuseFailAlloc_2883_, 5, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2883_, 6, v_recordedDeps_2854_);
lean_ctor_set(v_reuseFailAlloc_2883_, 7, v_messages_2855_);
lean_ctor_set(v_reuseFailAlloc_2883_, 8, v_infoState_2856_);
lean_ctor_set(v_reuseFailAlloc_2883_, 9, v_snapshotTasks_2857_);
v___x_2864_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v_mctx_2867_; lean_object* v_zetaDeltaFVarIds_2868_; lean_object* v_postponed_2869_; lean_object* v_diag_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2881_; 
v___x_2865_ = lean_st_ref_put(v___y_2846_, v___x_2864_);
v___x_2866_ = lean_st_ref_take(v___y_2845_);
v_mctx_2867_ = lean_ctor_get(v___x_2866_, 0);
v_zetaDeltaFVarIds_2868_ = lean_ctor_get(v___x_2866_, 2);
v_postponed_2869_ = lean_ctor_get(v___x_2866_, 3);
v_diag_2870_ = lean_ctor_get(v___x_2866_, 4);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v___x_2866_, 1);
lean_dec(v_unused_2882_);
v___x_2872_ = v___x_2866_;
v_isShared_2873_ = v_isSharedCheck_2881_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_diag_2870_);
lean_inc(v_postponed_2869_);
lean_inc(v_zetaDeltaFVarIds_2868_);
lean_inc(v_mctx_2867_);
lean_dec(v___x_2866_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2881_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2874_ = lean_box(0);
v___x_2875_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 1, v___x_2875_);
v___x_2877_ = v___x_2872_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_mctx_2867_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_zetaDeltaFVarIds_2868_);
lean_ctor_set(v_reuseFailAlloc_2880_, 3, v_postponed_2869_);
lean_ctor_set(v_reuseFailAlloc_2880_, 4, v_diag_2870_);
v___x_2877_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = lean_st_ref_put(v___y_2845_, v___x_2877_);
v___x_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2874_);
return v___x_2879_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2886_, lean_object* v_info_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2886_, v_info_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec(v___y_2888_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2892_, lean_object* v_info_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2892_, v_info_2893_, v___y_2895_, v___y_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2900_, lean_object* v_info_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2900_, v_info_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2908_, lean_object* v___x_2909_, lean_object* v_newEqs1_2910_, uint8_t v___x_2911_, uint8_t v___x_2912_, uint8_t v___x_2913_, lean_object* v_ism1_x27_2914_, lean_object* v_ism2_x27_2915_, lean_object* v_newRefls1_2916_, lean_object* v_newEqs2_2917_, lean_object* v_newRefls2_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = l_Lean_mkAppN(v_motive_2908_, v___x_2909_);
v___x_2925_ = l_Array_append___redArg(v_newEqs1_2910_, v_newEqs2_2917_);
v___x_2926_ = l_Lean_Meta_mkForallFVars(v___x_2925_, v___x_2924_, v___x_2911_, v___x_2912_, v___x_2912_, v___x_2913_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec_ref(v___x_2925_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
v___x_2928_ = l_Array_append___redArg(v_ism1_x27_2914_, v_ism2_x27_2915_);
v___x_2929_ = l_Lean_Meta_mkLambdaFVars(v___x_2928_, v_a_2927_, v___x_2911_, v___x_2912_, v___x_2911_, v___x_2912_, v___x_2913_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec_ref(v___x_2928_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2939_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2939_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2939_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2934_ = l_Array_append___redArg(v_newRefls1_2916_, v_newRefls2_2918_);
v___x_2935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2935_, 0, v_a_2930_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
if (v_isShared_2933_ == 0)
{
lean_ctor_set(v___x_2932_, 0, v___x_2935_);
v___x_2937_ = v___x_2932_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v___x_2935_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
else
{
lean_object* v_a_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2947_; 
lean_dec_ref(v_newRefls1_2916_);
v_a_2940_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2947_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2947_ == 0)
{
v___x_2942_ = v___x_2929_;
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_a_2940_);
lean_dec(v___x_2929_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2947_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2945_; 
if (v_isShared_2943_ == 0)
{
v___x_2945_ = v___x_2942_;
goto v_reusejp_2944_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
v___x_2945_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2944_;
}
v_reusejp_2944_:
{
return v___x_2945_;
}
}
}
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec_ref(v_newRefls1_2916_);
lean_dec_ref(v_ism1_x27_2914_);
v_a_2948_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2926_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2926_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2956_, lean_object* v___x_2957_, lean_object* v_newEqs1_2958_, lean_object* v___x_2959_, lean_object* v___x_2960_, lean_object* v___x_2961_, lean_object* v_ism1_x27_2962_, lean_object* v_ism2_x27_2963_, lean_object* v_newRefls1_2964_, lean_object* v_newEqs2_2965_, lean_object* v_newRefls2_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_){
_start:
{
uint8_t v___x_14959__boxed_2972_; uint8_t v___x_14960__boxed_2973_; uint8_t v___x_14961__boxed_2974_; lean_object* v_res_2975_; 
v___x_14959__boxed_2972_ = lean_unbox(v___x_2959_);
v___x_14960__boxed_2973_ = lean_unbox(v___x_2960_);
v___x_14961__boxed_2974_ = lean_unbox(v___x_2961_);
v_res_2975_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2956_, v___x_2957_, v_newEqs1_2958_, v___x_14959__boxed_2972_, v___x_14960__boxed_2973_, v___x_14961__boxed_2974_, v_ism1_x27_2962_, v_ism2_x27_2963_, v_newRefls1_2964_, v_newEqs2_2965_, v_newRefls2_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v_newRefls2_2966_);
lean_dec_ref(v_newEqs2_2965_);
lean_dec_ref(v_ism2_x27_2963_);
lean_dec_ref(v___x_2957_);
return v_res_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2976_, lean_object* v___x_2977_, uint8_t v___x_2978_, uint8_t v___x_2979_, uint8_t v___x_2980_, lean_object* v_ism1_x27_2981_, lean_object* v_ism2_x27_2982_, lean_object* v_is_2983_, lean_object* v___x_2984_, lean_object* v_newEqs1_2985_, lean_object* v_newRefls1_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___f_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2992_ = lean_box(v___x_2978_);
v___x_2993_ = lean_box(v___x_2979_);
v___x_2994_ = lean_box(v___x_2980_);
lean_inc_ref(v_ism2_x27_2982_);
v___f_2995_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2995_, 0, v_motive_2976_);
lean_closure_set(v___f_2995_, 1, v___x_2977_);
lean_closure_set(v___f_2995_, 2, v_newEqs1_2985_);
lean_closure_set(v___f_2995_, 3, v___x_2992_);
lean_closure_set(v___f_2995_, 4, v___x_2993_);
lean_closure_set(v___f_2995_, 5, v___x_2994_);
lean_closure_set(v___f_2995_, 6, v_ism1_x27_2981_);
lean_closure_set(v___f_2995_, 7, v_ism2_x27_2982_);
lean_closure_set(v___f_2995_, 8, v_newRefls1_2986_);
v___x_2996_ = lean_array_push(v_is_2983_, v___x_2984_);
v___x_2997_ = l_Lean_Meta_withNewEqs___redArg(v___x_2996_, v_ism2_x27_2982_, v___f_2995_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2998_, lean_object* v___x_2999_, lean_object* v___x_3000_, lean_object* v___x_3001_, lean_object* v___x_3002_, lean_object* v_ism1_x27_3003_, lean_object* v_ism2_x27_3004_, lean_object* v_is_3005_, lean_object* v___x_3006_, lean_object* v_newEqs1_3007_, lean_object* v_newRefls1_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
uint8_t v___x_15050__boxed_3014_; uint8_t v___x_15051__boxed_3015_; uint8_t v___x_15052__boxed_3016_; lean_object* v_res_3017_; 
v___x_15050__boxed_3014_ = lean_unbox(v___x_3000_);
v___x_15051__boxed_3015_ = lean_unbox(v___x_3001_);
v___x_15052__boxed_3016_ = lean_unbox(v___x_3002_);
v_res_3017_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2998_, v___x_2999_, v___x_15050__boxed_3014_, v___x_15051__boxed_3015_, v___x_15052__boxed_3016_, v_ism1_x27_3003_, v_ism2_x27_3004_, v_is_3005_, v___x_3006_, v_newEqs1_3007_, v_newRefls1_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
lean_dec(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_3018_, uint8_t v___x_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Lean_addDecl(v___x_3018_, v___x_3019_, v___y_3022_, v___y_3023_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3026_, lean_object* v___x_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_){
_start:
{
uint8_t v___x_15092__boxed_3033_; lean_object* v_res_3034_; 
v___x_15092__boxed_3033_ = lean_unbox(v___x_3027_);
v_res_3034_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3026_, v___x_15092__boxed_3033_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec_ref(v___y_3028_);
return v_res_3034_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3037_ = l_Lean_stringToMessageData(v___x_3036_);
return v___x_3037_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3040_ = l_Lean_stringToMessageData(v___x_3039_);
return v___x_3040_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3046_ = lean_box(0);
v___x_3047_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3048_ = l_Lean_mkConst(v___x_3047_, v___x_3046_);
return v___x_3048_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3051_ = l_Lean_stringToMessageData(v___x_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3052_, lean_object* v_a_3053_, lean_object* v___x_3054_, lean_object* v_zs1_3055_, lean_object* v_snd_3056_, uint8_t v___x_3057_, uint8_t v___x_3058_, uint8_t v___x_3059_, lean_object* v_alts_3060_, lean_object* v_zs2_3061_, lean_object* v___ctorRet2_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = lean_array_get_borrowed(v___x_3052_, v_a_3053_, v___x_3054_);
lean_inc_ref(v_zs1_3055_);
v___x_3069_ = l_Array_append___redArg(v_zs1_3055_, v_zs2_3061_);
lean_inc(v___x_3068_);
v___x_3070_ = l_Lean_Meta_instantiateForall(v___x_3068_, v___x_3069_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v___x_3072_ = lean_box(0);
v___x_3073_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3071_, v___x_3072_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v_a_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_a_3074_ = lean_ctor_get(v___x_3073_, 0);
lean_inc(v_a_3074_);
lean_dec_ref_known(v___x_3073_, 1);
v___x_3075_ = l_Lean_Expr_mvarId_x21(v_a_3074_);
v___x_3076_ = lean_array_get_size(v_snd_3056_);
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_box(0);
lean_inc_ref(v___y_3065_);
v___x_3079_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3076_, v___x_3075_, v___x_3077_, v___x_3078_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
if (lean_obj_tag(v_a_3080_) == 1)
{
lean_object* v_val_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3128_; 
v_val_3081_ = lean_ctor_get(v_a_3080_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v_a_3080_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3083_ = v_a_3080_;
v_isShared_3084_ = v_isSharedCheck_3128_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_val_3081_);
lean_dec(v_a_3080_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3128_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v_fst_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3126_; 
v_fst_3085_ = lean_ctor_get(v_val_3081_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_val_3081_);
if (v_isSharedCheck_3126_ == 0)
{
lean_object* v_unused_3127_; 
v_unused_3127_ = lean_ctor_get(v_val_3081_, 1);
lean_dec(v_unused_3127_);
v___x_3087_ = v_val_3081_;
v_isShared_3088_ = v_isSharedCheck_3126_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_fst_3085_);
lean_dec(v_val_3081_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3126_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___y_3090_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3118_ = lean_array_get_borrowed(v___x_3052_, v_alts_3060_, v___x_3054_);
v___x_3119_ = lean_array_get_size(v_zs1_3055_);
lean_dec_ref(v_zs1_3055_);
v___x_3120_ = lean_unsigned_to_nat(0u);
v___x_3121_ = lean_nat_dec_eq(v___x_3119_, v___x_3120_);
if (v___x_3121_ == 0)
{
lean_inc(v___x_3118_);
v___y_3090_ = v___x_3118_;
goto v___jp_3089_;
}
else
{
lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3122_ = lean_array_get_size(v_zs2_3061_);
v___x_3123_ = lean_nat_dec_eq(v___x_3122_, v___x_3120_);
if (v___x_3123_ == 0)
{
lean_inc(v___x_3118_);
v___y_3090_ = v___x_3118_;
goto v___jp_3089_;
}
else
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3118_);
v___x_3125_ = l_Lean_Expr_app___override(v___x_3118_, v___x_3124_);
v___y_3090_ = v___x_3125_;
goto v___jp_3089_;
}
}
v___jp_3089_:
{
uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; 
v___x_3091_ = 0;
v___x_3092_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3092_, 0, v___x_3091_);
lean_ctor_set_uint8(v___x_3092_, 1, v___x_3057_);
lean_ctor_set_uint8(v___x_3092_, 2, v___x_3058_);
lean_ctor_set_uint8(v___x_3092_, 3, v___x_3057_);
lean_inc_ref(v___y_3090_);
lean_inc(v_fst_3085_);
v___x_3093_ = l_Lean_MVarId_apply(v_fst_3085_, v___y_3090_, v___x_3092_, v___x_3078_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
if (lean_obj_tag(v_a_3094_) == 0)
{
lean_object* v___x_3095_; 
lean_dec_ref(v___y_3090_);
lean_del_object(v___x_3087_);
lean_dec(v_fst_3085_);
lean_del_object(v___x_3083_);
v___x_3095_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3074_, v___y_3064_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3097_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_a_3096_);
lean_dec_ref_known(v___x_3095_, 1);
v___x_3097_ = l_Lean_Meta_mkLambdaFVars(v___x_3069_, v_a_3096_, v___x_3058_, v___x_3057_, v___x_3058_, v___x_3057_, v___x_3059_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
lean_dec_ref(v___x_3069_);
return v___x_3097_;
}
else
{
lean_dec_ref(v___x_3069_);
return v___x_3095_;
}
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
lean_dec(v_a_3094_);
lean_dec(v_a_3074_);
lean_dec_ref(v___x_3069_);
v___x_3098_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3099_ = l_Lean_MessageData_ofExpr(v___y_3090_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set_tag(v___x_3087_, 7);
lean_ctor_set(v___x_3087_, 1, v___x_3099_);
lean_ctor_set(v___x_3087_, 0, v___x_3098_);
v___x_3101_ = v___x_3087_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3098_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3105_; 
v___x_3102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3101_);
lean_ctor_set(v___x_3103_, 1, v___x_3102_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set(v___x_3083_, 0, v_fst_3085_);
v___x_3105_ = v___x_3083_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_fst_3085_);
v___x_3105_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3103_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
v___x_3107_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3106_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
return v___x_3107_;
}
}
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec_ref(v___y_3090_);
lean_del_object(v___x_3087_);
lean_dec(v_fst_3085_);
lean_del_object(v___x_3083_);
lean_dec(v_a_3074_);
lean_dec_ref(v___x_3069_);
v_a_3110_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3093_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3093_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
lean_dec(v_a_3080_);
lean_dec(v_a_3074_);
lean_dec_ref(v___x_3069_);
lean_dec_ref(v_zs1_3055_);
v___x_3129_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3130_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3129_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_);
return v___x_3130_;
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v_a_3074_);
lean_dec_ref(v___x_3069_);
lean_dec_ref(v_zs1_3055_);
v_a_3131_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3079_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3079_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_dec_ref(v___x_3069_);
lean_dec_ref(v_zs1_3055_);
return v___x_3073_;
}
}
else
{
lean_dec_ref(v___x_3069_);
lean_dec_ref(v_zs1_3055_);
return v___x_3070_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3139_, lean_object* v_a_3140_, lean_object* v___x_3141_, lean_object* v_zs1_3142_, lean_object* v_snd_3143_, lean_object* v___x_3144_, lean_object* v___x_3145_, lean_object* v___x_3146_, lean_object* v_alts_3147_, lean_object* v_zs2_3148_, lean_object* v___ctorRet2_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
uint8_t v___x_15152__boxed_3155_; uint8_t v___x_15153__boxed_3156_; uint8_t v___x_15154__boxed_3157_; lean_object* v_res_3158_; 
v___x_15152__boxed_3155_ = lean_unbox(v___x_3144_);
v___x_15153__boxed_3156_ = lean_unbox(v___x_3145_);
v___x_15154__boxed_3157_ = lean_unbox(v___x_3146_);
v_res_3158_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3139_, v_a_3140_, v___x_3141_, v_zs1_3142_, v_snd_3143_, v___x_15152__boxed_3155_, v___x_15153__boxed_3156_, v___x_15154__boxed_3157_, v_alts_3147_, v_zs2_3148_, v___ctorRet2_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec_ref(v___ctorRet2_3149_);
lean_dec_ref(v_zs2_3148_);
lean_dec_ref(v_alts_3147_);
lean_dec_ref(v_snd_3143_);
lean_dec(v___x_3141_);
lean_dec_ref(v_a_3140_);
lean_dec_ref(v___x_3139_);
return v_res_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3159_, lean_object* v_a_3160_, lean_object* v___x_3161_, lean_object* v_snd_3162_, uint8_t v___x_3163_, uint8_t v___x_3164_, uint8_t v___x_3165_, lean_object* v_alts_3166_, lean_object* v_a_3167_, lean_object* v_zs1_3168_, lean_object* v___ctorRet1_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; 
v___x_3175_ = lean_box(v___x_3163_);
v___x_3176_ = lean_box(v___x_3164_);
v___x_3177_ = lean_box(v___x_3165_);
v___f_3178_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3178_, 0, v___x_3159_);
lean_closure_set(v___f_3178_, 1, v_a_3160_);
lean_closure_set(v___f_3178_, 2, v___x_3161_);
lean_closure_set(v___f_3178_, 3, v_zs1_3168_);
lean_closure_set(v___f_3178_, 4, v_snd_3162_);
lean_closure_set(v___f_3178_, 5, v___x_3175_);
lean_closure_set(v___f_3178_, 6, v___x_3176_);
lean_closure_set(v___f_3178_, 7, v___x_3177_);
lean_closure_set(v___f_3178_, 8, v_alts_3166_);
v___x_3179_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3167_, v___f_3178_, v___x_3164_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3180_, lean_object* v_a_3181_, lean_object* v___x_3182_, lean_object* v_snd_3183_, lean_object* v___x_3184_, lean_object* v___x_3185_, lean_object* v___x_3186_, lean_object* v_alts_3187_, lean_object* v_a_3188_, lean_object* v_zs1_3189_, lean_object* v___ctorRet1_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
uint8_t v___x_15351__boxed_3196_; uint8_t v___x_15352__boxed_3197_; uint8_t v___x_15353__boxed_3198_; lean_object* v_res_3199_; 
v___x_15351__boxed_3196_ = lean_unbox(v___x_3184_);
v___x_15352__boxed_3197_ = lean_unbox(v___x_3185_);
v___x_15353__boxed_3198_ = lean_unbox(v___x_3186_);
v_res_3199_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3180_, v_a_3181_, v___x_3182_, v_snd_3183_, v___x_15351__boxed_3196_, v___x_15352__boxed_3197_, v___x_15353__boxed_3198_, v_alts_3187_, v_a_3188_, v_zs1_3189_, v___ctorRet1_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec_ref(v___ctorRet1_3190_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3200_, lean_object* v_params_3201_, lean_object* v_a_3202_, lean_object* v_snd_3203_, lean_object* v_alts_3204_, size_t v_sz_3205_, size_t v_i_3206_, lean_object* v_bs_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v___x_3213_; 
v___x_3213_ = lean_usize_dec_lt(v_i_3206_, v_sz_3205_);
if (v___x_3213_ == 0)
{
lean_object* v___x_3214_; 
lean_dec_ref(v_alts_3204_);
lean_dec_ref(v_snd_3203_);
lean_dec_ref(v_a_3202_);
lean_dec(v_tail_3200_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v_bs_3207_);
return v___x_3214_;
}
else
{
lean_object* v___x_3215_; uint8_t v___x_3216_; uint8_t v___x_3217_; lean_object* v_v_3218_; lean_object* v___x_3219_; lean_object* v_bs_x27_3220_; lean_object* v___y_3222_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3215_ = l_Lean_instInhabitedExpr;
v___x_3216_ = 0;
v___x_3217_ = 1;
v_v_3218_ = lean_array_uget(v_bs_3207_, v_i_3206_);
v___x_3219_ = lean_unsigned_to_nat(0u);
v_bs_x27_3220_ = lean_array_uset(v_bs_3207_, v_i_3206_, v___x_3219_);
v___x_3236_ = lean_usize_to_nat(v_i_3206_);
lean_inc(v_tail_3200_);
v___x_3237_ = l_Lean_mkConst(v_v_3218_, v_tail_3200_);
v___x_3238_ = l_Lean_mkAppN(v___x_3237_, v_params_3201_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
v___x_3239_ = lean_infer_type(v___x_3238_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___f_3244_; lean_object* v___x_3245_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc_n(v_a_3240_, 2);
lean_dec_ref_known(v___x_3239_, 1);
v___x_3241_ = lean_box(v___x_3213_);
v___x_3242_ = lean_box(v___x_3216_);
v___x_3243_ = lean_box(v___x_3217_);
lean_inc_ref(v_alts_3204_);
lean_inc_ref(v_snd_3203_);
lean_inc_ref(v_a_3202_);
v___f_3244_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3244_, 0, v___x_3215_);
lean_closure_set(v___f_3244_, 1, v_a_3202_);
lean_closure_set(v___f_3244_, 2, v___x_3236_);
lean_closure_set(v___f_3244_, 3, v_snd_3203_);
lean_closure_set(v___f_3244_, 4, v___x_3241_);
lean_closure_set(v___f_3244_, 5, v___x_3242_);
lean_closure_set(v___f_3244_, 6, v___x_3243_);
lean_closure_set(v___f_3244_, 7, v_alts_3204_);
lean_closure_set(v___f_3244_, 8, v_a_3240_);
v___x_3245_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3240_, v___f_3244_, v___x_3216_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
v___y_3222_ = v___x_3245_;
goto v___jp_3221_;
}
else
{
lean_dec(v___x_3236_);
v___y_3222_ = v___x_3239_;
goto v___jp_3221_;
}
v___jp_3221_:
{
if (lean_obj_tag(v___y_3222_) == 0)
{
lean_object* v_a_3223_; size_t v___x_3224_; size_t v___x_3225_; lean_object* v___x_3226_; 
v_a_3223_ = lean_ctor_get(v___y_3222_, 0);
lean_inc(v_a_3223_);
lean_dec_ref_known(v___y_3222_, 1);
v___x_3224_ = ((size_t)1ULL);
v___x_3225_ = lean_usize_add(v_i_3206_, v___x_3224_);
v___x_3226_ = lean_array_uset(v_bs_x27_3220_, v_i_3206_, v_a_3223_);
v_i_3206_ = v___x_3225_;
v_bs_3207_ = v___x_3226_;
goto _start;
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec_ref(v_bs_x27_3220_);
lean_dec_ref(v_alts_3204_);
lean_dec_ref(v_snd_3203_);
lean_dec_ref(v_a_3202_);
lean_dec(v_tail_3200_);
v_a_3228_ = lean_ctor_get(v___y_3222_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___y_3222_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___y_3222_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___y_3222_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3246_, lean_object* v_params_3247_, lean_object* v_a_3248_, lean_object* v_snd_3249_, lean_object* v_alts_3250_, lean_object* v_sz_3251_, lean_object* v_i_3252_, lean_object* v_bs_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
size_t v_sz_boxed_3259_; size_t v_i_boxed_3260_; lean_object* v_res_3261_; 
v_sz_boxed_3259_ = lean_unbox_usize(v_sz_3251_);
lean_dec(v_sz_3251_);
v_i_boxed_3260_ = lean_unbox_usize(v_i_3252_);
lean_dec(v_i_3252_);
v_res_3261_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3246_, v_params_3247_, v_a_3248_, v_snd_3249_, v_alts_3250_, v_sz_boxed_3259_, v_i_boxed_3260_, v_bs_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec_ref(v_params_3247_);
return v_res_3261_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3262_ = lean_box(0);
v___x_3263_ = lean_unsigned_to_nat(16u);
v___x_3264_ = lean_mk_array(v___x_3263_, v___x_3262_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3265_, lean_object* v___x_3266_, uint8_t v___x_3267_, uint8_t v___x_3268_, uint8_t v___x_3269_, lean_object* v_ism1_x27_3270_, lean_object* v_is_3271_, lean_object* v___x_3272_, lean_object* v___x_3273_, lean_object* v___x_3274_, lean_object* v___x_3275_, lean_object* v_params_3276_, lean_object* v___x_3277_, lean_object* v___x_3278_, lean_object* v_heq_3279_, lean_object* v_val_3280_, lean_object* v_tail_3281_, lean_object* v_alts_3282_, size_t v_sz_3283_, size_t v___x_3284_, lean_object* v___x_3285_, lean_object* v___x_3286_, lean_object* v_declName_3287_, lean_object* v_levelParams_3288_, lean_object* v_numIndices_3289_, lean_object* v___x_3290_, lean_object* v___x_3291_, lean_object* v_numParams_3292_, lean_object* v_snd_3293_, lean_object* v_ism2_x27_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___f_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v___x_3301_ = lean_box(v___x_3267_);
v___x_3302_ = lean_box(v___x_3268_);
v___x_3303_ = lean_box(v___x_3269_);
lean_inc_ref(v___x_3272_);
lean_inc_ref_n(v_is_3271_, 2);
lean_inc_ref(v_ism1_x27_3270_);
lean_inc_ref(v_motive_3265_);
v___f_3304_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3304_, 0, v_motive_3265_);
lean_closure_set(v___f_3304_, 1, v___x_3266_);
lean_closure_set(v___f_3304_, 2, v___x_3301_);
lean_closure_set(v___f_3304_, 3, v___x_3302_);
lean_closure_set(v___f_3304_, 4, v___x_3303_);
lean_closure_set(v___f_3304_, 5, v_ism1_x27_3270_);
lean_closure_set(v___f_3304_, 6, v_ism2_x27_3294_);
lean_closure_set(v___f_3304_, 7, v_is_3271_);
lean_closure_set(v___f_3304_, 8, v___x_3272_);
lean_inc_ref(v___x_3273_);
v___x_3305_ = lean_array_push(v_is_3271_, v___x_3273_);
v___x_3306_ = l_Lean_Meta_withNewEqs___redArg(v___x_3305_, v_ism1_x27_3270_, v___f_3304_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v_fst_3308_; lean_object* v_snd_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3410_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v_fst_3308_ = lean_ctor_get(v_a_3307_, 0);
v_snd_3309_ = lean_ctor_get(v_a_3307_, 1);
v_isSharedCheck_3410_ = !lean_is_exclusive(v_a_3307_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3311_ = v_a_3307_;
v_isShared_3312_ = v_isSharedCheck_3410_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_snd_3309_);
lean_inc(v_fst_3308_);
lean_dec(v_a_3307_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3410_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3313_ = l_Lean_mkConst(v___x_3274_, v___x_3275_);
v___x_3314_ = l_Lean_mkAppN(v___x_3313_, v_params_3276_);
v___x_3315_ = l_Lean_Expr_app___override(v___x_3314_, v_fst_3308_);
lean_inc_ref(v_is_3271_);
v___x_3316_ = l_Array_append___redArg(v_is_3271_, v___x_3277_);
v___x_3317_ = l_Array_append___redArg(v___x_3316_, v_is_3271_);
v___x_3318_ = l_Array_append___redArg(v___x_3317_, v___x_3278_);
v___x_3319_ = l_Lean_mkAppN(v___x_3315_, v___x_3318_);
lean_dec_ref(v___x_3318_);
lean_inc_ref(v_heq_3279_);
v___x_3320_ = l_Lean_Expr_app___override(v___x_3319_, v_heq_3279_);
v___x_3321_ = l_Lean_InductiveVal_numCtors(v_val_3280_);
lean_inc_ref(v___x_3320_);
v___x_3322_ = l_Lean_Meta_inferArgumentTypesN(v___x_3321_, v___x_3320_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3324_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref_known(v___x_3322_, 1);
lean_inc_ref(v_alts_3282_);
lean_inc(v_snd_3309_);
v___x_3324_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3281_, v_params_3276_, v_a_3323_, v_snd_3309_, v_alts_3282_, v_sz_3283_, v___x_3284_, v___x_3285_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3324_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
lean_inc(v_a_3325_);
lean_dec_ref_known(v___x_3324_, 1);
v___x_3326_ = l_Lean_mkAppN(v___x_3320_, v_a_3325_);
lean_dec(v_a_3325_);
v___x_3327_ = l_Lean_mkAppN(v___x_3326_, v_snd_3309_);
lean_dec(v_snd_3309_);
lean_inc_ref(v___x_3286_);
v___x_3328_ = lean_array_push(v___x_3286_, v_motive_3265_);
v___x_3329_ = l_Array_append___redArg(v_params_3276_, v___x_3328_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = l_Array_append___redArg(v___x_3329_, v_is_3271_);
lean_dec_ref(v_is_3271_);
v___x_3331_ = lean_unsigned_to_nat(2u);
v___x_3332_ = lean_mk_empty_array_with_capacity(v___x_3331_);
v___x_3333_ = lean_array_push(v___x_3332_, v___x_3273_);
v___x_3334_ = lean_array_push(v___x_3333_, v___x_3272_);
v___x_3335_ = l_Array_append___redArg(v___x_3330_, v___x_3334_);
lean_dec_ref(v___x_3334_);
v___x_3336_ = lean_array_push(v___x_3286_, v_heq_3279_);
v___x_3337_ = l_Array_append___redArg(v___x_3335_, v___x_3336_);
lean_dec_ref(v___x_3336_);
v___x_3338_ = l_Array_append___redArg(v___x_3337_, v_alts_3282_);
lean_dec_ref(v_alts_3282_);
v___x_3339_ = l_Lean_Meta_mkLambdaFVars(v___x_3338_, v___x_3327_, v___x_3267_, v___x_3268_, v___x_3267_, v___x_3268_, v___x_3269_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
lean_dec_ref(v___x_3338_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v_a_3340_; lean_object* v___x_3341_; 
v_a_3340_ = lean_ctor_get(v___x_3339_, 0);
lean_inc_n(v_a_3340_, 2);
lean_dec_ref_known(v___x_3339_, 1);
lean_inc(v___y_3299_);
lean_inc_ref(v___y_3298_);
lean_inc(v___y_3297_);
lean_inc_ref(v___y_3296_);
v___x_3341_ = lean_infer_type(v_a_3340_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3377_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3343_ = lean_box(1);
lean_inc(v_declName_3287_);
v___x_3344_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3287_, v_levelParams_3288_, v_a_3342_, v_a_3340_, v___x_3343_, v___y_3299_);
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3347_ = v___x_3344_;
v_isShared_3348_ = v_isSharedCheck_3377_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3344_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3377_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
lean_ctor_set_tag(v___x_3347_, 1);
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
lean_object* v___x_3351_; lean_object* v___f_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3351_ = lean_box(v___x_3267_);
lean_inc_ref(v___x_3350_);
v___f_3352_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3352_, 0, v___x_3350_);
lean_closure_set(v___f_3352_, 1, v___x_3351_);
v___x_3353_ = lean_nat_add(v_numIndices_3289_, v___x_3290_);
lean_inc(v___x_3291_);
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3291_);
v___x_3355_ = lean_box(0);
v___x_3356_ = lean_mk_empty_array_with_capacity(v___x_3290_);
v___x_3357_ = lean_array_push(v___x_3356_, v___x_3355_);
v___x_3358_ = lean_array_push(v___x_3357_, v___x_3355_);
v___x_3359_ = lean_array_push(v___x_3358_, v___x_3355_);
v___x_3360_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 1, v___x_3360_);
lean_ctor_set(v___x_3311_, 0, v___x_3291_);
v___x_3362_ = v___x_3311_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3291_);
lean_ctor_set(v_reuseFailAlloc_3375_, 1, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3363_; uint8_t v___y_3365_; uint8_t v___x_3374_; 
v___x_3363_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3363_, 0, v_numParams_3292_);
lean_ctor_set(v___x_3363_, 1, v___x_3353_);
lean_ctor_set(v___x_3363_, 2, v_snd_3293_);
lean_ctor_set(v___x_3363_, 3, v___x_3354_);
lean_ctor_set(v___x_3363_, 4, v___x_3359_);
lean_ctor_set(v___x_3363_, 5, v___x_3362_);
v___x_3374_ = l_Lean_isPrivateName(v_declName_3287_);
if (v___x_3374_ == 0)
{
v___y_3365_ = v___x_3268_;
goto v___jp_3364_;
}
else
{
v___y_3365_ = v___x_3267_;
goto v___jp_3364_;
}
v___jp_3364_:
{
lean_object* v___x_3366_; 
v___x_3366_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3352_, v___y_3365_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
lean_dec_ref_known(v___x_3366_, 1);
v___x_3367_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3287_);
v___x_3368_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3367_, v_declName_3287_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v___x_3369_; uint8_t v___x_3370_; lean_object* v___x_3371_; 
lean_dec_ref_known(v___x_3368_, 1);
lean_inc_n(v_declName_3287_, 2);
v___x_3369_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3287_, v___x_3363_, v___y_3297_, v___y_3299_);
lean_dec_ref(v___x_3369_);
v___x_3370_ = 0;
v___x_3371_ = l_Lean_Meta_setInlineAttribute(v_declName_3287_, v___x_3370_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3372_; 
lean_dec_ref_known(v___x_3371_, 1);
v___x_3372_ = l_Lean_enableRealizationsForConst(v_declName_3287_, v___y_3298_, v___y_3299_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v___x_3373_; 
lean_dec_ref_known(v___x_3372_, 1);
v___x_3373_ = l_Lean_compileDecl(v___x_3350_, v___x_3268_, v___y_3298_, v___y_3299_);
return v___x_3373_;
}
else
{
lean_dec_ref(v___x_3350_);
return v___x_3372_;
}
}
else
{
lean_dec_ref(v___x_3350_);
lean_dec(v_declName_3287_);
return v___x_3371_;
}
}
else
{
lean_dec_ref_known(v___x_3363_, 6);
lean_dec_ref(v___x_3350_);
lean_dec(v_declName_3287_);
return v___x_3368_;
}
}
else
{
lean_dec_ref_known(v___x_3363_, 6);
lean_dec_ref(v___x_3350_);
lean_dec(v_declName_3287_);
return v___x_3366_;
}
}
}
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_dec(v_a_3340_);
lean_del_object(v___x_3311_);
lean_dec_ref(v_snd_3293_);
lean_dec(v_numParams_3292_);
lean_dec(v___x_3291_);
lean_dec(v_levelParams_3288_);
lean_dec(v_declName_3287_);
v_a_3378_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3341_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3341_);
v___x_3380_ = lean_box(0);
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
v_resetjp_3379_:
{
lean_object* v___x_3383_; 
if (v_isShared_3381_ == 0)
{
v___x_3383_ = v___x_3380_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v_a_3378_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_del_object(v___x_3311_);
lean_dec_ref(v_snd_3293_);
lean_dec(v_numParams_3292_);
lean_dec(v___x_3291_);
lean_dec(v_levelParams_3288_);
lean_dec(v_declName_3287_);
v_a_3386_ = lean_ctor_get(v___x_3339_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3339_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3339_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3339_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3311_);
lean_dec(v_snd_3309_);
lean_dec_ref(v_snd_3293_);
lean_dec(v_numParams_3292_);
lean_dec(v___x_3291_);
lean_dec(v_levelParams_3288_);
lean_dec(v_declName_3287_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v_alts_3282_);
lean_dec_ref(v_heq_3279_);
lean_dec_ref(v_params_3276_);
lean_dec_ref(v___x_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_is_3271_);
lean_dec_ref(v_motive_3265_);
v_a_3394_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3324_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3324_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v___x_3320_);
lean_del_object(v___x_3311_);
lean_dec(v_snd_3309_);
lean_dec_ref(v_snd_3293_);
lean_dec(v_numParams_3292_);
lean_dec(v___x_3291_);
lean_dec(v_levelParams_3288_);
lean_dec(v_declName_3287_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_alts_3282_);
lean_dec(v_tail_3281_);
lean_dec_ref(v_heq_3279_);
lean_dec_ref(v_params_3276_);
lean_dec_ref(v___x_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_is_3271_);
lean_dec_ref(v_motive_3265_);
v_a_3402_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3322_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3322_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v_snd_3293_);
lean_dec(v_numParams_3292_);
lean_dec(v___x_3291_);
lean_dec(v_levelParams_3288_);
lean_dec(v_declName_3287_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_alts_3282_);
lean_dec(v_tail_3281_);
lean_dec_ref(v_heq_3279_);
lean_dec_ref(v_params_3276_);
lean_dec(v___x_3275_);
lean_dec(v___x_3274_);
lean_dec_ref(v___x_3273_);
lean_dec_ref(v___x_3272_);
lean_dec_ref(v_is_3271_);
lean_dec_ref(v_motive_3265_);
v_a_3411_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3306_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3306_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3419_ = _args[0];
lean_object* v___x_3420_ = _args[1];
lean_object* v___x_3421_ = _args[2];
lean_object* v___x_3422_ = _args[3];
lean_object* v___x_3423_ = _args[4];
lean_object* v_ism1_x27_3424_ = _args[5];
lean_object* v_is_3425_ = _args[6];
lean_object* v___x_3426_ = _args[7];
lean_object* v___x_3427_ = _args[8];
lean_object* v___x_3428_ = _args[9];
lean_object* v___x_3429_ = _args[10];
lean_object* v_params_3430_ = _args[11];
lean_object* v___x_3431_ = _args[12];
lean_object* v___x_3432_ = _args[13];
lean_object* v_heq_3433_ = _args[14];
lean_object* v_val_3434_ = _args[15];
lean_object* v_tail_3435_ = _args[16];
lean_object* v_alts_3436_ = _args[17];
lean_object* v_sz_3437_ = _args[18];
lean_object* v___x_3438_ = _args[19];
lean_object* v___x_3439_ = _args[20];
lean_object* v___x_3440_ = _args[21];
lean_object* v_declName_3441_ = _args[22];
lean_object* v_levelParams_3442_ = _args[23];
lean_object* v_numIndices_3443_ = _args[24];
lean_object* v___x_3444_ = _args[25];
lean_object* v___x_3445_ = _args[26];
lean_object* v_numParams_3446_ = _args[27];
lean_object* v_snd_3447_ = _args[28];
lean_object* v_ism2_x27_3448_ = _args[29];
lean_object* v_x_3449_ = _args[30];
lean_object* v___y_3450_ = _args[31];
lean_object* v___y_3451_ = _args[32];
lean_object* v___y_3452_ = _args[33];
lean_object* v___y_3453_ = _args[34];
lean_object* v___y_3454_ = _args[35];
_start:
{
uint8_t v___x_15490__boxed_3455_; uint8_t v___x_15491__boxed_3456_; uint8_t v___x_15492__boxed_3457_; size_t v_sz_boxed_3458_; size_t v___x_15501__boxed_3459_; lean_object* v_res_3460_; 
v___x_15490__boxed_3455_ = lean_unbox(v___x_3421_);
v___x_15491__boxed_3456_ = lean_unbox(v___x_3422_);
v___x_15492__boxed_3457_ = lean_unbox(v___x_3423_);
v_sz_boxed_3458_ = lean_unbox_usize(v_sz_3437_);
lean_dec(v_sz_3437_);
v___x_15501__boxed_3459_ = lean_unbox_usize(v___x_3438_);
lean_dec(v___x_3438_);
v_res_3460_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3419_, v___x_3420_, v___x_15490__boxed_3455_, v___x_15491__boxed_3456_, v___x_15492__boxed_3457_, v_ism1_x27_3424_, v_is_3425_, v___x_3426_, v___x_3427_, v___x_3428_, v___x_3429_, v_params_3430_, v___x_3431_, v___x_3432_, v_heq_3433_, v_val_3434_, v_tail_3435_, v_alts_3436_, v_sz_boxed_3458_, v___x_15501__boxed_3459_, v___x_3439_, v___x_3440_, v_declName_3441_, v_levelParams_3442_, v_numIndices_3443_, v___x_3444_, v___x_3445_, v_numParams_3446_, v_snd_3447_, v_ism2_x27_3448_, v_x_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v_x_3449_);
lean_dec(v___x_3444_);
lean_dec(v_numIndices_3443_);
lean_dec_ref(v_val_3434_);
lean_dec_ref(v___x_3432_);
lean_dec_ref(v___x_3431_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3461_, lean_object* v___x_3462_, uint8_t v___x_3463_, uint8_t v___x_3464_, uint8_t v___x_3465_, lean_object* v_is_3466_, lean_object* v___x_3467_, lean_object* v___x_3468_, lean_object* v___x_3469_, lean_object* v___x_3470_, lean_object* v_params_3471_, lean_object* v___x_3472_, lean_object* v___x_3473_, lean_object* v_heq_3474_, lean_object* v_val_3475_, lean_object* v_tail_3476_, lean_object* v_alts_3477_, size_t v_sz_3478_, size_t v___x_3479_, lean_object* v___x_3480_, lean_object* v___x_3481_, lean_object* v_declName_3482_, lean_object* v_levelParams_3483_, lean_object* v_numIndices_3484_, lean_object* v___x_3485_, lean_object* v___x_3486_, lean_object* v_numParams_3487_, lean_object* v_snd_3488_, lean_object* v___x_3489_, lean_object* v___x_3490_, lean_object* v_ism1_x27_3491_, lean_object* v_x_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___f_3503_; lean_object* v___x_3504_; 
v___x_3498_ = lean_box(v___x_3463_);
v___x_3499_ = lean_box(v___x_3464_);
v___x_3500_ = lean_box(v___x_3465_);
v___x_3501_ = lean_box_usize(v_sz_3478_);
v___x_3502_ = lean_box_usize(v___x_3479_);
v___f_3503_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3503_, 0, v_motive_3461_);
lean_closure_set(v___f_3503_, 1, v___x_3462_);
lean_closure_set(v___f_3503_, 2, v___x_3498_);
lean_closure_set(v___f_3503_, 3, v___x_3499_);
lean_closure_set(v___f_3503_, 4, v___x_3500_);
lean_closure_set(v___f_3503_, 5, v_ism1_x27_3491_);
lean_closure_set(v___f_3503_, 6, v_is_3466_);
lean_closure_set(v___f_3503_, 7, v___x_3467_);
lean_closure_set(v___f_3503_, 8, v___x_3468_);
lean_closure_set(v___f_3503_, 9, v___x_3469_);
lean_closure_set(v___f_3503_, 10, v___x_3470_);
lean_closure_set(v___f_3503_, 11, v_params_3471_);
lean_closure_set(v___f_3503_, 12, v___x_3472_);
lean_closure_set(v___f_3503_, 13, v___x_3473_);
lean_closure_set(v___f_3503_, 14, v_heq_3474_);
lean_closure_set(v___f_3503_, 15, v_val_3475_);
lean_closure_set(v___f_3503_, 16, v_tail_3476_);
lean_closure_set(v___f_3503_, 17, v_alts_3477_);
lean_closure_set(v___f_3503_, 18, v___x_3501_);
lean_closure_set(v___f_3503_, 19, v___x_3502_);
lean_closure_set(v___f_3503_, 20, v___x_3480_);
lean_closure_set(v___f_3503_, 21, v___x_3481_);
lean_closure_set(v___f_3503_, 22, v_declName_3482_);
lean_closure_set(v___f_3503_, 23, v_levelParams_3483_);
lean_closure_set(v___f_3503_, 24, v_numIndices_3484_);
lean_closure_set(v___f_3503_, 25, v___x_3485_);
lean_closure_set(v___f_3503_, 26, v___x_3486_);
lean_closure_set(v___f_3503_, 27, v_numParams_3487_);
lean_closure_set(v___f_3503_, 28, v_snd_3488_);
v___x_3504_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3489_, v___x_3490_, v___f_3503_, v___x_3463_, v___x_3463_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3505_ = _args[0];
lean_object* v___x_3506_ = _args[1];
lean_object* v___x_3507_ = _args[2];
lean_object* v___x_3508_ = _args[3];
lean_object* v___x_3509_ = _args[4];
lean_object* v_is_3510_ = _args[5];
lean_object* v___x_3511_ = _args[6];
lean_object* v___x_3512_ = _args[7];
lean_object* v___x_3513_ = _args[8];
lean_object* v___x_3514_ = _args[9];
lean_object* v_params_3515_ = _args[10];
lean_object* v___x_3516_ = _args[11];
lean_object* v___x_3517_ = _args[12];
lean_object* v_heq_3518_ = _args[13];
lean_object* v_val_3519_ = _args[14];
lean_object* v_tail_3520_ = _args[15];
lean_object* v_alts_3521_ = _args[16];
lean_object* v_sz_3522_ = _args[17];
lean_object* v___x_3523_ = _args[18];
lean_object* v___x_3524_ = _args[19];
lean_object* v___x_3525_ = _args[20];
lean_object* v_declName_3526_ = _args[21];
lean_object* v_levelParams_3527_ = _args[22];
lean_object* v_numIndices_3528_ = _args[23];
lean_object* v___x_3529_ = _args[24];
lean_object* v___x_3530_ = _args[25];
lean_object* v_numParams_3531_ = _args[26];
lean_object* v_snd_3532_ = _args[27];
lean_object* v___x_3533_ = _args[28];
lean_object* v___x_3534_ = _args[29];
lean_object* v_ism1_x27_3535_ = _args[30];
lean_object* v_x_3536_ = _args[31];
lean_object* v___y_3537_ = _args[32];
lean_object* v___y_3538_ = _args[33];
lean_object* v___y_3539_ = _args[34];
lean_object* v___y_3540_ = _args[35];
lean_object* v___y_3541_ = _args[36];
_start:
{
uint8_t v___x_15812__boxed_3542_; uint8_t v___x_15813__boxed_3543_; uint8_t v___x_15814__boxed_3544_; size_t v_sz_boxed_3545_; size_t v___x_15823__boxed_3546_; lean_object* v_res_3547_; 
v___x_15812__boxed_3542_ = lean_unbox(v___x_3507_);
v___x_15813__boxed_3543_ = lean_unbox(v___x_3508_);
v___x_15814__boxed_3544_ = lean_unbox(v___x_3509_);
v_sz_boxed_3545_ = lean_unbox_usize(v_sz_3522_);
lean_dec(v_sz_3522_);
v___x_15823__boxed_3546_ = lean_unbox_usize(v___x_3523_);
lean_dec(v___x_3523_);
v_res_3547_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3505_, v___x_3506_, v___x_15812__boxed_3542_, v___x_15813__boxed_3543_, v___x_15814__boxed_3544_, v_is_3510_, v___x_3511_, v___x_3512_, v___x_3513_, v___x_3514_, v_params_3515_, v___x_3516_, v___x_3517_, v_heq_3518_, v_val_3519_, v_tail_3520_, v_alts_3521_, v_sz_boxed_3545_, v___x_15823__boxed_3546_, v___x_3524_, v___x_3525_, v_declName_3526_, v_levelParams_3527_, v_numIndices_3528_, v___x_3529_, v___x_3530_, v_numParams_3531_, v_snd_3532_, v___x_3533_, v___x_3534_, v_ism1_x27_3535_, v_x_3536_, v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec_ref(v_x_3536_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3548_, lean_object* v___x_3549_, lean_object* v_motive_3550_, lean_object* v___x_3551_, uint8_t v___x_3552_, uint8_t v___x_3553_, uint8_t v___x_3554_, lean_object* v_is_3555_, lean_object* v___x_3556_, lean_object* v___x_3557_, lean_object* v___x_3558_, lean_object* v___x_3559_, lean_object* v_params_3560_, lean_object* v___x_3561_, lean_object* v___x_3562_, lean_object* v_heq_3563_, lean_object* v_val_3564_, lean_object* v_tail_3565_, size_t v_sz_3566_, size_t v___x_3567_, lean_object* v___x_3568_, lean_object* v___x_3569_, lean_object* v_declName_3570_, lean_object* v_levelParams_3571_, lean_object* v___x_3572_, lean_object* v___x_3573_, lean_object* v_numParams_3574_, lean_object* v_snd_3575_, lean_object* v___x_3576_, lean_object* v_alts_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_){
_start:
{
lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___f_3590_; lean_object* v___x_3591_; 
v___x_3583_ = lean_nat_add(v_numIndices_3548_, v___x_3549_);
v___x_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
v___x_3585_ = lean_box(v___x_3552_);
v___x_3586_ = lean_box(v___x_3553_);
v___x_3587_ = lean_box(v___x_3554_);
v___x_3588_ = lean_box_usize(v_sz_3566_);
v___x_3589_ = lean_box_usize(v___x_3567_);
lean_inc_ref(v___x_3584_);
lean_inc_ref(v___x_3576_);
v___f_3590_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3590_, 0, v_motive_3550_);
lean_closure_set(v___f_3590_, 1, v___x_3551_);
lean_closure_set(v___f_3590_, 2, v___x_3585_);
lean_closure_set(v___f_3590_, 3, v___x_3586_);
lean_closure_set(v___f_3590_, 4, v___x_3587_);
lean_closure_set(v___f_3590_, 5, v_is_3555_);
lean_closure_set(v___f_3590_, 6, v___x_3556_);
lean_closure_set(v___f_3590_, 7, v___x_3557_);
lean_closure_set(v___f_3590_, 8, v___x_3558_);
lean_closure_set(v___f_3590_, 9, v___x_3559_);
lean_closure_set(v___f_3590_, 10, v_params_3560_);
lean_closure_set(v___f_3590_, 11, v___x_3561_);
lean_closure_set(v___f_3590_, 12, v___x_3562_);
lean_closure_set(v___f_3590_, 13, v_heq_3563_);
lean_closure_set(v___f_3590_, 14, v_val_3564_);
lean_closure_set(v___f_3590_, 15, v_tail_3565_);
lean_closure_set(v___f_3590_, 16, v_alts_3577_);
lean_closure_set(v___f_3590_, 17, v___x_3588_);
lean_closure_set(v___f_3590_, 18, v___x_3589_);
lean_closure_set(v___f_3590_, 19, v___x_3568_);
lean_closure_set(v___f_3590_, 20, v___x_3569_);
lean_closure_set(v___f_3590_, 21, v_declName_3570_);
lean_closure_set(v___f_3590_, 22, v_levelParams_3571_);
lean_closure_set(v___f_3590_, 23, v_numIndices_3548_);
lean_closure_set(v___f_3590_, 24, v___x_3572_);
lean_closure_set(v___f_3590_, 25, v___x_3573_);
lean_closure_set(v___f_3590_, 26, v_numParams_3574_);
lean_closure_set(v___f_3590_, 27, v_snd_3575_);
lean_closure_set(v___f_3590_, 28, v___x_3576_);
lean_closure_set(v___f_3590_, 29, v___x_3584_);
v___x_3591_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3576_, v___x_3584_, v___f_3590_, v___x_3552_, v___x_3552_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3592_ = _args[0];
lean_object* v___x_3593_ = _args[1];
lean_object* v_motive_3594_ = _args[2];
lean_object* v___x_3595_ = _args[3];
lean_object* v___x_3596_ = _args[4];
lean_object* v___x_3597_ = _args[5];
lean_object* v___x_3598_ = _args[6];
lean_object* v_is_3599_ = _args[7];
lean_object* v___x_3600_ = _args[8];
lean_object* v___x_3601_ = _args[9];
lean_object* v___x_3602_ = _args[10];
lean_object* v___x_3603_ = _args[11];
lean_object* v_params_3604_ = _args[12];
lean_object* v___x_3605_ = _args[13];
lean_object* v___x_3606_ = _args[14];
lean_object* v_heq_3607_ = _args[15];
lean_object* v_val_3608_ = _args[16];
lean_object* v_tail_3609_ = _args[17];
lean_object* v_sz_3610_ = _args[18];
lean_object* v___x_3611_ = _args[19];
lean_object* v___x_3612_ = _args[20];
lean_object* v___x_3613_ = _args[21];
lean_object* v_declName_3614_ = _args[22];
lean_object* v_levelParams_3615_ = _args[23];
lean_object* v___x_3616_ = _args[24];
lean_object* v___x_3617_ = _args[25];
lean_object* v_numParams_3618_ = _args[26];
lean_object* v_snd_3619_ = _args[27];
lean_object* v___x_3620_ = _args[28];
lean_object* v_alts_3621_ = _args[29];
lean_object* v___y_3622_ = _args[30];
lean_object* v___y_3623_ = _args[31];
lean_object* v___y_3624_ = _args[32];
lean_object* v___y_3625_ = _args[33];
lean_object* v___y_3626_ = _args[34];
_start:
{
uint8_t v___x_15905__boxed_3627_; uint8_t v___x_15906__boxed_3628_; uint8_t v___x_15907__boxed_3629_; size_t v_sz_boxed_3630_; size_t v___x_15916__boxed_3631_; lean_object* v_res_3632_; 
v___x_15905__boxed_3627_ = lean_unbox(v___x_3596_);
v___x_15906__boxed_3628_ = lean_unbox(v___x_3597_);
v___x_15907__boxed_3629_ = lean_unbox(v___x_3598_);
v_sz_boxed_3630_ = lean_unbox_usize(v_sz_3610_);
lean_dec(v_sz_3610_);
v___x_15916__boxed_3631_ = lean_unbox_usize(v___x_3611_);
lean_dec(v___x_3611_);
v_res_3632_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3592_, v___x_3593_, v_motive_3594_, v___x_3595_, v___x_15905__boxed_3627_, v___x_15906__boxed_3628_, v___x_15907__boxed_3629_, v_is_3599_, v___x_3600_, v___x_3601_, v___x_3602_, v___x_3603_, v_params_3604_, v___x_3605_, v___x_3606_, v_heq_3607_, v_val_3608_, v_tail_3609_, v_sz_boxed_3630_, v___x_15916__boxed_3631_, v___x_3612_, v___x_3613_, v_declName_3614_, v_levelParams_3615_, v___x_3616_, v___x_3617_, v_numParams_3618_, v_snd_3619_, v___x_3620_, v_alts_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
lean_dec(v___x_3593_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3633_, lean_object* v_declInfos_3634_, lean_object* v_k_3635_, lean_object* v_kind_3636_, lean_object* v_x_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
uint8_t v_kind_boxed_3643_; lean_object* v_res_3644_; 
v_kind_boxed_3643_ = lean_unbox(v_kind_3636_);
v_res_3644_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3633_, v_declInfos_3634_, v_k_3635_, v_kind_boxed_3643_, v_x_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3645_, lean_object* v_k_3646_, uint8_t v_kind_3647_, lean_object* v_acc_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
lean_object* v___x_3654_; lean_object* v_toApplicative_3655_; lean_object* v_toFunctor_3656_; lean_object* v_toSeq_3657_; lean_object* v_toSeqLeft_3658_; lean_object* v_toSeqRight_3659_; lean_object* v___f_3660_; lean_object* v___f_3661_; lean_object* v___f_3662_; lean_object* v___f_3663_; lean_object* v___x_3664_; lean_object* v___f_3665_; lean_object* v___f_3666_; lean_object* v___f_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v_toApplicative_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3729_; 
v___x_3654_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3655_ = lean_ctor_get(v___x_3654_, 0);
v_toFunctor_3656_ = lean_ctor_get(v_toApplicative_3655_, 0);
v_toSeq_3657_ = lean_ctor_get(v_toApplicative_3655_, 2);
v_toSeqLeft_3658_ = lean_ctor_get(v_toApplicative_3655_, 3);
v_toSeqRight_3659_ = lean_ctor_get(v_toApplicative_3655_, 4);
v___f_3660_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3661_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3656_, 2);
v___f_3662_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3662_, 0, v_toFunctor_3656_);
v___f_3663_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3663_, 0, v_toFunctor_3656_);
v___x_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3664_, 0, v___f_3662_);
lean_ctor_set(v___x_3664_, 1, v___f_3663_);
lean_inc(v_toSeqRight_3659_);
v___f_3665_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3665_, 0, v_toSeqRight_3659_);
lean_inc(v_toSeqLeft_3658_);
v___f_3666_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3666_, 0, v_toSeqLeft_3658_);
lean_inc(v_toSeq_3657_);
v___f_3667_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3667_, 0, v_toSeq_3657_);
v___x_3668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3664_);
lean_ctor_set(v___x_3668_, 1, v___f_3660_);
lean_ctor_set(v___x_3668_, 2, v___f_3667_);
lean_ctor_set(v___x_3668_, 3, v___f_3666_);
lean_ctor_set(v___x_3668_, 4, v___f_3665_);
v___x_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
lean_ctor_set(v___x_3669_, 1, v___f_3661_);
v___x_3670_ = l_StateRefT_x27_instMonad___redArg(v___x_3669_);
v_toApplicative_3671_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v___x_3670_, 1);
lean_dec(v_unused_3730_);
v___x_3673_ = v___x_3670_;
v_isShared_3674_ = v_isSharedCheck_3729_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_toApplicative_3671_);
lean_dec(v___x_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3729_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v_toFunctor_3675_; lean_object* v_toSeq_3676_; lean_object* v_toSeqLeft_3677_; lean_object* v_toSeqRight_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3727_; 
v_toFunctor_3675_ = lean_ctor_get(v_toApplicative_3671_, 0);
v_toSeq_3676_ = lean_ctor_get(v_toApplicative_3671_, 2);
v_toSeqLeft_3677_ = lean_ctor_get(v_toApplicative_3671_, 3);
v_toSeqRight_3678_ = lean_ctor_get(v_toApplicative_3671_, 4);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_toApplicative_3671_);
if (v_isSharedCheck_3727_ == 0)
{
lean_object* v_unused_3728_; 
v_unused_3728_ = lean_ctor_get(v_toApplicative_3671_, 1);
lean_dec(v_unused_3728_);
v___x_3680_ = v_toApplicative_3671_;
v_isShared_3681_ = v_isSharedCheck_3727_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_toSeqRight_3678_);
lean_inc(v_toSeqLeft_3677_);
lean_inc(v_toSeq_3676_);
lean_inc(v_toFunctor_3675_);
lean_dec(v_toApplicative_3671_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3727_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___f_3682_; lean_object* v___f_3683_; lean_object* v___f_3684_; lean_object* v___f_3685_; lean_object* v___x_3686_; lean_object* v___f_3687_; lean_object* v___f_3688_; lean_object* v___f_3689_; lean_object* v___x_3691_; 
v___f_3682_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3683_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3675_);
v___f_3684_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3684_, 0, v_toFunctor_3675_);
v___f_3685_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3685_, 0, v_toFunctor_3675_);
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___f_3684_);
lean_ctor_set(v___x_3686_, 1, v___f_3685_);
v___f_3687_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3687_, 0, v_toSeqRight_3678_);
v___f_3688_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3688_, 0, v_toSeqLeft_3677_);
v___f_3689_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3689_, 0, v_toSeq_3676_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 4, v___f_3687_);
lean_ctor_set(v___x_3680_, 3, v___f_3688_);
lean_ctor_set(v___x_3680_, 2, v___f_3689_);
lean_ctor_set(v___x_3680_, 1, v___f_3682_);
lean_ctor_set(v___x_3680_, 0, v___x_3686_);
v___x_3691_ = v___x_3680_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3686_);
lean_ctor_set(v_reuseFailAlloc_3726_, 1, v___f_3682_);
lean_ctor_set(v_reuseFailAlloc_3726_, 2, v___f_3689_);
lean_ctor_set(v_reuseFailAlloc_3726_, 3, v___f_3688_);
lean_ctor_set(v_reuseFailAlloc_3726_, 4, v___f_3687_);
v___x_3691_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3693_; 
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 1, v___f_3683_);
lean_ctor_set(v___x_3673_, 0, v___x_3691_);
v___x_3693_ = v___x_3673_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3691_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___f_3683_);
v___x_3693_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; uint8_t v___x_3696_; 
v___x_3694_ = lean_array_get_size(v_acc_3648_);
v___x_3695_ = lean_array_get_size(v_declInfos_3645_);
v___x_3696_ = lean_nat_dec_lt(v___x_3694_, v___x_3695_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; 
lean_dec_ref(v___x_3693_);
lean_dec_ref(v_declInfos_3645_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3651_);
lean_inc(v___y_3650_);
lean_inc_ref(v___y_3649_);
v___x_3697_ = lean_apply_6(v_k_3646_, v_acc_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, lean_box(0));
return v___x_3697_;
}
else
{
lean_object* v___x_3698_; uint8_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v_snd_3707_; lean_object* v_fst_3708_; lean_object* v_fst_3709_; lean_object* v_snd_3710_; lean_object* v___x_3711_; lean_object* v___f_3712_; lean_object* v___x_3713_; 
v___x_3698_ = lean_box(0);
v___x_3699_ = 0;
v___x_3700_ = l_Lean_instInhabitedExpr;
v___f_3701_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3701_, 0, v___x_3693_);
lean_closure_set(v___f_3701_, 1, v___x_3700_);
v___f_3702_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3702_, 0, v___f_3701_);
v___x_3703_ = lean_box(v___x_3699_);
v___x_3704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
lean_ctor_set(v___x_3704_, 1, v___f_3702_);
v___x_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3698_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = lean_array_get(v___x_3705_, v_declInfos_3645_, v___x_3694_);
lean_dec_ref_known(v___x_3705_, 2);
v_snd_3707_ = lean_ctor_get(v___x_3706_, 1);
lean_inc(v_snd_3707_);
v_fst_3708_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_fst_3708_);
lean_dec(v___x_3706_);
v_fst_3709_ = lean_ctor_get(v_snd_3707_, 0);
lean_inc(v_fst_3709_);
v_snd_3710_ = lean_ctor_get(v_snd_3707_, 1);
lean_inc(v_snd_3710_);
lean_dec(v_snd_3707_);
v___x_3711_ = lean_box(v_kind_3647_);
lean_inc_ref(v_acc_3648_);
v___f_3712_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3712_, 0, v_acc_3648_);
lean_closure_set(v___f_3712_, 1, v_declInfos_3645_);
lean_closure_set(v___f_3712_, 2, v_k_3646_);
lean_closure_set(v___f_3712_, 3, v___x_3711_);
lean_inc(v___y_3652_);
lean_inc_ref(v___y_3651_);
lean_inc(v___y_3650_);
lean_inc_ref(v___y_3649_);
v___x_3713_ = lean_apply_6(v_snd_3710_, v_acc_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, lean_box(0));
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; uint8_t v___x_3715_; lean_object* v___x_3716_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v___x_3715_ = lean_unbox(v_fst_3709_);
lean_dec(v_fst_3709_);
v___x_3716_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3708_, v___x_3715_, v_a_3714_, v___f_3712_, v_kind_3647_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
return v___x_3716_;
}
else
{
lean_object* v_a_3717_; lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3724_; 
lean_dec_ref(v___f_3712_);
lean_dec(v_fst_3709_);
lean_dec(v_fst_3708_);
v_a_3717_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3724_ == 0)
{
v___x_3719_ = v___x_3713_;
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
else
{
lean_inc(v_a_3717_);
lean_dec(v___x_3713_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3724_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
lean_object* v___x_3722_; 
if (v_isShared_3720_ == 0)
{
v___x_3722_ = v___x_3719_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_a_3717_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3731_, lean_object* v_declInfos_3732_, lean_object* v_k_3733_, uint8_t v_kind_3734_, lean_object* v_x_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = lean_array_push(v_acc_3731_, v_x_3735_);
v___x_3742_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3732_, v_k_3733_, v_kind_3734_, v___x_3741_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3743_, lean_object* v_k_3744_, lean_object* v_kind_3745_, lean_object* v_acc_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
uint8_t v_kind_boxed_3752_; lean_object* v_res_3753_; 
v_kind_boxed_3752_ = lean_unbox(v_kind_3745_);
v_res_3753_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3743_, v_k_3744_, v_kind_boxed_3752_, v_acc_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3754_, lean_object* v_k_3755_, uint8_t v_kind_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3762_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3763_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3754_, v_k_3755_, v_kind_3756_, v___x_3762_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3764_, lean_object* v_k_3765_, lean_object* v_kind_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
uint8_t v_kind_boxed_3772_; lean_object* v_res_3773_; 
v_kind_boxed_3772_ = lean_unbox(v_kind_3766_);
v_res_3773_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3764_, v_k_3765_, v_kind_boxed_3772_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
lean_dec(v___y_3770_);
lean_dec_ref(v___y_3769_);
lean_dec(v___y_3768_);
lean_dec_ref(v___y_3767_);
return v_res_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3774_, lean_object* v_k_3775_, uint8_t v_kind_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
size_t v_sz_3782_; size_t v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; 
v_sz_3782_ = lean_array_size(v_declInfos_3774_);
v___x_3783_ = ((size_t)0ULL);
v___x_3784_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3782_, v___x_3783_, v_declInfos_3774_);
v___x_3785_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3784_, v_k_3775_, v_kind_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
return v___x_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3786_, lean_object* v_k_3787_, lean_object* v_kind_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
uint8_t v_kind_boxed_3794_; lean_object* v_res_3795_; 
v_kind_boxed_3794_ = lean_unbox(v_kind_3788_);
v_res_3795_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3786_, v_k_3787_, v_kind_boxed_3794_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3796_, lean_object* v_k_3797_, uint8_t v_kind_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
size_t v_sz_3804_; size_t v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v_sz_3804_ = lean_array_size(v_declInfos_3796_);
v___x_3805_ = ((size_t)0ULL);
v___x_3806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3804_, v___x_3805_, v_declInfos_3796_);
v___x_3807_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3806_, v_k_3797_, v_kind_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3808_, lean_object* v_k_3809_, lean_object* v_kind_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
uint8_t v_kind_boxed_3816_; lean_object* v_res_3817_; 
v_kind_boxed_3816_ = lean_unbox(v_kind_3810_);
v_res_3817_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3808_, v_k_3809_, v_kind_boxed_3816_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
return v_res_3817_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3820_ = lean_box(0);
v___x_3821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3822_ = l_Lean_mkConst(v___x_3821_, v___x_3820_);
return v___x_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3823_, lean_object* v_v_3824_, lean_object* v___x_3825_, lean_object* v___x_3826_, lean_object* v___x_3827_, lean_object* v_motive_3828_, uint8_t v___x_3829_, uint8_t v___x_3830_, uint8_t v___x_3831_, lean_object* v_zs12_3832_, lean_object* v_is_3833_, lean_object* v_fields1_3834_, lean_object* v_fields2_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v_e_3851_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
lean_inc_ref(v___x_3827_);
v___x_3861_ = l_Lean_mkAppN(v___x_3827_, v_fields1_3834_);
v___x_3862_ = l_Lean_mkAppN(v___x_3827_, v_fields2_3835_);
lean_inc(v___x_3825_);
v___x_3863_ = l_Lean_mkNatLit(v___x_3825_);
v___x_3864_ = l_Lean_Meta_mkEqRefl(v___x_3863_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v___x_3866_ = lean_unsigned_to_nat(3u);
v___x_3867_ = lean_mk_empty_array_with_capacity(v___x_3866_);
v___x_3868_ = lean_array_push(v___x_3867_, v___x_3861_);
v___x_3869_ = lean_array_push(v___x_3868_, v___x_3862_);
v___x_3870_ = lean_array_push(v___x_3869_, v_a_3865_);
v___x_3871_ = l_Array_append___redArg(v_is_3833_, v___x_3870_);
lean_dec_ref(v___x_3870_);
v___x_3872_ = l_Lean_mkAppN(v_motive_3828_, v___x_3871_);
lean_dec_ref(v___x_3871_);
v___x_3873_ = l_Lean_Meta_mkForallFVars(v_zs12_3832_, v___x_3872_, v___x_3829_, v___x_3830_, v___x_3830_, v___x_3831_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v___x_3875_ = lean_array_get_size(v_zs12_3832_);
v___x_3876_ = lean_nat_dec_eq(v___x_3875_, v___x_3823_);
if (v___x_3876_ == 0)
{
v_e_3851_ = v_a_3874_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3878_ = l_Lean_mkArrow(v___x_3877_, v_a_3874_, v___y_3838_, v___y_3839_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_a_3879_);
lean_dec_ref_known(v___x_3878_, 1);
v_e_3851_ = v_a_3879_;
goto v___jp_3850_;
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v___x_3825_);
lean_dec(v_v_3824_);
lean_dec(v___x_3823_);
v_a_3880_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3878_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3878_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec(v___x_3825_);
lean_dec(v_v_3824_);
lean_dec(v___x_3823_);
v_a_3888_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3873_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3873_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec_ref(v___x_3862_);
lean_dec_ref(v___x_3861_);
lean_dec_ref(v_is_3833_);
lean_dec_ref(v_motive_3828_);
lean_dec(v___x_3825_);
lean_dec(v_v_3824_);
lean_dec(v___x_3823_);
v_a_3896_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3864_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3864_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
v___jp_3841_:
{
lean_object* v___x_3844_; uint8_t v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3844_ = lean_array_get_size(v_zs12_3832_);
v___x_3845_ = lean_nat_dec_eq(v___x_3844_, v___x_3823_);
v___x_3846_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3846_, 0, v___x_3844_);
lean_ctor_set(v___x_3846_, 1, v___x_3823_);
lean_ctor_set_uint8(v___x_3846_, sizeof(void*)*2, v___x_3845_);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___y_3843_);
lean_ctor_set(v___x_3847_, 1, v___y_3842_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
lean_ctor_set(v___x_3848_, 1, v___x_3846_);
v___x_3849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
return v___x_3849_;
}
v___jp_3850_:
{
if (lean_obj_tag(v_v_3824_) == 1)
{
lean_object* v_str_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
lean_dec(v___x_3825_);
v_str_3852_ = lean_ctor_get(v_v_3824_, 1);
lean_inc_ref(v_str_3852_);
lean_dec_ref_known(v_v_3824_, 2);
v___x_3853_ = lean_box(0);
v___x_3854_ = l_Lean_Name_str___override(v___x_3853_, v_str_3852_);
v___y_3842_ = v_e_3851_;
v___y_3843_ = v___x_3854_;
goto v___jp_3841_;
}
else
{
lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
lean_dec(v_v_3824_);
v___x_3855_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3856_ = lean_nat_add(v___x_3825_, v___x_3826_);
lean_dec(v___x_3825_);
v___x_3857_ = l_Nat_reprFast(v___x_3856_);
v___x_3858_ = lean_string_append(v___x_3855_, v___x_3857_);
lean_dec_ref(v___x_3857_);
v___x_3859_ = lean_box(0);
v___x_3860_ = l_Lean_Name_str___override(v___x_3859_, v___x_3858_);
v___y_3842_ = v_e_3851_;
v___y_3843_ = v___x_3860_;
goto v___jp_3841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3904_ = _args[0];
lean_object* v_v_3905_ = _args[1];
lean_object* v___x_3906_ = _args[2];
lean_object* v___x_3907_ = _args[3];
lean_object* v___x_3908_ = _args[4];
lean_object* v_motive_3909_ = _args[5];
lean_object* v___x_3910_ = _args[6];
lean_object* v___x_3911_ = _args[7];
lean_object* v___x_3912_ = _args[8];
lean_object* v_zs12_3913_ = _args[9];
lean_object* v_is_3914_ = _args[10];
lean_object* v_fields1_3915_ = _args[11];
lean_object* v_fields2_3916_ = _args[12];
lean_object* v___y_3917_ = _args[13];
lean_object* v___y_3918_ = _args[14];
lean_object* v___y_3919_ = _args[15];
lean_object* v___y_3920_ = _args[16];
lean_object* v___y_3921_ = _args[17];
_start:
{
uint8_t v___x_16252__boxed_3922_; uint8_t v___x_16253__boxed_3923_; uint8_t v___x_16254__boxed_3924_; lean_object* v_res_3925_; 
v___x_16252__boxed_3922_ = lean_unbox(v___x_3910_);
v___x_16253__boxed_3923_ = lean_unbox(v___x_3911_);
v___x_16254__boxed_3924_ = lean_unbox(v___x_3912_);
v_res_3925_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3904_, v_v_3905_, v___x_3906_, v___x_3907_, v___x_3908_, v_motive_3909_, v___x_16252__boxed_3922_, v___x_16253__boxed_3923_, v___x_16254__boxed_3924_, v_zs12_3913_, v_is_3914_, v_fields1_3915_, v_fields2_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
lean_dec(v___y_3920_);
lean_dec_ref(v___y_3919_);
lean_dec(v___y_3918_);
lean_dec_ref(v___y_3917_);
lean_dec_ref(v_fields2_3916_);
lean_dec_ref(v_fields1_3915_);
lean_dec_ref(v_zs12_3913_);
lean_dec(v___x_3907_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3926_, lean_object* v_params_3927_, lean_object* v_motive_3928_, size_t v_sz_3929_, size_t v_i_3930_, lean_object* v_bs_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_){
_start:
{
uint8_t v___x_3937_; 
v___x_3937_ = lean_usize_dec_lt(v_i_3930_, v_sz_3929_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; 
lean_dec_ref(v_motive_3928_);
lean_dec(v_tail_3926_);
v___x_3938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3938_, 0, v_bs_3931_);
return v___x_3938_;
}
else
{
lean_object* v___x_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; uint8_t v___x_3942_; lean_object* v_v_3943_; lean_object* v_bs_x27_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___f_3951_; lean_object* v___x_3952_; 
v___x_3939_ = lean_unsigned_to_nat(0u);
v___x_3940_ = lean_unsigned_to_nat(1u);
v___x_3941_ = 0;
v___x_3942_ = 1;
v_v_3943_ = lean_array_uget(v_bs_3931_, v_i_3930_);
v_bs_x27_3944_ = lean_array_uset(v_bs_3931_, v_i_3930_, v___x_3939_);
v___x_3945_ = lean_usize_to_nat(v_i_3930_);
lean_inc(v_tail_3926_);
lean_inc(v_v_3943_);
v___x_3946_ = l_Lean_mkConst(v_v_3943_, v_tail_3926_);
v___x_3947_ = l_Lean_mkAppN(v___x_3946_, v_params_3927_);
v___x_3948_ = lean_box(v___x_3941_);
v___x_3949_ = lean_box(v___x_3937_);
v___x_3950_ = lean_box(v___x_3942_);
lean_inc_ref(v_motive_3928_);
lean_inc_ref(v___x_3947_);
v___f_3951_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3951_, 0, v___x_3939_);
lean_closure_set(v___f_3951_, 1, v_v_3943_);
lean_closure_set(v___f_3951_, 2, v___x_3945_);
lean_closure_set(v___f_3951_, 3, v___x_3940_);
lean_closure_set(v___f_3951_, 4, v___x_3947_);
lean_closure_set(v___f_3951_, 5, v_motive_3928_);
lean_closure_set(v___f_3951_, 6, v___x_3948_);
lean_closure_set(v___f_3951_, 7, v___x_3949_);
lean_closure_set(v___f_3951_, 8, v___x_3950_);
v___x_3952_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3947_, v___f_3951_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v_a_3953_; size_t v___x_3954_; size_t v___x_3955_; lean_object* v___x_3956_; 
v_a_3953_ = lean_ctor_get(v___x_3952_, 0);
lean_inc(v_a_3953_);
lean_dec_ref_known(v___x_3952_, 1);
v___x_3954_ = ((size_t)1ULL);
v___x_3955_ = lean_usize_add(v_i_3930_, v___x_3954_);
v___x_3956_ = lean_array_uset(v_bs_x27_3944_, v_i_3930_, v_a_3953_);
v_i_3930_ = v___x_3955_;
v_bs_3931_ = v___x_3956_;
goto _start;
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec_ref(v_bs_x27_3944_);
lean_dec_ref(v_motive_3928_);
lean_dec(v_tail_3926_);
v_a_3958_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3952_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3952_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3966_, lean_object* v_params_3967_, lean_object* v_motive_3968_, lean_object* v_sz_3969_, lean_object* v_i_3970_, lean_object* v_bs_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
size_t v_sz_boxed_3977_; size_t v_i_boxed_3978_; lean_object* v_res_3979_; 
v_sz_boxed_3977_ = lean_unbox_usize(v_sz_3969_);
lean_dec(v_sz_3969_);
v_i_boxed_3978_ = lean_unbox_usize(v_i_3970_);
lean_dec(v_i_3970_);
v_res_3979_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3966_, v_params_3967_, v_motive_3968_, v_sz_boxed_3977_, v_i_boxed_3978_, v_bs_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec_ref(v___y_3972_);
lean_dec_ref(v_params_3967_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3982_, lean_object* v_tail_3983_, lean_object* v_params_3984_, lean_object* v_numIndices_3985_, lean_object* v___x_3986_, lean_object* v___x_3987_, uint8_t v___x_3988_, uint8_t v___x_3989_, uint8_t v___x_3990_, lean_object* v_is_3991_, lean_object* v___x_3992_, lean_object* v___x_3993_, lean_object* v___x_3994_, lean_object* v___x_3995_, lean_object* v___x_3996_, lean_object* v___x_3997_, lean_object* v_heq_3998_, lean_object* v_val_3999_, lean_object* v___x_4000_, lean_object* v_declName_4001_, lean_object* v_levelParams_4002_, lean_object* v___x_4003_, lean_object* v___x_4004_, lean_object* v_numParams_4005_, lean_object* v___x_4006_, lean_object* v_motive_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v___x_4013_; size_t v_sz_4014_; size_t v___x_4015_; lean_object* v___x_4016_; 
v___x_4013_ = lean_array_mk(v_ctors_3982_);
v_sz_4014_ = lean_array_size(v___x_4013_);
v___x_4015_ = ((size_t)0ULL);
lean_inc_ref(v___x_4013_);
lean_inc_ref(v_motive_4007_);
lean_inc(v_tail_3983_);
v___x_4016_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3983_, v_params_3984_, v_motive_4007_, v_sz_4014_, v___x_4015_, v___x_4013_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4018_; lean_object* v_fst_4019_; lean_object* v_snd_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___f_4026_; uint8_t v___x_4027_; lean_object* v___x_4028_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref_known(v___x_4016_, 1);
v___x_4018_ = l_Array_unzip___redArg(v_a_4017_);
lean_dec(v_a_4017_);
v_fst_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_fst_4019_);
v_snd_4020_ = lean_ctor_get(v___x_4018_, 1);
lean_inc(v_snd_4020_);
lean_dec_ref(v___x_4018_);
v___x_4021_ = lean_box(v___x_3988_);
v___x_4022_ = lean_box(v___x_3989_);
v___x_4023_ = lean_box(v___x_3990_);
v___x_4024_ = lean_box_usize(v_sz_4014_);
v___x_4025_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4026_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4026_, 0, v_numIndices_3985_);
lean_closure_set(v___f_4026_, 1, v___x_3986_);
lean_closure_set(v___f_4026_, 2, v_motive_4007_);
lean_closure_set(v___f_4026_, 3, v___x_3987_);
lean_closure_set(v___f_4026_, 4, v___x_4021_);
lean_closure_set(v___f_4026_, 5, v___x_4022_);
lean_closure_set(v___f_4026_, 6, v___x_4023_);
lean_closure_set(v___f_4026_, 7, v_is_3991_);
lean_closure_set(v___f_4026_, 8, v___x_3992_);
lean_closure_set(v___f_4026_, 9, v___x_3993_);
lean_closure_set(v___f_4026_, 10, v___x_3994_);
lean_closure_set(v___f_4026_, 11, v___x_3995_);
lean_closure_set(v___f_4026_, 12, v_params_3984_);
lean_closure_set(v___f_4026_, 13, v___x_3996_);
lean_closure_set(v___f_4026_, 14, v___x_3997_);
lean_closure_set(v___f_4026_, 15, v_heq_3998_);
lean_closure_set(v___f_4026_, 16, v_val_3999_);
lean_closure_set(v___f_4026_, 17, v_tail_3983_);
lean_closure_set(v___f_4026_, 18, v___x_4024_);
lean_closure_set(v___f_4026_, 19, v___x_4025_);
lean_closure_set(v___f_4026_, 20, v___x_4013_);
lean_closure_set(v___f_4026_, 21, v___x_4000_);
lean_closure_set(v___f_4026_, 22, v_declName_4001_);
lean_closure_set(v___f_4026_, 23, v_levelParams_4002_);
lean_closure_set(v___f_4026_, 24, v___x_4003_);
lean_closure_set(v___f_4026_, 25, v___x_4004_);
lean_closure_set(v___f_4026_, 26, v_numParams_4005_);
lean_closure_set(v___f_4026_, 27, v_snd_4020_);
lean_closure_set(v___f_4026_, 28, v___x_4006_);
v___x_4027_ = 0;
v___x_4028_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_4019_, v___f_4026_, v___x_4027_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
return v___x_4028_;
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
lean_dec_ref(v___x_4013_);
lean_dec_ref(v_motive_4007_);
lean_dec_ref(v___x_4006_);
lean_dec(v_numParams_4005_);
lean_dec(v___x_4004_);
lean_dec(v___x_4003_);
lean_dec(v_levelParams_4002_);
lean_dec(v_declName_4001_);
lean_dec_ref(v___x_4000_);
lean_dec_ref(v_val_3999_);
lean_dec_ref(v_heq_3998_);
lean_dec_ref(v___x_3997_);
lean_dec_ref(v___x_3996_);
lean_dec(v___x_3995_);
lean_dec(v___x_3994_);
lean_dec_ref(v___x_3993_);
lean_dec_ref(v___x_3992_);
lean_dec_ref(v_is_3991_);
lean_dec_ref(v___x_3987_);
lean_dec(v___x_3986_);
lean_dec(v_numIndices_3985_);
lean_dec_ref(v_params_3984_);
lean_dec(v_tail_3983_);
v_a_4029_ = lean_ctor_get(v___x_4016_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4016_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4016_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4037_ = _args[0];
lean_object* v_tail_4038_ = _args[1];
lean_object* v_params_4039_ = _args[2];
lean_object* v_numIndices_4040_ = _args[3];
lean_object* v___x_4041_ = _args[4];
lean_object* v___x_4042_ = _args[5];
lean_object* v___x_4043_ = _args[6];
lean_object* v___x_4044_ = _args[7];
lean_object* v___x_4045_ = _args[8];
lean_object* v_is_4046_ = _args[9];
lean_object* v___x_4047_ = _args[10];
lean_object* v___x_4048_ = _args[11];
lean_object* v___x_4049_ = _args[12];
lean_object* v___x_4050_ = _args[13];
lean_object* v___x_4051_ = _args[14];
lean_object* v___x_4052_ = _args[15];
lean_object* v_heq_4053_ = _args[16];
lean_object* v_val_4054_ = _args[17];
lean_object* v___x_4055_ = _args[18];
lean_object* v_declName_4056_ = _args[19];
lean_object* v_levelParams_4057_ = _args[20];
lean_object* v___x_4058_ = _args[21];
lean_object* v___x_4059_ = _args[22];
lean_object* v_numParams_4060_ = _args[23];
lean_object* v___x_4061_ = _args[24];
lean_object* v_motive_4062_ = _args[25];
lean_object* v___y_4063_ = _args[26];
lean_object* v___y_4064_ = _args[27];
lean_object* v___y_4065_ = _args[28];
lean_object* v___y_4066_ = _args[29];
lean_object* v___y_4067_ = _args[30];
_start:
{
uint8_t v___x_16489__boxed_4068_; uint8_t v___x_16490__boxed_4069_; uint8_t v___x_16491__boxed_4070_; lean_object* v_res_4071_; 
v___x_16489__boxed_4068_ = lean_unbox(v___x_4043_);
v___x_16490__boxed_4069_ = lean_unbox(v___x_4044_);
v___x_16491__boxed_4070_ = lean_unbox(v___x_4045_);
v_res_4071_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4037_, v_tail_4038_, v_params_4039_, v_numIndices_4040_, v___x_4041_, v___x_4042_, v___x_16489__boxed_4068_, v___x_16490__boxed_4069_, v___x_16491__boxed_4070_, v_is_4046_, v___x_4047_, v___x_4048_, v___x_4049_, v___x_4050_, v___x_4051_, v___x_4052_, v_heq_4053_, v_val_4054_, v___x_4055_, v_declName_4056_, v_levelParams_4057_, v___x_4058_, v___x_4059_, v_numParams_4060_, v___x_4061_, v_motive_4062_, v___y_4063_, v___y_4064_, v___y_4065_, v___y_4066_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
lean_dec(v___y_4064_);
lean_dec_ref(v___y_4063_);
return v_res_4071_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4072_, lean_object* v___x_4073_, lean_object* v_is_4074_, lean_object* v_head_4075_, lean_object* v_ctors_4076_, lean_object* v_tail_4077_, lean_object* v_params_4078_, lean_object* v_numIndices_4079_, lean_object* v___x_4080_, lean_object* v___x_4081_, lean_object* v___x_4082_, lean_object* v___x_4083_, lean_object* v___x_4084_, lean_object* v_val_4085_, lean_object* v___x_4086_, lean_object* v_declName_4087_, lean_object* v_levelParams_4088_, lean_object* v___x_4089_, lean_object* v_numParams_4090_, lean_object* v___x_4091_, lean_object* v_heq_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; uint8_t v___x_4106_; uint8_t v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___f_4111_; lean_object* v___x_4112_; 
v___x_4098_ = lean_unsigned_to_nat(3u);
v___x_4099_ = lean_mk_empty_array_with_capacity(v___x_4098_);
lean_inc_ref(v___x_4072_);
v___x_4100_ = lean_array_push(v___x_4099_, v___x_4072_);
lean_inc_ref(v___x_4073_);
v___x_4101_ = lean_array_push(v___x_4100_, v___x_4073_);
lean_inc_ref(v_heq_4092_);
v___x_4102_ = lean_array_push(v___x_4101_, v_heq_4092_);
lean_inc_ref(v_is_4074_);
v___x_4103_ = l_Array_append___redArg(v_is_4074_, v___x_4102_);
lean_dec_ref(v___x_4102_);
v___x_4104_ = l_Lean_mkSort(v_head_4075_);
v___x_4105_ = 0;
v___x_4106_ = 1;
v___x_4107_ = 1;
v___x_4108_ = lean_box(v___x_4105_);
v___x_4109_ = lean_box(v___x_4106_);
v___x_4110_ = lean_box(v___x_4107_);
lean_inc_ref(v___x_4103_);
v___f_4111_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4111_, 0, v_ctors_4076_);
lean_closure_set(v___f_4111_, 1, v_tail_4077_);
lean_closure_set(v___f_4111_, 2, v_params_4078_);
lean_closure_set(v___f_4111_, 3, v_numIndices_4079_);
lean_closure_set(v___f_4111_, 4, v___x_4080_);
lean_closure_set(v___f_4111_, 5, v___x_4103_);
lean_closure_set(v___f_4111_, 6, v___x_4108_);
lean_closure_set(v___f_4111_, 7, v___x_4109_);
lean_closure_set(v___f_4111_, 8, v___x_4110_);
lean_closure_set(v___f_4111_, 9, v_is_4074_);
lean_closure_set(v___f_4111_, 10, v___x_4073_);
lean_closure_set(v___f_4111_, 11, v___x_4072_);
lean_closure_set(v___f_4111_, 12, v___x_4081_);
lean_closure_set(v___f_4111_, 13, v___x_4082_);
lean_closure_set(v___f_4111_, 14, v___x_4083_);
lean_closure_set(v___f_4111_, 15, v___x_4084_);
lean_closure_set(v___f_4111_, 16, v_heq_4092_);
lean_closure_set(v___f_4111_, 17, v_val_4085_);
lean_closure_set(v___f_4111_, 18, v___x_4086_);
lean_closure_set(v___f_4111_, 19, v_declName_4087_);
lean_closure_set(v___f_4111_, 20, v_levelParams_4088_);
lean_closure_set(v___f_4111_, 21, v___x_4098_);
lean_closure_set(v___f_4111_, 22, v___x_4089_);
lean_closure_set(v___f_4111_, 23, v_numParams_4090_);
lean_closure_set(v___f_4111_, 24, v___x_4091_);
v___x_4112_ = l_Lean_Meta_mkForallFVars(v___x_4103_, v___x_4104_, v___x_4105_, v___x_4106_, v___x_4106_, v___x_4107_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
lean_dec_ref(v___x_4103_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4114_; uint8_t v___x_4115_; lean_object* v___x_4116_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___x_4112_, 1);
v___x_4114_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4115_ = 0;
v___x_4116_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4114_, v___x_4107_, v_a_4113_, v___f_4111_, v___x_4115_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v___x_4116_;
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec_ref(v___f_4111_);
v_a_4117_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4112_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4112_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4125_ = _args[0];
lean_object* v___x_4126_ = _args[1];
lean_object* v_is_4127_ = _args[2];
lean_object* v_head_4128_ = _args[3];
lean_object* v_ctors_4129_ = _args[4];
lean_object* v_tail_4130_ = _args[5];
lean_object* v_params_4131_ = _args[6];
lean_object* v_numIndices_4132_ = _args[7];
lean_object* v___x_4133_ = _args[8];
lean_object* v___x_4134_ = _args[9];
lean_object* v___x_4135_ = _args[10];
lean_object* v___x_4136_ = _args[11];
lean_object* v___x_4137_ = _args[12];
lean_object* v_val_4138_ = _args[13];
lean_object* v___x_4139_ = _args[14];
lean_object* v_declName_4140_ = _args[15];
lean_object* v_levelParams_4141_ = _args[16];
lean_object* v___x_4142_ = _args[17];
lean_object* v_numParams_4143_ = _args[18];
lean_object* v___x_4144_ = _args[19];
lean_object* v_heq_4145_ = _args[20];
lean_object* v___y_4146_ = _args[21];
lean_object* v___y_4147_ = _args[22];
lean_object* v___y_4148_ = _args[23];
lean_object* v___y_4149_ = _args[24];
lean_object* v___y_4150_ = _args[25];
_start:
{
lean_object* v_res_4151_; 
v_res_4151_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4125_, v___x_4126_, v_is_4127_, v_head_4128_, v_ctors_4129_, v_tail_4130_, v_params_4131_, v_numIndices_4132_, v___x_4133_, v___x_4134_, v___x_4135_, v___x_4136_, v___x_4137_, v_val_4138_, v___x_4139_, v_declName_4140_, v_levelParams_4141_, v___x_4142_, v_numParams_4143_, v___x_4144_, v_heq_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4152_, lean_object* v_x1_4153_, lean_object* v_indName_4154_, lean_object* v_tail_4155_, lean_object* v_params_4156_, lean_object* v_is_4157_, lean_object* v___x_4158_, lean_object* v_head_4159_, lean_object* v_ctors_4160_, lean_object* v_numIndices_4161_, lean_object* v___x_4162_, lean_object* v___x_4163_, lean_object* v_val_4164_, lean_object* v_declName_4165_, lean_object* v_levelParams_4166_, lean_object* v_numParams_4167_, lean_object* v___x_4168_, lean_object* v_x2_4169_, lean_object* v_x_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___f_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4176_ = lean_unsigned_to_nat(0u);
v___x_4177_ = lean_array_get_borrowed(v___x_4152_, v_x1_4153_, v___x_4176_);
v___x_4178_ = lean_array_get_borrowed(v___x_4152_, v_x2_4169_, v___x_4176_);
v___x_4179_ = l_Lean_mkCtorIdxName(v_indName_4154_);
lean_inc(v_tail_4155_);
v___x_4180_ = l_Lean_mkConst(v___x_4179_, v_tail_4155_);
lean_inc_ref(v_params_4156_);
v___x_4181_ = l_Array_append___redArg(v_params_4156_, v_is_4157_);
v___x_4182_ = lean_mk_empty_array_with_capacity(v___x_4158_);
lean_inc_n(v___x_4177_, 2);
lean_inc_ref_n(v___x_4182_, 2);
v___x_4183_ = lean_array_push(v___x_4182_, v___x_4177_);
lean_inc_ref(v___x_4181_);
v___x_4184_ = l_Array_append___redArg(v___x_4181_, v___x_4183_);
lean_inc_ref(v___x_4180_);
v___x_4185_ = l_Lean_mkAppN(v___x_4180_, v___x_4184_);
lean_dec_ref(v___x_4184_);
lean_inc_n(v___x_4178_, 2);
v___x_4186_ = lean_array_push(v___x_4182_, v___x_4178_);
lean_inc_ref(v___x_4186_);
v___f_4187_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4187_, 0, v___x_4177_);
lean_closure_set(v___f_4187_, 1, v___x_4178_);
lean_closure_set(v___f_4187_, 2, v_is_4157_);
lean_closure_set(v___f_4187_, 3, v_head_4159_);
lean_closure_set(v___f_4187_, 4, v_ctors_4160_);
lean_closure_set(v___f_4187_, 5, v_tail_4155_);
lean_closure_set(v___f_4187_, 6, v_params_4156_);
lean_closure_set(v___f_4187_, 7, v_numIndices_4161_);
lean_closure_set(v___f_4187_, 8, v___x_4158_);
lean_closure_set(v___f_4187_, 9, v___x_4162_);
lean_closure_set(v___f_4187_, 10, v___x_4163_);
lean_closure_set(v___f_4187_, 11, v___x_4183_);
lean_closure_set(v___f_4187_, 12, v___x_4186_);
lean_closure_set(v___f_4187_, 13, v_val_4164_);
lean_closure_set(v___f_4187_, 14, v___x_4182_);
lean_closure_set(v___f_4187_, 15, v_declName_4165_);
lean_closure_set(v___f_4187_, 16, v_levelParams_4166_);
lean_closure_set(v___f_4187_, 17, v___x_4176_);
lean_closure_set(v___f_4187_, 18, v_numParams_4167_);
lean_closure_set(v___f_4187_, 19, v___x_4168_);
v___x_4188_ = l_Array_append___redArg(v___x_4181_, v___x_4186_);
lean_dec_ref(v___x_4186_);
v___x_4189_ = l_Lean_mkAppN(v___x_4180_, v___x_4188_);
lean_dec_ref(v___x_4188_);
v___x_4190_ = l_Lean_Meta_mkEq(v___x_4185_, v___x_4189_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
lean_dec_ref_known(v___x_4190_, 1);
v___x_4192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4193_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4192_, v_a_4191_, v___f_4187_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_);
return v___x_4193_;
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
lean_dec_ref(v___f_4187_);
v_a_4194_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v___x_4190_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v___x_4190_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4202_ = _args[0];
lean_object* v_x1_4203_ = _args[1];
lean_object* v_indName_4204_ = _args[2];
lean_object* v_tail_4205_ = _args[3];
lean_object* v_params_4206_ = _args[4];
lean_object* v_is_4207_ = _args[5];
lean_object* v___x_4208_ = _args[6];
lean_object* v_head_4209_ = _args[7];
lean_object* v_ctors_4210_ = _args[8];
lean_object* v_numIndices_4211_ = _args[9];
lean_object* v___x_4212_ = _args[10];
lean_object* v___x_4213_ = _args[11];
lean_object* v_val_4214_ = _args[12];
lean_object* v_declName_4215_ = _args[13];
lean_object* v_levelParams_4216_ = _args[14];
lean_object* v_numParams_4217_ = _args[15];
lean_object* v___x_4218_ = _args[16];
lean_object* v_x2_4219_ = _args[17];
lean_object* v_x_4220_ = _args[18];
lean_object* v___y_4221_ = _args[19];
lean_object* v___y_4222_ = _args[20];
lean_object* v___y_4223_ = _args[21];
lean_object* v___y_4224_ = _args[22];
lean_object* v___y_4225_ = _args[23];
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4202_, v_x1_4203_, v_indName_4204_, v_tail_4205_, v_params_4206_, v_is_4207_, v___x_4208_, v_head_4209_, v_ctors_4210_, v_numIndices_4211_, v___x_4212_, v___x_4213_, v_val_4214_, v_declName_4215_, v_levelParams_4216_, v_numParams_4217_, v___x_4218_, v_x2_4219_, v_x_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec_ref(v_x_4220_);
lean_dec_ref(v_x2_4219_);
lean_dec_ref(v_x1_4203_);
lean_dec_ref(v___x_4202_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4227_, lean_object* v_indName_4228_, lean_object* v_tail_4229_, lean_object* v_params_4230_, lean_object* v_is_4231_, lean_object* v___x_4232_, lean_object* v_head_4233_, lean_object* v_ctors_4234_, lean_object* v_numIndices_4235_, lean_object* v___x_4236_, lean_object* v___x_4237_, lean_object* v_val_4238_, lean_object* v_declName_4239_, lean_object* v_levelParams_4240_, lean_object* v_numParams_4241_, lean_object* v___x_4242_, lean_object* v_t_4243_, lean_object* v___x_4244_, lean_object* v_x1_4245_, lean_object* v_x_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___f_4252_; uint8_t v___x_4253_; lean_object* v___x_4254_; 
v___f_4252_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4252_, 0, v___x_4227_);
lean_closure_set(v___f_4252_, 1, v_x1_4245_);
lean_closure_set(v___f_4252_, 2, v_indName_4228_);
lean_closure_set(v___f_4252_, 3, v_tail_4229_);
lean_closure_set(v___f_4252_, 4, v_params_4230_);
lean_closure_set(v___f_4252_, 5, v_is_4231_);
lean_closure_set(v___f_4252_, 6, v___x_4232_);
lean_closure_set(v___f_4252_, 7, v_head_4233_);
lean_closure_set(v___f_4252_, 8, v_ctors_4234_);
lean_closure_set(v___f_4252_, 9, v_numIndices_4235_);
lean_closure_set(v___f_4252_, 10, v___x_4236_);
lean_closure_set(v___f_4252_, 11, v___x_4237_);
lean_closure_set(v___f_4252_, 12, v_val_4238_);
lean_closure_set(v___f_4252_, 13, v_declName_4239_);
lean_closure_set(v___f_4252_, 14, v_levelParams_4240_);
lean_closure_set(v___f_4252_, 15, v_numParams_4241_);
lean_closure_set(v___f_4252_, 16, v___x_4242_);
v___x_4253_ = 0;
v___x_4254_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4243_, v___x_4244_, v___f_4252_, v___x_4253_, v___x_4253_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
return v___x_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4255_ = _args[0];
lean_object* v_indName_4256_ = _args[1];
lean_object* v_tail_4257_ = _args[2];
lean_object* v_params_4258_ = _args[3];
lean_object* v_is_4259_ = _args[4];
lean_object* v___x_4260_ = _args[5];
lean_object* v_head_4261_ = _args[6];
lean_object* v_ctors_4262_ = _args[7];
lean_object* v_numIndices_4263_ = _args[8];
lean_object* v___x_4264_ = _args[9];
lean_object* v___x_4265_ = _args[10];
lean_object* v_val_4266_ = _args[11];
lean_object* v_declName_4267_ = _args[12];
lean_object* v_levelParams_4268_ = _args[13];
lean_object* v_numParams_4269_ = _args[14];
lean_object* v___x_4270_ = _args[15];
lean_object* v_t_4271_ = _args[16];
lean_object* v___x_4272_ = _args[17];
lean_object* v_x1_4273_ = _args[18];
lean_object* v_x_4274_ = _args[19];
lean_object* v___y_4275_ = _args[20];
lean_object* v___y_4276_ = _args[21];
lean_object* v___y_4277_ = _args[22];
lean_object* v___y_4278_ = _args[23];
lean_object* v___y_4279_ = _args[24];
_start:
{
lean_object* v_res_4280_; 
v_res_4280_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4255_, v_indName_4256_, v_tail_4257_, v_params_4258_, v_is_4259_, v___x_4260_, v_head_4261_, v_ctors_4262_, v_numIndices_4263_, v___x_4264_, v___x_4265_, v_val_4266_, v_declName_4267_, v_levelParams_4268_, v_numParams_4269_, v___x_4270_, v_t_4271_, v___x_4272_, v_x1_4273_, v_x_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_);
lean_dec(v___y_4278_);
lean_dec_ref(v___y_4277_);
lean_dec(v___y_4276_);
lean_dec_ref(v___y_4275_);
lean_dec_ref(v_x_4274_);
return v_res_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4281_, lean_object* v_indName_4282_, lean_object* v_tail_4283_, lean_object* v_params_4284_, lean_object* v_head_4285_, lean_object* v_ctors_4286_, lean_object* v_numIndices_4287_, lean_object* v___x_4288_, lean_object* v___x_4289_, lean_object* v_val_4290_, lean_object* v_declName_4291_, lean_object* v_levelParams_4292_, lean_object* v_numParams_4293_, lean_object* v___x_4294_, lean_object* v_is_4295_, lean_object* v_t_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___f_4304_; uint8_t v___x_4305_; lean_object* v___x_4306_; 
v___x_4302_ = lean_unsigned_to_nat(1u);
v___x_4303_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4296_);
v___f_4304_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4304_, 0, v___x_4281_);
lean_closure_set(v___f_4304_, 1, v_indName_4282_);
lean_closure_set(v___f_4304_, 2, v_tail_4283_);
lean_closure_set(v___f_4304_, 3, v_params_4284_);
lean_closure_set(v___f_4304_, 4, v_is_4295_);
lean_closure_set(v___f_4304_, 5, v___x_4302_);
lean_closure_set(v___f_4304_, 6, v_head_4285_);
lean_closure_set(v___f_4304_, 7, v_ctors_4286_);
lean_closure_set(v___f_4304_, 8, v_numIndices_4287_);
lean_closure_set(v___f_4304_, 9, v___x_4288_);
lean_closure_set(v___f_4304_, 10, v___x_4289_);
lean_closure_set(v___f_4304_, 11, v_val_4290_);
lean_closure_set(v___f_4304_, 12, v_declName_4291_);
lean_closure_set(v___f_4304_, 13, v_levelParams_4292_);
lean_closure_set(v___f_4304_, 14, v_numParams_4293_);
lean_closure_set(v___f_4304_, 15, v___x_4294_);
lean_closure_set(v___f_4304_, 16, v_t_4296_);
lean_closure_set(v___f_4304_, 17, v___x_4303_);
v___x_4305_ = 0;
v___x_4306_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4296_, v___x_4303_, v___f_4304_, v___x_4305_, v___x_4305_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
return v___x_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4307_ = _args[0];
lean_object* v_indName_4308_ = _args[1];
lean_object* v_tail_4309_ = _args[2];
lean_object* v_params_4310_ = _args[3];
lean_object* v_head_4311_ = _args[4];
lean_object* v_ctors_4312_ = _args[5];
lean_object* v_numIndices_4313_ = _args[6];
lean_object* v___x_4314_ = _args[7];
lean_object* v___x_4315_ = _args[8];
lean_object* v_val_4316_ = _args[9];
lean_object* v_declName_4317_ = _args[10];
lean_object* v_levelParams_4318_ = _args[11];
lean_object* v_numParams_4319_ = _args[12];
lean_object* v___x_4320_ = _args[13];
lean_object* v_is_4321_ = _args[14];
lean_object* v_t_4322_ = _args[15];
lean_object* v___y_4323_ = _args[16];
lean_object* v___y_4324_ = _args[17];
lean_object* v___y_4325_ = _args[18];
lean_object* v___y_4326_ = _args[19];
lean_object* v___y_4327_ = _args[20];
_start:
{
lean_object* v_res_4328_; 
v_res_4328_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4307_, v_indName_4308_, v_tail_4309_, v_params_4310_, v_head_4311_, v_ctors_4312_, v_numIndices_4313_, v___x_4314_, v___x_4315_, v_val_4316_, v_declName_4317_, v_levelParams_4318_, v_numParams_4319_, v___x_4320_, v_is_4321_, v_t_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec(v___y_4324_);
lean_dec_ref(v___y_4323_);
return v_res_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4329_, lean_object* v_indName_4330_, lean_object* v_tail_4331_, lean_object* v_head_4332_, lean_object* v_ctors_4333_, lean_object* v_numIndices_4334_, lean_object* v___x_4335_, lean_object* v___x_4336_, lean_object* v_val_4337_, lean_object* v_declName_4338_, lean_object* v_levelParams_4339_, lean_object* v_numParams_4340_, lean_object* v_params_4341_, lean_object* v_t_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v___x_4348_; lean_object* v___f_4349_; lean_object* v___x_4350_; uint8_t v___x_4351_; lean_object* v___x_4352_; 
v___x_4348_ = l_Lean_Expr_bindingBody_x21(v_t_4342_);
lean_inc_ref(v___x_4348_);
lean_inc(v_numIndices_4334_);
v___f_4349_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4349_, 0, v___x_4329_);
lean_closure_set(v___f_4349_, 1, v_indName_4330_);
lean_closure_set(v___f_4349_, 2, v_tail_4331_);
lean_closure_set(v___f_4349_, 3, v_params_4341_);
lean_closure_set(v___f_4349_, 4, v_head_4332_);
lean_closure_set(v___f_4349_, 5, v_ctors_4333_);
lean_closure_set(v___f_4349_, 6, v_numIndices_4334_);
lean_closure_set(v___f_4349_, 7, v___x_4335_);
lean_closure_set(v___f_4349_, 8, v___x_4336_);
lean_closure_set(v___f_4349_, 9, v_val_4337_);
lean_closure_set(v___f_4349_, 10, v_declName_4338_);
lean_closure_set(v___f_4349_, 11, v_levelParams_4339_);
lean_closure_set(v___f_4349_, 12, v_numParams_4340_);
lean_closure_set(v___f_4349_, 13, v___x_4348_);
v___x_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4350_, 0, v_numIndices_4334_);
v___x_4351_ = 0;
v___x_4352_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4348_, v___x_4350_, v___f_4349_, v___x_4351_, v___x_4351_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4353_ = _args[0];
lean_object* v_indName_4354_ = _args[1];
lean_object* v_tail_4355_ = _args[2];
lean_object* v_head_4356_ = _args[3];
lean_object* v_ctors_4357_ = _args[4];
lean_object* v_numIndices_4358_ = _args[5];
lean_object* v___x_4359_ = _args[6];
lean_object* v___x_4360_ = _args[7];
lean_object* v_val_4361_ = _args[8];
lean_object* v_declName_4362_ = _args[9];
lean_object* v_levelParams_4363_ = _args[10];
lean_object* v_numParams_4364_ = _args[11];
lean_object* v_params_4365_ = _args[12];
lean_object* v_t_4366_ = _args[13];
lean_object* v___y_4367_ = _args[14];
lean_object* v___y_4368_ = _args[15];
lean_object* v___y_4369_ = _args[16];
lean_object* v___y_4370_ = _args[17];
lean_object* v___y_4371_ = _args[18];
_start:
{
lean_object* v_res_4372_; 
v_res_4372_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4353_, v_indName_4354_, v_tail_4355_, v_head_4356_, v_ctors_4357_, v_numIndices_4358_, v___x_4359_, v___x_4360_, v_val_4361_, v_declName_4362_, v_levelParams_4363_, v_numParams_4364_, v_params_4365_, v_t_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
lean_dec(v___y_4370_);
lean_dec_ref(v___y_4369_);
lean_dec(v___y_4368_);
lean_dec_ref(v___y_4367_);
lean_dec_ref(v_t_4366_);
return v_res_4372_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v___x_4377_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4378_ = lean_unsigned_to_nat(58u);
v___x_4379_ = lean_unsigned_to_nat(142u);
v___x_4380_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4381_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4382_ = l_mkPanicMessageWithDecl(v___x_4381_, v___x_4380_, v___x_4379_, v___x_4378_, v___x_4377_);
return v___x_4382_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4383_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4384_ = lean_unsigned_to_nat(60u);
v___x_4385_ = lean_unsigned_to_nat(136u);
v___x_4386_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4387_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4388_ = l_mkPanicMessageWithDecl(v___x_4387_, v___x_4386_, v___x_4385_, v___x_4384_, v___x_4383_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4389_, lean_object* v_indName_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_4390_);
v___x_4397_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v___x_4397_, 1);
if (lean_obj_tag(v_a_4398_) == 5)
{
lean_object* v_val_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v_val_4399_ = lean_ctor_get(v_a_4398_, 0);
lean_inc_ref(v_val_4399_);
lean_dec_ref_known(v_a_4398_, 1);
v___x_4400_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4389_);
v___x_4401_ = l_Lean_Name_append(v_declName_4389_, v___x_4400_);
lean_inc(v_indName_4390_);
lean_inc(v___x_4401_);
v___x_4402_ = l_Lean_mkCasesOnSameCtorHet(v___x_4401_, v_indName_4390_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4434_; 
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4434_ == 0)
{
lean_object* v_unused_4435_; 
v_unused_4435_ = lean_ctor_get(v___x_4402_, 0);
lean_dec(v_unused_4435_);
v___x_4404_ = v___x_4402_;
v_isShared_4405_ = v_isSharedCheck_4434_;
goto v_resetjp_4403_;
}
else
{
lean_dec(v___x_4402_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4434_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
lean_inc(v_indName_4390_);
v___x_4406_ = l_Lean_mkCasesOnName(v_indName_4390_);
v___x_4407_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4406_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v_levelParams_4409_; lean_object* v_type_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref_known(v___x_4407_, 1);
v_levelParams_4409_ = lean_ctor_get(v_a_4408_, 1);
lean_inc_n(v_levelParams_4409_, 2);
v_type_4410_ = lean_ctor_get(v_a_4408_, 2);
lean_inc_ref(v_type_4410_);
lean_dec(v_a_4408_);
v___x_4411_ = lean_box(0);
v___x_4412_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4409_, v___x_4411_);
if (lean_obj_tag(v___x_4412_) == 1)
{
lean_object* v_head_4413_; lean_object* v_tail_4414_; lean_object* v_numParams_4415_; lean_object* v_numIndices_4416_; lean_object* v_ctors_4417_; lean_object* v___f_4418_; lean_object* v___x_4420_; 
v_head_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_head_4413_);
v_tail_4414_ = lean_ctor_get(v___x_4412_, 1);
lean_inc(v_tail_4414_);
v_numParams_4415_ = lean_ctor_get(v_val_4399_, 1);
lean_inc_n(v_numParams_4415_, 2);
v_numIndices_4416_ = lean_ctor_get(v_val_4399_, 2);
lean_inc(v_numIndices_4416_);
v_ctors_4417_ = lean_ctor_get(v_val_4399_, 4);
lean_inc(v_ctors_4417_);
v___f_4418_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4418_, 0, v___x_4396_);
lean_closure_set(v___f_4418_, 1, v_indName_4390_);
lean_closure_set(v___f_4418_, 2, v_tail_4414_);
lean_closure_set(v___f_4418_, 3, v_head_4413_);
lean_closure_set(v___f_4418_, 4, v_ctors_4417_);
lean_closure_set(v___f_4418_, 5, v_numIndices_4416_);
lean_closure_set(v___f_4418_, 6, v___x_4401_);
lean_closure_set(v___f_4418_, 7, v___x_4412_);
lean_closure_set(v___f_4418_, 8, v_val_4399_);
lean_closure_set(v___f_4418_, 9, v_declName_4389_);
lean_closure_set(v___f_4418_, 10, v_levelParams_4409_);
lean_closure_set(v___f_4418_, 11, v_numParams_4415_);
if (v_isShared_4405_ == 0)
{
lean_ctor_set_tag(v___x_4404_, 1);
lean_ctor_set(v___x_4404_, 0, v_numParams_4415_);
v___x_4420_ = v___x_4404_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_numParams_4415_);
v___x_4420_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
uint8_t v___x_4421_; lean_object* v___x_4422_; 
v___x_4421_ = 0;
v___x_4422_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4410_, v___x_4420_, v___f_4418_, v___x_4421_, v___x_4421_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
return v___x_4422_;
}
}
else
{
lean_object* v___x_4424_; lean_object* v___x_4425_; 
lean_dec(v___x_4412_);
lean_dec_ref(v_type_4410_);
lean_dec(v_levelParams_4409_);
lean_del_object(v___x_4404_);
lean_dec(v___x_4401_);
lean_dec_ref(v_val_4399_);
lean_dec(v_indName_4390_);
lean_dec(v_declName_4389_);
v___x_4424_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4425_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4424_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
return v___x_4425_;
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_del_object(v___x_4404_);
lean_dec(v___x_4401_);
lean_dec_ref(v_val_4399_);
lean_dec(v_indName_4390_);
lean_dec(v_declName_4389_);
v_a_4426_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4407_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4407_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
}
else
{
lean_dec(v___x_4401_);
lean_dec_ref(v_val_4399_);
lean_dec(v_indName_4390_);
lean_dec(v_declName_4389_);
return v___x_4402_;
}
}
else
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
lean_dec(v_a_4398_);
lean_dec(v_indName_4390_);
lean_dec(v_declName_4389_);
v___x_4436_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4437_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4436_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_);
return v___x_4437_;
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec(v_indName_4390_);
lean_dec(v_declName_4389_);
v_a_4438_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4397_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4397_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4446_, lean_object* v_indName_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l_Lean_mkCasesOnSameCtor(v_declName_4446_, v_indName_4447_, v_a_4448_, v_a_4449_, v_a_4450_, v_a_4451_);
lean_dec(v_a_4451_);
lean_dec_ref(v_a_4450_);
lean_dec(v_a_4449_);
lean_dec_ref(v_a_4448_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4454_, lean_object* v_params_4455_, lean_object* v_motive_4456_, lean_object* v_as_4457_, size_t v_sz_4458_, size_t v_i_4459_, lean_object* v_bs_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v___x_4466_; 
v___x_4466_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4454_, v_params_4455_, v_motive_4456_, v_sz_4458_, v_i_4459_, v_bs_4460_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
return v___x_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4467_, lean_object* v_params_4468_, lean_object* v_motive_4469_, lean_object* v_as_4470_, lean_object* v_sz_4471_, lean_object* v_i_4472_, lean_object* v_bs_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
size_t v_sz_boxed_4479_; size_t v_i_boxed_4480_; lean_object* v_res_4481_; 
v_sz_boxed_4479_ = lean_unbox_usize(v_sz_4471_);
lean_dec(v_sz_4471_);
v_i_boxed_4480_ = lean_unbox_usize(v_i_4472_);
lean_dec(v_i_4472_);
v_res_4481_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4467_, v_params_4468_, v_motive_4469_, v_as_4470_, v_sz_boxed_4479_, v_i_boxed_4480_, v_bs_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
lean_dec(v___y_4477_);
lean_dec_ref(v___y_4476_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec_ref(v_as_4470_);
lean_dec_ref(v_params_4468_);
return v_res_4481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4482_, lean_object* v_params_4483_, lean_object* v_a_4484_, lean_object* v_snd_4485_, lean_object* v_alts_4486_, lean_object* v_as_4487_, size_t v_sz_4488_, size_t v_i_4489_, lean_object* v_bs_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4482_, v_params_4483_, v_a_4484_, v_snd_4485_, v_alts_4486_, v_sz_4488_, v_i_4489_, v_bs_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4497_, lean_object* v_params_4498_, lean_object* v_a_4499_, lean_object* v_snd_4500_, lean_object* v_alts_4501_, lean_object* v_as_4502_, lean_object* v_sz_4503_, lean_object* v_i_4504_, lean_object* v_bs_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
size_t v_sz_boxed_4511_; size_t v_i_boxed_4512_; lean_object* v_res_4513_; 
v_sz_boxed_4511_ = lean_unbox_usize(v_sz_4503_);
lean_dec(v_sz_4503_);
v_i_boxed_4512_ = lean_unbox_usize(v_i_4504_);
lean_dec(v_i_4504_);
v_res_4513_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4497_, v_params_4498_, v_a_4499_, v_snd_4500_, v_alts_4501_, v_as_4502_, v_sz_boxed_4511_, v_i_boxed_4512_, v_bs_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec_ref(v_as_4502_);
lean_dec_ref(v_params_4498_);
return v_res_4513_;
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
