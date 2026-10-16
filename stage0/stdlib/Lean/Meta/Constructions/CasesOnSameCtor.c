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
lean_object* v___x_235_; uint8_t v___y_237_; lean_object* v_env_245_; uint8_t v___x_246_; 
v___x_235_ = lean_st_ref_get(v___y_233_);
v_env_245_ = lean_ctor_get(v___x_235_, 0);
lean_inc_ref_n(v_env_245_, 2);
lean_dec(v___x_235_);
v___x_246_ = l_Lean_Environment_hasUnsafe(v_env_245_, v_type_230_);
if (v___x_246_ == 0)
{
uint8_t v___x_247_; 
v___x_247_ = l_Lean_Environment_hasUnsafe(v_env_245_, v_value_231_);
if (v___x_247_ == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 1;
v___y_237_ = v___x_248_;
goto v___jp_236_;
}
else
{
goto v___jp_243_;
}
}
else
{
lean_dec_ref(v_env_245_);
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
uint8_t v___x_244_; 
v___x_244_ = 0;
v___y_237_ = v___x_244_;
goto v___jp_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg___boxed(lean_object* v_name_249_, lean_object* v_levelParams_250_, lean_object* v_type_251_, lean_object* v_value_252_, lean_object* v_hints_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_249_, v_levelParams_250_, v_type_251_, v_value_252_, v_hints_253_, v___y_254_);
lean_dec(v___y_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(lean_object* v_name_257_, lean_object* v_levelParams_258_, lean_object* v_type_259_, lean_object* v_value_260_, lean_object* v_hints_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_name_257_, v_levelParams_258_, v_type_259_, v_value_260_, v_hints_261_, v___y_265_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___boxed(lean_object* v_name_268_, lean_object* v_levelParams_269_, lean_object* v_type_270_, lean_object* v_value_271_, lean_object* v_hints_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(v_name_268_, v_levelParams_269_, v_type_270_, v_value_271_, v_hints_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object* v___y_279_, uint8_t v_isExporting_280_, lean_object* v___x_281_, lean_object* v___y_282_, lean_object* v___x_283_, lean_object* v_a_x3f_284_){
_start:
{
lean_object* v___x_286_; lean_object* v_env_287_; lean_object* v_nextMacroScope_288_; lean_object* v_ngen_289_; lean_object* v_auxDeclNGen_290_; lean_object* v_traceState_291_; lean_object* v_recordedDeps_292_; lean_object* v_messages_293_; lean_object* v_infoState_294_; lean_object* v_snapshotTasks_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_320_; 
v___x_286_ = lean_st_ref_take(v___y_279_);
v_env_287_ = lean_ctor_get(v___x_286_, 0);
v_nextMacroScope_288_ = lean_ctor_get(v___x_286_, 1);
v_ngen_289_ = lean_ctor_get(v___x_286_, 2);
v_auxDeclNGen_290_ = lean_ctor_get(v___x_286_, 3);
v_traceState_291_ = lean_ctor_get(v___x_286_, 4);
v_recordedDeps_292_ = lean_ctor_get(v___x_286_, 6);
v_messages_293_ = lean_ctor_get(v___x_286_, 7);
v_infoState_294_ = lean_ctor_get(v___x_286_, 8);
v_snapshotTasks_295_ = lean_ctor_get(v___x_286_, 9);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_286_, 5);
lean_dec(v_unused_321_);
v___x_297_ = v___x_286_;
v_isShared_298_ = v_isSharedCheck_320_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_snapshotTasks_295_);
lean_inc(v_infoState_294_);
lean_inc(v_messages_293_);
lean_inc(v_recordedDeps_292_);
lean_inc(v_traceState_291_);
lean_inc(v_auxDeclNGen_290_);
lean_inc(v_ngen_289_);
lean_inc(v_nextMacroScope_288_);
lean_inc(v_env_287_);
lean_dec(v___x_286_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_320_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_Environment_setExporting(v_env_287_, v_isExporting_280_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 5, v___x_281_);
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_nextMacroScope_288_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_ngen_289_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_auxDeclNGen_290_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_traceState_291_);
lean_ctor_set(v_reuseFailAlloc_319_, 5, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_319_, 6, v_recordedDeps_292_);
lean_ctor_set(v_reuseFailAlloc_319_, 7, v_messages_293_);
lean_ctor_set(v_reuseFailAlloc_319_, 8, v_infoState_294_);
lean_ctor_set(v_reuseFailAlloc_319_, 9, v_snapshotTasks_295_);
v___x_301_ = v_reuseFailAlloc_319_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_mctx_304_; lean_object* v_zetaDeltaFVarIds_305_; lean_object* v_postponed_306_; lean_object* v_diag_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_317_; 
v___x_302_ = lean_st_ref_put(v___y_279_, v___x_301_);
v___x_303_ = lean_st_ref_take(v___y_282_);
v_mctx_304_ = lean_ctor_get(v___x_303_, 0);
v_zetaDeltaFVarIds_305_ = lean_ctor_get(v___x_303_, 2);
v_postponed_306_ = lean_ctor_get(v___x_303_, 3);
v_diag_307_ = lean_ctor_get(v___x_303_, 4);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v___x_303_, 1);
lean_dec(v_unused_318_);
v___x_309_ = v___x_303_;
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_diag_307_);
lean_inc(v_postponed_306_);
lean_inc(v_zetaDeltaFVarIds_305_);
lean_inc(v_mctx_304_);
lean_dec(v___x_303_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_box(0);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v___x_283_);
v___x_313_ = v___x_309_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_mctx_304_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_zetaDeltaFVarIds_305_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_postponed_306_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_diag_307_);
v___x_313_ = v_reuseFailAlloc_316_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_st_ref_put(v___y_282_, v___x_313_);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_311_);
return v___x_315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object* v___y_322_, lean_object* v_isExporting_323_, lean_object* v___x_324_, lean_object* v___y_325_, lean_object* v___x_326_, lean_object* v_a_x3f_327_, lean_object* v___y_328_){
_start:
{
uint8_t v_isExporting_boxed_329_; lean_object* v_res_330_; 
v_isExporting_boxed_329_ = lean_unbox(v_isExporting_323_);
v_res_330_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_322_, v_isExporting_boxed_329_, v___x_324_, v___y_325_, v___x_326_, v_a_x3f_327_);
lean_dec(v_a_x3f_327_);
lean_dec(v___y_325_);
lean_dec(v___y_322_);
return v_res_330_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_331_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_337_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
lean_ctor_set(v___x_337_, 4, v___x_336_);
lean_ctor_set(v___x_337_, 5, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object* v_x_338_, uint8_t v_isExporting_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v___x_345_; lean_object* v_env_346_; lean_object* v___x_347_; uint8_t v_isModule_348_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_346_);
lean_dec(v___x_345_);
v___x_347_ = l_Lean_Environment_header(v_env_346_);
v_isModule_348_ = lean_ctor_get_uint8(v___x_347_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_347_);
if (v_isModule_348_ == 0)
{
lean_object* v___x_349_; 
lean_dec_ref(v_env_346_);
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v___x_349_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
return v___x_349_;
}
else
{
uint8_t v_isExporting_350_; 
v_isExporting_350_ = lean_ctor_get_uint8(v_env_346_, sizeof(void*)*13);
lean_dec_ref(v_env_346_);
if (v_isExporting_339_ == 0)
{
if (v_isExporting_350_ == 0)
{
lean_object* v___x_417_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v___x_417_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
return v___x_417_;
}
else
{
goto v___jp_351_;
}
}
else
{
if (v_isExporting_350_ == 0)
{
goto v___jp_351_;
}
else
{
lean_object* v___x_418_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v___x_418_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
return v___x_418_;
}
}
v___jp_351_:
{
lean_object* v___x_352_; lean_object* v_env_353_; lean_object* v_nextMacroScope_354_; lean_object* v_ngen_355_; lean_object* v_auxDeclNGen_356_; lean_object* v_traceState_357_; lean_object* v_recordedDeps_358_; lean_object* v_messages_359_; lean_object* v_infoState_360_; lean_object* v_snapshotTasks_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_415_; 
v___x_352_ = lean_st_ref_take(v___y_343_);
v_env_353_ = lean_ctor_get(v___x_352_, 0);
v_nextMacroScope_354_ = lean_ctor_get(v___x_352_, 1);
v_ngen_355_ = lean_ctor_get(v___x_352_, 2);
v_auxDeclNGen_356_ = lean_ctor_get(v___x_352_, 3);
v_traceState_357_ = lean_ctor_get(v___x_352_, 4);
v_recordedDeps_358_ = lean_ctor_get(v___x_352_, 6);
v_messages_359_ = lean_ctor_get(v___x_352_, 7);
v_infoState_360_ = lean_ctor_get(v___x_352_, 8);
v_snapshotTasks_361_ = lean_ctor_get(v___x_352_, 9);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v___x_352_, 5);
lean_dec(v_unused_416_);
v___x_363_ = v___x_352_;
v_isShared_364_ = v_isSharedCheck_415_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_snapshotTasks_361_);
lean_inc(v_infoState_360_);
lean_inc(v_messages_359_);
lean_inc(v_recordedDeps_358_);
lean_inc(v_traceState_357_);
lean_inc(v_auxDeclNGen_356_);
lean_inc(v_ngen_355_);
lean_inc(v_nextMacroScope_354_);
lean_inc(v_env_353_);
lean_dec(v___x_352_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_415_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_365_ = l_Lean_Environment_setExporting(v_env_353_, v_isExporting_339_);
v___x_366_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 5, v___x_366_);
lean_ctor_set(v___x_363_, 0, v___x_365_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_nextMacroScope_354_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v_ngen_355_);
lean_ctor_set(v_reuseFailAlloc_414_, 3, v_auxDeclNGen_356_);
lean_ctor_set(v_reuseFailAlloc_414_, 4, v_traceState_357_);
lean_ctor_set(v_reuseFailAlloc_414_, 5, v___x_366_);
lean_ctor_set(v_reuseFailAlloc_414_, 6, v_recordedDeps_358_);
lean_ctor_set(v_reuseFailAlloc_414_, 7, v_messages_359_);
lean_ctor_set(v_reuseFailAlloc_414_, 8, v_infoState_360_);
lean_ctor_set(v_reuseFailAlloc_414_, 9, v_snapshotTasks_361_);
v___x_368_ = v_reuseFailAlloc_414_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_mctx_371_; lean_object* v_zetaDeltaFVarIds_372_; lean_object* v_postponed_373_; lean_object* v_diag_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_412_; 
v___x_369_ = lean_st_ref_put(v___y_343_, v___x_368_);
v___x_370_ = lean_st_ref_take(v___y_341_);
v_mctx_371_ = lean_ctor_get(v___x_370_, 0);
v_zetaDeltaFVarIds_372_ = lean_ctor_get(v___x_370_, 2);
v_postponed_373_ = lean_ctor_get(v___x_370_, 3);
v_diag_374_ = lean_ctor_get(v___x_370_, 4);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_412_ == 0)
{
lean_object* v_unused_413_; 
v_unused_413_ = lean_ctor_get(v___x_370_, 1);
lean_dec(v_unused_413_);
v___x_376_ = v___x_370_;
v_isShared_377_ = v_isSharedCheck_412_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_diag_374_);
lean_inc(v_postponed_373_);
lean_inc(v_zetaDeltaFVarIds_372_);
lean_inc(v_mctx_371_);
lean_dec(v___x_370_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_412_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_378_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 1, v___x_378_);
v___x_380_ = v___x_376_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_mctx_371_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v___x_378_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_zetaDeltaFVarIds_372_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_postponed_373_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_diag_374_);
v___x_380_ = v_reuseFailAlloc_411_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
lean_object* v___x_381_; lean_object* v_r_382_; 
v___x_381_ = lean_st_ref_put(v___y_341_, v___x_380_);
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v_r_382_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
if (lean_obj_tag(v_r_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_399_; 
v_a_383_ = lean_ctor_get(v_r_382_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v_r_382_);
if (v_isSharedCheck_399_ == 0)
{
v___x_385_ = v_r_382_;
v_isShared_386_ = v_isSharedCheck_399_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v_r_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_399_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
lean_inc(v_a_383_);
if (v_isShared_386_ == 0)
{
lean_ctor_set_tag(v___x_385_, 1);
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_398_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
v___x_389_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_350_, v___x_366_, v___y_341_, v___x_378_, v___x_388_);
lean_dec_ref(v___x_388_);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v___x_389_, 0);
lean_dec(v_unused_397_);
v___x_391_ = v___x_389_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_dec(v___x_389_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
lean_ctor_set(v___x_391_, 0, v_a_383_);
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_383_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_a_400_ = lean_ctor_get(v_r_382_, 0);
lean_inc(v_a_400_);
lean_dec_ref_known(v_r_382_, 1);
v___x_401_ = lean_box(0);
v___x_402_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_350_, v___x_366_, v___y_341_, v___x_378_, v___x_401_);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_410_);
v___x_404_ = v___x_402_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_dec(v___x_402_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set_tag(v___x_404_, 1);
lean_ctor_set(v___x_404_, 0, v_a_400_);
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_400_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_419_, lean_object* v_isExporting_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
uint8_t v_isExporting_boxed_426_; lean_object* v_res_427_; 
v_isExporting_boxed_426_ = lean_unbox(v_isExporting_420_);
v_res_427_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_419_, v_isExporting_boxed_426_, v___y_421_, v___y_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v___y_422_);
lean_dec_ref(v___y_421_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_428_, lean_object* v_x_429_, uint8_t v_isExporting_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_429_, v_isExporting_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_437_, lean_object* v_x_438_, lean_object* v_isExporting_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
uint8_t v_isExporting_boxed_445_; lean_object* v_res_446_; 
v_isExporting_boxed_445_ = lean_unbox(v_isExporting_439_);
v_res_446_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_437_, v_x_438_, v_isExporting_boxed_445_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_msg_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___f_454_; lean_object* v___x_15760__overap_455_; lean_object* v___x_456_; 
v___f_454_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15760__overap_455_ = lean_panic_fn_borrowed(v___f_454_, v_msg_448_);
lean_inc(v___y_452_);
lean_inc_ref(v___y_451_);
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
v___x_456_ = lean_apply_5(v___x_15760__overap_455_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, lean_box(0));
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_msg_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_msg_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object* v_name_464_, lean_object* v_type_465_, lean_object* v_k_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
uint8_t v___x_472_; uint8_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = 0;
v___x_473_ = 0;
v___x_474_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_464_, v___x_472_, v_type_465_, v_k_466_, v___x_473_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object* v_name_475_, lean_object* v_type_476_, lean_object* v_k_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_475_, v_type_476_, v_k_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object* v___x_484_, lean_object* v_ism2_485_, lean_object* v_motive_486_, uint8_t v___x_487_, uint8_t v___x_488_, uint8_t v___x_489_, lean_object* v_a_490_, lean_object* v___f_491_, lean_object* v_zs1_492_, lean_object* v_val_493_, lean_object* v___x_494_, lean_object* v_indName_495_, lean_object* v_v_496_, lean_object* v___x_497_, lean_object* v_params_498_, lean_object* v___x_499_, lean_object* v_h_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_506_ = l_Array_append___redArg(v___x_484_, v_ism2_485_);
v___x_507_ = l_Lean_mkAppN(v_motive_486_, v___x_506_);
lean_dec_ref(v___x_506_);
v___x_508_ = l_Lean_Meta_mkLambdaFVars(v_ism2_485_, v___x_507_, v___x_487_, v___x_488_, v___x_487_, v___x_488_, v___x_489_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_510_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
lean_dec_ref_known(v___x_508_, 1);
v___x_510_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_490_, v___f_491_, v___x_487_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___y_513_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_a_511_);
lean_dec_ref_known(v___x_510_, 1);
v___x_516_ = l_Lean_InductiveVal_numCtors(v_val_493_);
v___x_517_ = lean_nat_dec_eq(v___x_516_, v___x_494_);
lean_dec(v___x_516_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_dec(v___x_499_);
v___x_518_ = l_Lean_mkConstructorElimName(v_indName_495_, v_v_496_);
v___x_519_ = l_Lean_mkConst(v___x_518_, v___x_497_);
v___x_520_ = lean_mk_empty_array_with_capacity(v___x_494_);
v___x_521_ = lean_array_push(v___x_520_, v_a_509_);
v___x_522_ = l_Array_append___redArg(v_params_498_, v___x_521_);
lean_dec_ref(v___x_521_);
v___x_523_ = l_Array_append___redArg(v___x_522_, v_ism2_485_);
v___x_524_ = lean_unsigned_to_nat(2u);
v___x_525_ = lean_mk_empty_array_with_capacity(v___x_524_);
lean_inc_ref(v_h_500_);
v___x_526_ = lean_array_push(v___x_525_, v_h_500_);
v___x_527_ = lean_array_push(v___x_526_, v_a_511_);
v___x_528_ = l_Array_append___redArg(v___x_523_, v___x_527_);
lean_dec_ref(v___x_527_);
v___x_529_ = l_Lean_mkAppN(v___x_519_, v___x_528_);
lean_dec_ref(v___x_528_);
v___y_513_ = v___x_529_;
goto v___jp_512_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v_v_496_);
v___x_530_ = l_Lean_mkConst(v___x_499_, v___x_497_);
v___x_531_ = lean_mk_empty_array_with_capacity(v___x_494_);
lean_inc_ref(v___x_531_);
v___x_532_ = lean_array_push(v___x_531_, v_a_509_);
v___x_533_ = l_Array_append___redArg(v_params_498_, v___x_532_);
lean_dec_ref(v___x_532_);
v___x_534_ = l_Array_append___redArg(v___x_533_, v_ism2_485_);
v___x_535_ = lean_array_push(v___x_531_, v_a_511_);
v___x_536_ = l_Array_append___redArg(v___x_534_, v___x_535_);
lean_dec_ref(v___x_535_);
v___x_537_ = l_Lean_mkAppN(v___x_530_, v___x_536_);
lean_dec_ref(v___x_536_);
v___y_513_ = v___x_537_;
goto v___jp_512_;
}
v___jp_512_:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = lean_array_push(v_zs1_492_, v_h_500_);
v___x_515_ = l_Lean_Meta_mkLambdaFVars(v___x_514_, v___y_513_, v___x_487_, v___x_488_, v___x_487_, v___x_488_, v___x_489_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec_ref(v___x_514_);
return v___x_515_;
}
}
else
{
lean_dec(v_a_509_);
lean_dec_ref(v_h_500_);
lean_dec(v___x_499_);
lean_dec_ref(v_params_498_);
lean_dec(v___x_497_);
lean_dec(v_v_496_);
lean_dec_ref(v_zs1_492_);
return v___x_510_;
}
}
else
{
lean_dec_ref(v_h_500_);
lean_dec(v___x_499_);
lean_dec_ref(v_params_498_);
lean_dec(v___x_497_);
lean_dec(v_v_496_);
lean_dec_ref(v_zs1_492_);
lean_dec_ref(v___f_491_);
lean_dec_ref(v_a_490_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_538_ = _args[0];
lean_object* v_ism2_539_ = _args[1];
lean_object* v_motive_540_ = _args[2];
lean_object* v___x_541_ = _args[3];
lean_object* v___x_542_ = _args[4];
lean_object* v___x_543_ = _args[5];
lean_object* v_a_544_ = _args[6];
lean_object* v___f_545_ = _args[7];
lean_object* v_zs1_546_ = _args[8];
lean_object* v_val_547_ = _args[9];
lean_object* v___x_548_ = _args[10];
lean_object* v_indName_549_ = _args[11];
lean_object* v_v_550_ = _args[12];
lean_object* v___x_551_ = _args[13];
lean_object* v_params_552_ = _args[14];
lean_object* v___x_553_ = _args[15];
lean_object* v_h_554_ = _args[16];
lean_object* v___y_555_ = _args[17];
lean_object* v___y_556_ = _args[18];
lean_object* v___y_557_ = _args[19];
lean_object* v___y_558_ = _args[20];
lean_object* v___y_559_ = _args[21];
_start:
{
uint8_t v___x_20824__boxed_560_; uint8_t v___x_20825__boxed_561_; uint8_t v___x_20826__boxed_562_; lean_object* v_res_563_; 
v___x_20824__boxed_560_ = lean_unbox(v___x_541_);
v___x_20825__boxed_561_ = lean_unbox(v___x_542_);
v___x_20826__boxed_562_ = lean_unbox(v___x_543_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_538_, v_ism2_539_, v_motive_540_, v___x_20824__boxed_560_, v___x_20825__boxed_561_, v___x_20826__boxed_562_, v_a_544_, v___f_545_, v_zs1_546_, v_val_547_, v___x_548_, v_indName_549_, v_v_550_, v___x_551_, v_params_552_, v___x_553_, v_h_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v_indName_549_);
lean_dec(v___x_548_);
lean_dec_ref(v_val_547_);
lean_dec_ref(v_ism2_539_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object* v___x_564_, lean_object* v_alts_565_, lean_object* v___x_566_, lean_object* v_zs1_567_, uint8_t v___x_568_, uint8_t v___x_569_, uint8_t v___x_570_, lean_object* v_zs2_571_, lean_object* v_x_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_578_ = lean_array_get_borrowed(v___x_564_, v_alts_565_, v___x_566_);
v___x_579_ = l_Array_append___redArg(v_zs1_567_, v_zs2_571_);
lean_inc(v___x_578_);
v___x_580_ = l_Lean_mkAppN(v___x_578_, v___x_579_);
lean_dec_ref(v___x_579_);
v___x_581_ = l_Lean_Meta_mkLambdaFVars(v_zs2_571_, v___x_580_, v___x_568_, v___x_569_, v___x_568_, v___x_569_, v___x_570_, v___y_573_, v___y_574_, v___y_575_, v___y_576_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object* v___x_582_, lean_object* v_alts_583_, lean_object* v___x_584_, lean_object* v_zs1_585_, lean_object* v___x_586_, lean_object* v___x_587_, lean_object* v___x_588_, lean_object* v_zs2_589_, lean_object* v_x_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
uint8_t v___x_20936__boxed_596_; uint8_t v___x_20937__boxed_597_; uint8_t v___x_20938__boxed_598_; lean_object* v_res_599_; 
v___x_20936__boxed_596_ = lean_unbox(v___x_586_);
v___x_20937__boxed_597_ = lean_unbox(v___x_587_);
v___x_20938__boxed_598_ = lean_unbox(v___x_588_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_582_, v_alts_583_, v___x_584_, v_zs1_585_, v___x_20936__boxed_596_, v___x_20937__boxed_597_, v___x_20938__boxed_598_, v_zs2_589_, v_x_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec_ref(v_x_590_);
lean_dec_ref(v_zs2_589_);
lean_dec(v___x_584_);
lean_dec_ref(v_alts_583_);
lean_dec_ref(v___x_582_);
return v_res_599_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_600_; lean_object* v_dummy_601_; 
v___x_600_ = lean_box(0);
v_dummy_601_ = l_Lean_Expr_sort___override(v___x_600_);
return v_dummy_601_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = lean_box(0);
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4));
v___x_610_ = l_Lean_mkConst(v___x_609_, v___x_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object* v___x_611_, lean_object* v_alts_612_, lean_object* v___x_613_, uint8_t v___x_614_, uint8_t v___x_615_, uint8_t v___x_616_, lean_object* v___x_617_, lean_object* v___x_618_, lean_object* v___x_619_, lean_object* v_ism2_620_, lean_object* v_motive_621_, lean_object* v_a_622_, lean_object* v_val_623_, lean_object* v_indName_624_, lean_object* v_v_625_, lean_object* v___x_626_, lean_object* v_params_627_, lean_object* v___x_628_, lean_object* v___x_629_, lean_object* v___x_630_, lean_object* v_zs1_631_, lean_object* v_ctorRet1_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___f_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_638_ = lean_box(v___x_614_);
v___x_639_ = lean_box(v___x_615_);
v___x_640_ = lean_box(v___x_616_);
lean_inc_ref(v_zs1_631_);
lean_inc(v___x_613_);
v___f_641_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_641_, 0, v___x_611_);
lean_closure_set(v___f_641_, 1, v_alts_612_);
lean_closure_set(v___f_641_, 2, v___x_613_);
lean_closure_set(v___f_641_, 3, v_zs1_631_);
lean_closure_set(v___f_641_, 4, v___x_638_);
lean_closure_set(v___f_641_, 5, v___x_639_);
lean_closure_set(v___f_641_, 6, v___x_640_);
v___x_642_ = l_Lean_mkAppN(v___x_617_, v_zs1_631_);
lean_inc(v___y_636_);
lean_inc_ref(v___y_635_);
lean_inc(v___y_634_);
lean_inc_ref(v___y_633_);
v___x_643_ = lean_whnf(v_ctorRet1_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v_dummy_645_; lean_object* v_nargs_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___f_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v_dummy_645_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_646_ = l_Lean_Expr_getAppNumArgs(v_a_644_);
lean_inc(v_nargs_646_);
v___x_647_ = lean_mk_array(v_nargs_646_, v_dummy_645_);
v___x_648_ = lean_nat_sub(v_nargs_646_, v___x_618_);
lean_dec(v_nargs_646_);
v___x_649_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_644_, v___x_647_, v___x_648_);
v___x_650_ = lean_array_get_size(v___x_649_);
v___x_651_ = l_Array_toSubarray___redArg(v___x_649_, v___x_619_, v___x_650_);
v___x_652_ = l_Subarray_copy___redArg(v___x_651_);
v___x_653_ = lean_array_push(v___x_652_, v___x_642_);
v___x_654_ = lean_box(v___x_614_);
v___x_655_ = lean_box(v___x_615_);
v___x_656_ = lean_box(v___x_616_);
lean_inc(v___x_618_);
v___f_657_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed), 22, 16);
lean_closure_set(v___f_657_, 0, v___x_653_);
lean_closure_set(v___f_657_, 1, v_ism2_620_);
lean_closure_set(v___f_657_, 2, v_motive_621_);
lean_closure_set(v___f_657_, 3, v___x_654_);
lean_closure_set(v___f_657_, 4, v___x_655_);
lean_closure_set(v___f_657_, 5, v___x_656_);
lean_closure_set(v___f_657_, 6, v_a_622_);
lean_closure_set(v___f_657_, 7, v___f_641_);
lean_closure_set(v___f_657_, 8, v_zs1_631_);
lean_closure_set(v___f_657_, 9, v_val_623_);
lean_closure_set(v___f_657_, 10, v___x_618_);
lean_closure_set(v___f_657_, 11, v_indName_624_);
lean_closure_set(v___f_657_, 12, v_v_625_);
lean_closure_set(v___f_657_, 13, v___x_626_);
lean_closure_set(v___f_657_, 14, v_params_627_);
lean_closure_set(v___f_657_, 15, v___x_628_);
v___x_658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2));
v___x_659_ = l_Lean_Level_ofNat(v___x_618_);
lean_dec(v___x_618_);
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = l_Lean_mkConst(v___x_658_, v___x_661_);
v___x_663_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
v___x_664_ = l_Lean_mkRawNatLit(v___x_613_);
v___x_665_ = l_Lean_mkApp3(v___x_662_, v___x_663_, v___x_629_, v___x_664_);
v___x_666_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_630_, v___x_665_, v___f_657_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
return v___x_666_;
}
else
{
lean_dec_ref(v___x_642_);
lean_dec_ref(v___f_641_);
lean_dec_ref(v_zs1_631_);
lean_dec(v___x_630_);
lean_dec_ref(v___x_629_);
lean_dec(v___x_628_);
lean_dec_ref(v_params_627_);
lean_dec(v___x_626_);
lean_dec(v_v_625_);
lean_dec(v_indName_624_);
lean_dec_ref(v_val_623_);
lean_dec_ref(v_a_622_);
lean_dec_ref(v_motive_621_);
lean_dec_ref(v_ism2_620_);
lean_dec(v___x_619_);
lean_dec(v___x_618_);
lean_dec(v___x_613_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_667_ = _args[0];
lean_object* v_alts_668_ = _args[1];
lean_object* v___x_669_ = _args[2];
lean_object* v___x_670_ = _args[3];
lean_object* v___x_671_ = _args[4];
lean_object* v___x_672_ = _args[5];
lean_object* v___x_673_ = _args[6];
lean_object* v___x_674_ = _args[7];
lean_object* v___x_675_ = _args[8];
lean_object* v_ism2_676_ = _args[9];
lean_object* v_motive_677_ = _args[10];
lean_object* v_a_678_ = _args[11];
lean_object* v_val_679_ = _args[12];
lean_object* v_indName_680_ = _args[13];
lean_object* v_v_681_ = _args[14];
lean_object* v___x_682_ = _args[15];
lean_object* v_params_683_ = _args[16];
lean_object* v___x_684_ = _args[17];
lean_object* v___x_685_ = _args[18];
lean_object* v___x_686_ = _args[19];
lean_object* v_zs1_687_ = _args[20];
lean_object* v_ctorRet1_688_ = _args[21];
lean_object* v___y_689_ = _args[22];
lean_object* v___y_690_ = _args[23];
lean_object* v___y_691_ = _args[24];
lean_object* v___y_692_ = _args[25];
lean_object* v___y_693_ = _args[26];
_start:
{
uint8_t v___x_20997__boxed_694_; uint8_t v___x_20998__boxed_695_; uint8_t v___x_20999__boxed_696_; lean_object* v_res_697_; 
v___x_20997__boxed_694_ = lean_unbox(v___x_670_);
v___x_20998__boxed_695_ = lean_unbox(v___x_671_);
v___x_20999__boxed_696_ = lean_unbox(v___x_672_);
v_res_697_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_667_, v_alts_668_, v___x_669_, v___x_20997__boxed_694_, v___x_20998__boxed_695_, v___x_20999__boxed_696_, v___x_673_, v___x_674_, v___x_675_, v_ism2_676_, v_motive_677_, v_a_678_, v_val_679_, v_indName_680_, v_v_681_, v___x_682_, v_params_683_, v___x_684_, v___x_685_, v___x_686_, v_zs1_687_, v_ctorRet1_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object* v_tail_701_, lean_object* v_params_702_, lean_object* v_alts_703_, lean_object* v___x_704_, lean_object* v_ism2_705_, lean_object* v_motive_706_, lean_object* v_val_707_, lean_object* v_indName_708_, lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v___x_711_, size_t v_sz_712_, size_t v_i_713_, lean_object* v_bs_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_lt(v_i_713_, v_sz_712_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec_ref(v___x_711_);
lean_dec(v___x_710_);
lean_dec(v___x_709_);
lean_dec(v_indName_708_);
lean_dec_ref(v_val_707_);
lean_dec_ref(v_motive_706_);
lean_dec_ref(v_ism2_705_);
lean_dec(v___x_704_);
lean_dec_ref(v_alts_703_);
lean_dec_ref(v_params_702_);
lean_dec(v_tail_701_);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v_bs_714_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; uint8_t v___x_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_v_727_; lean_object* v___x_728_; lean_object* v_bs_x27_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_722_ = l_Lean_instInhabitedExpr;
v___x_723_ = 0;
v___x_724_ = 1;
v___x_725_ = lean_unsigned_to_nat(1u);
v___x_726_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v_v_727_ = lean_array_uget(v_bs_714_, v_i_713_);
v___x_728_ = lean_unsigned_to_nat(0u);
v_bs_x27_729_ = lean_array_uset(v_bs_714_, v_i_713_, v___x_728_);
v___x_730_ = lean_usize_to_nat(v_i_713_);
lean_inc(v_tail_701_);
lean_inc(v_v_727_);
v___x_731_ = l_Lean_mkConst(v_v_727_, v_tail_701_);
v___x_732_ = l_Lean_mkAppN(v___x_731_, v_params_702_);
lean_inc(v___y_718_);
lean_inc_ref(v___y_717_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc_ref(v___x_732_);
v___x_733_ = lean_infer_type(v___x_732_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___f_738_; lean_object* v___x_739_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc_n(v_a_734_, 2);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = lean_box(v___x_723_);
v___x_736_ = lean_box(v___x_720_);
v___x_737_ = lean_box(v___x_724_);
lean_inc_ref(v___x_711_);
lean_inc(v___x_710_);
lean_inc_ref(v_params_702_);
lean_inc(v___x_709_);
lean_inc(v_indName_708_);
lean_inc_ref(v_val_707_);
lean_inc_ref(v_motive_706_);
lean_inc_ref(v_ism2_705_);
lean_inc(v___x_704_);
lean_inc_ref(v_alts_703_);
v___f_738_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed), 27, 20);
lean_closure_set(v___f_738_, 0, v___x_722_);
lean_closure_set(v___f_738_, 1, v_alts_703_);
lean_closure_set(v___f_738_, 2, v___x_730_);
lean_closure_set(v___f_738_, 3, v___x_735_);
lean_closure_set(v___f_738_, 4, v___x_736_);
lean_closure_set(v___f_738_, 5, v___x_737_);
lean_closure_set(v___f_738_, 6, v___x_732_);
lean_closure_set(v___f_738_, 7, v___x_725_);
lean_closure_set(v___f_738_, 8, v___x_704_);
lean_closure_set(v___f_738_, 9, v_ism2_705_);
lean_closure_set(v___f_738_, 10, v_motive_706_);
lean_closure_set(v___f_738_, 11, v_a_734_);
lean_closure_set(v___f_738_, 12, v_val_707_);
lean_closure_set(v___f_738_, 13, v_indName_708_);
lean_closure_set(v___f_738_, 14, v_v_727_);
lean_closure_set(v___f_738_, 15, v___x_709_);
lean_closure_set(v___f_738_, 16, v_params_702_);
lean_closure_set(v___f_738_, 17, v___x_710_);
lean_closure_set(v___f_738_, 18, v___x_711_);
lean_closure_set(v___f_738_, 19, v___x_726_);
v___x_739_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_734_, v___f_738_, v___x_723_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; size_t v___x_741_; size_t v___x_742_; lean_object* v___x_743_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = ((size_t)1ULL);
v___x_742_ = lean_usize_add(v_i_713_, v___x_741_);
v___x_743_ = lean_array_uset(v_bs_x27_729_, v_i_713_, v_a_740_);
v_i_713_ = v___x_742_;
v_bs_714_ = v___x_743_;
goto _start;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_bs_x27_729_);
lean_dec_ref(v___x_711_);
lean_dec(v___x_710_);
lean_dec(v___x_709_);
lean_dec(v_indName_708_);
lean_dec_ref(v_val_707_);
lean_dec_ref(v_motive_706_);
lean_dec_ref(v_ism2_705_);
lean_dec(v___x_704_);
lean_dec_ref(v_alts_703_);
lean_dec_ref(v_params_702_);
lean_dec(v_tail_701_);
v_a_745_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_739_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_739_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v___x_732_);
lean_dec(v___x_730_);
lean_dec_ref(v_bs_x27_729_);
lean_dec(v_v_727_);
lean_dec_ref(v___x_711_);
lean_dec(v___x_710_);
lean_dec(v___x_709_);
lean_dec(v_indName_708_);
lean_dec_ref(v_val_707_);
lean_dec_ref(v_motive_706_);
lean_dec_ref(v_ism2_705_);
lean_dec(v___x_704_);
lean_dec_ref(v_alts_703_);
lean_dec_ref(v_params_702_);
lean_dec(v_tail_701_);
v_a_753_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_733_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_733_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_tail_761_ = _args[0];
lean_object* v_params_762_ = _args[1];
lean_object* v_alts_763_ = _args[2];
lean_object* v___x_764_ = _args[3];
lean_object* v_ism2_765_ = _args[4];
lean_object* v_motive_766_ = _args[5];
lean_object* v_val_767_ = _args[6];
lean_object* v_indName_768_ = _args[7];
lean_object* v___x_769_ = _args[8];
lean_object* v___x_770_ = _args[9];
lean_object* v___x_771_ = _args[10];
lean_object* v_sz_772_ = _args[11];
lean_object* v_i_773_ = _args[12];
lean_object* v_bs_774_ = _args[13];
lean_object* v___y_775_ = _args[14];
lean_object* v___y_776_ = _args[15];
lean_object* v___y_777_ = _args[16];
lean_object* v___y_778_ = _args[17];
lean_object* v___y_779_ = _args[18];
_start:
{
size_t v_sz_boxed_780_; size_t v_i_boxed_781_; lean_object* v_res_782_; 
v_sz_boxed_780_ = lean_unbox_usize(v_sz_772_);
lean_dec(v_sz_772_);
v_i_boxed_781_ = lean_unbox_usize(v_i_773_);
lean_dec(v_i_773_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_761_, v_params_762_, v_alts_763_, v___x_764_, v_ism2_765_, v_motive_766_, v_val_767_, v_indName_768_, v___x_769_, v___x_770_, v___x_771_, v_sz_boxed_780_, v_i_boxed_781_, v_bs_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_783_, lean_object* v___x_784_, lean_object* v_a_785_, lean_object* v_ism1_786_, uint8_t v___x_787_, uint8_t v___x_788_, uint8_t v___x_789_, lean_object* v_name_790_, lean_object* v___x_791_, lean_object* v_params_792_, lean_object* v___x_793_, lean_object* v_tail_794_, lean_object* v_alts_795_, lean_object* v_numParams_796_, lean_object* v_ism2_797_, lean_object* v_val_798_, lean_object* v_indName_799_, lean_object* v___x_800_, lean_object* v___x_801_, lean_object* v___x_802_, lean_object* v_heq_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_inc_ref(v_motive_783_);
v___x_809_ = l_Lean_mkAppN(v_motive_783_, v___x_784_);
v___x_810_ = l_Lean_mkArrow(v_a_785_, v___x_809_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; lean_object* v___x_812_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref_known(v___x_810_, 1);
v___x_812_ = l_Lean_Meta_mkLambdaFVars(v_ism1_786_, v_a_811_, v___x_787_, v___x_788_, v___x_787_, v___x_788_, v___x_789_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; size_t v_sz_818_; size_t v___x_819_; lean_object* v___x_820_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
lean_inc(v___x_791_);
v___x_814_ = l_Lean_mkConst(v_name_790_, v___x_791_);
v___x_815_ = l_Lean_mkAppN(v___x_814_, v_params_792_);
v___x_816_ = l_Lean_Expr_app___override(v___x_815_, v_a_813_);
v___x_817_ = l_Lean_mkAppN(v___x_816_, v_ism1_786_);
v_sz_818_ = lean_array_size(v___x_793_);
v___x_819_ = ((size_t)0ULL);
lean_inc_ref(v_motive_783_);
lean_inc_ref(v_ism2_797_);
lean_inc_ref(v_alts_795_);
lean_inc_ref(v_params_792_);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_794_, v_params_792_, v_alts_795_, v_numParams_796_, v_ism2_797_, v_motive_783_, v_val_798_, v_indName_799_, v___x_791_, v___x_800_, v___x_801_, v_sz_818_, v___x_819_, v___x_793_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_a_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_821_);
lean_dec_ref_known(v___x_820_, 1);
v___x_822_ = l_Lean_mkAppN(v___x_817_, v_a_821_);
lean_dec(v_a_821_);
lean_inc_ref(v_heq_803_);
v___x_823_ = l_Lean_Meta_mkEqSymm(v_heq_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_825_ = l_Lean_Expr_app___override(v___x_822_, v_a_824_);
v___x_826_ = lean_mk_empty_array_with_capacity(v___x_802_);
lean_inc_ref(v___x_826_);
v___x_827_ = lean_array_push(v___x_826_, v_motive_783_);
v___x_828_ = l_Array_append___redArg(v_params_792_, v___x_827_);
lean_dec_ref(v___x_827_);
v___x_829_ = l_Array_append___redArg(v___x_828_, v_ism1_786_);
v___x_830_ = l_Array_append___redArg(v___x_829_, v_ism2_797_);
lean_dec_ref(v_ism2_797_);
v___x_831_ = lean_array_push(v___x_826_, v_heq_803_);
v___x_832_ = l_Array_append___redArg(v___x_830_, v___x_831_);
lean_dec_ref(v___x_831_);
v___x_833_ = l_Array_append___redArg(v___x_832_, v_alts_795_);
lean_dec_ref(v_alts_795_);
v___x_834_ = l_Lean_Meta_mkLambdaFVars(v___x_833_, v___x_825_, v___x_787_, v___x_788_, v___x_787_, v___x_788_, v___x_789_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
lean_dec_ref(v___x_833_);
return v___x_834_;
}
else
{
lean_dec_ref(v___x_822_);
lean_dec_ref(v_heq_803_);
lean_dec_ref(v_ism2_797_);
lean_dec_ref(v_alts_795_);
lean_dec_ref(v_params_792_);
lean_dec_ref(v_motive_783_);
return v___x_823_;
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec_ref(v___x_817_);
lean_dec_ref(v_heq_803_);
lean_dec_ref(v_ism2_797_);
lean_dec_ref(v_alts_795_);
lean_dec_ref(v_params_792_);
lean_dec_ref(v_motive_783_);
v_a_835_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_820_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_820_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_dec_ref(v_heq_803_);
lean_dec_ref(v___x_801_);
lean_dec(v___x_800_);
lean_dec(v_indName_799_);
lean_dec_ref(v_val_798_);
lean_dec_ref(v_ism2_797_);
lean_dec(v_numParams_796_);
lean_dec_ref(v_alts_795_);
lean_dec(v_tail_794_);
lean_dec_ref(v___x_793_);
lean_dec_ref(v_params_792_);
lean_dec(v___x_791_);
lean_dec(v_name_790_);
lean_dec_ref(v_motive_783_);
return v___x_812_;
}
}
else
{
lean_dec_ref(v_heq_803_);
lean_dec_ref(v___x_801_);
lean_dec(v___x_800_);
lean_dec(v_indName_799_);
lean_dec_ref(v_val_798_);
lean_dec_ref(v_ism2_797_);
lean_dec(v_numParams_796_);
lean_dec_ref(v_alts_795_);
lean_dec(v_tail_794_);
lean_dec_ref(v___x_793_);
lean_dec_ref(v_params_792_);
lean_dec(v___x_791_);
lean_dec(v_name_790_);
lean_dec_ref(v_motive_783_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object** _args){
lean_object* v_motive_843_ = _args[0];
lean_object* v___x_844_ = _args[1];
lean_object* v_a_845_ = _args[2];
lean_object* v_ism1_846_ = _args[3];
lean_object* v___x_847_ = _args[4];
lean_object* v___x_848_ = _args[5];
lean_object* v___x_849_ = _args[6];
lean_object* v_name_850_ = _args[7];
lean_object* v___x_851_ = _args[8];
lean_object* v_params_852_ = _args[9];
lean_object* v___x_853_ = _args[10];
lean_object* v_tail_854_ = _args[11];
lean_object* v_alts_855_ = _args[12];
lean_object* v_numParams_856_ = _args[13];
lean_object* v_ism2_857_ = _args[14];
lean_object* v_val_858_ = _args[15];
lean_object* v_indName_859_ = _args[16];
lean_object* v___x_860_ = _args[17];
lean_object* v___x_861_ = _args[18];
lean_object* v___x_862_ = _args[19];
lean_object* v_heq_863_ = _args[20];
lean_object* v___y_864_ = _args[21];
lean_object* v___y_865_ = _args[22];
lean_object* v___y_866_ = _args[23];
lean_object* v___y_867_ = _args[24];
lean_object* v___y_868_ = _args[25];
_start:
{
uint8_t v___x_21239__boxed_869_; uint8_t v___x_21240__boxed_870_; uint8_t v___x_21241__boxed_871_; lean_object* v_res_872_; 
v___x_21239__boxed_869_ = lean_unbox(v___x_847_);
v___x_21240__boxed_870_ = lean_unbox(v___x_848_);
v___x_21241__boxed_871_ = lean_unbox(v___x_849_);
v_res_872_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_843_, v___x_844_, v_a_845_, v_ism1_846_, v___x_21239__boxed_869_, v___x_21240__boxed_870_, v___x_21241__boxed_871_, v_name_850_, v___x_851_, v_params_852_, v___x_853_, v_tail_854_, v_alts_855_, v_numParams_856_, v_ism2_857_, v_val_858_, v_indName_859_, v___x_860_, v___x_861_, v___x_862_, v_heq_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec_ref(v___y_864_);
lean_dec(v___x_862_);
lean_dec_ref(v_ism1_846_);
lean_dec_ref(v___x_844_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_873_, lean_object* v_tail_874_, lean_object* v_params_875_, lean_object* v_ism1_876_, lean_object* v_ism2_877_, lean_object* v_motive_878_, lean_object* v___x_879_, uint8_t v___x_880_, uint8_t v___x_881_, uint8_t v___x_882_, lean_object* v_name_883_, lean_object* v___x_884_, lean_object* v___x_885_, lean_object* v_numParams_886_, lean_object* v_val_887_, lean_object* v___x_888_, lean_object* v___x_889_, lean_object* v_alts_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
lean_inc(v_indName_873_);
v___x_896_ = l_Lean_mkCtorIdxName(v_indName_873_);
lean_inc(v_tail_874_);
v___x_897_ = l_Lean_mkConst(v___x_896_, v_tail_874_);
lean_inc_ref_n(v_params_875_, 2);
v___x_898_ = l_Array_append___redArg(v_params_875_, v_ism1_876_);
lean_inc_ref(v___x_897_);
v___x_899_ = l_Lean_mkAppN(v___x_897_, v___x_898_);
lean_dec_ref(v___x_898_);
v___x_900_ = l_Array_append___redArg(v_params_875_, v_ism2_877_);
v___x_901_ = l_Lean_mkAppN(v___x_897_, v___x_900_);
lean_dec_ref(v___x_900_);
lean_inc_ref(v___x_901_);
lean_inc_ref(v___x_899_);
v___x_902_ = l_Lean_Meta_mkEq(v___x_899_, v___x_901_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref_known(v___x_902_, 1);
lean_inc_ref(v___x_901_);
v___x_904_ = l_Lean_Meta_mkEq(v___x_901_, v___x_899_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = lean_box(v___x_880_);
v___x_907_ = lean_box(v___x_881_);
v___x_908_ = lean_box(v___x_882_);
v___f_909_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__0___boxed), 26, 20);
lean_closure_set(v___f_909_, 0, v_motive_878_);
lean_closure_set(v___f_909_, 1, v___x_879_);
lean_closure_set(v___f_909_, 2, v_a_905_);
lean_closure_set(v___f_909_, 3, v_ism1_876_);
lean_closure_set(v___f_909_, 4, v___x_906_);
lean_closure_set(v___f_909_, 5, v___x_907_);
lean_closure_set(v___f_909_, 6, v___x_908_);
lean_closure_set(v___f_909_, 7, v_name_883_);
lean_closure_set(v___f_909_, 8, v___x_884_);
lean_closure_set(v___f_909_, 9, v_params_875_);
lean_closure_set(v___f_909_, 10, v___x_885_);
lean_closure_set(v___f_909_, 11, v_tail_874_);
lean_closure_set(v___f_909_, 12, v_alts_890_);
lean_closure_set(v___f_909_, 13, v_numParams_886_);
lean_closure_set(v___f_909_, 14, v_ism2_877_);
lean_closure_set(v___f_909_, 15, v_val_887_);
lean_closure_set(v___f_909_, 16, v_indName_873_);
lean_closure_set(v___f_909_, 17, v___x_888_);
lean_closure_set(v___f_909_, 18, v___x_901_);
lean_closure_set(v___f_909_, 19, v___x_889_);
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_911_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_910_, v_a_903_, v___f_909_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_911_;
}
else
{
lean_dec(v_a_903_);
lean_dec_ref(v___x_901_);
lean_dec_ref(v_alts_890_);
lean_dec(v___x_889_);
lean_dec(v___x_888_);
lean_dec_ref(v_val_887_);
lean_dec(v_numParams_886_);
lean_dec_ref(v___x_885_);
lean_dec(v___x_884_);
lean_dec(v_name_883_);
lean_dec_ref(v___x_879_);
lean_dec_ref(v_motive_878_);
lean_dec_ref(v_ism2_877_);
lean_dec_ref(v_ism1_876_);
lean_dec_ref(v_params_875_);
lean_dec(v_tail_874_);
lean_dec(v_indName_873_);
return v___x_904_;
}
}
else
{
lean_dec_ref(v___x_901_);
lean_dec_ref(v___x_899_);
lean_dec_ref(v_alts_890_);
lean_dec(v___x_889_);
lean_dec(v___x_888_);
lean_dec_ref(v_val_887_);
lean_dec(v_numParams_886_);
lean_dec_ref(v___x_885_);
lean_dec(v___x_884_);
lean_dec(v_name_883_);
lean_dec_ref(v___x_879_);
lean_dec_ref(v_motive_878_);
lean_dec_ref(v_ism2_877_);
lean_dec_ref(v_ism1_876_);
lean_dec_ref(v_params_875_);
lean_dec(v_tail_874_);
lean_dec(v_indName_873_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object** _args){
lean_object* v_indName_912_ = _args[0];
lean_object* v_tail_913_ = _args[1];
lean_object* v_params_914_ = _args[2];
lean_object* v_ism1_915_ = _args[3];
lean_object* v_ism2_916_ = _args[4];
lean_object* v_motive_917_ = _args[5];
lean_object* v___x_918_ = _args[6];
lean_object* v___x_919_ = _args[7];
lean_object* v___x_920_ = _args[8];
lean_object* v___x_921_ = _args[9];
lean_object* v_name_922_ = _args[10];
lean_object* v___x_923_ = _args[11];
lean_object* v___x_924_ = _args[12];
lean_object* v_numParams_925_ = _args[13];
lean_object* v_val_926_ = _args[14];
lean_object* v___x_927_ = _args[15];
lean_object* v___x_928_ = _args[16];
lean_object* v_alts_929_ = _args[17];
lean_object* v___y_930_ = _args[18];
lean_object* v___y_931_ = _args[19];
lean_object* v___y_932_ = _args[20];
lean_object* v___y_933_ = _args[21];
lean_object* v___y_934_ = _args[22];
_start:
{
uint8_t v___x_21362__boxed_935_; uint8_t v___x_21363__boxed_936_; uint8_t v___x_21364__boxed_937_; lean_object* v_res_938_; 
v___x_21362__boxed_935_ = lean_unbox(v___x_919_);
v___x_21363__boxed_936_ = lean_unbox(v___x_920_);
v___x_21364__boxed_937_ = lean_unbox(v___x_921_);
v_res_938_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_912_, v_tail_913_, v_params_914_, v_ism1_915_, v_ism2_916_, v_motive_917_, v___x_918_, v___x_21362__boxed_935_, v___x_21363__boxed_936_, v___x_21364__boxed_937_, v_name_922_, v___x_923_, v___x_924_, v_numParams_925_, v_val_926_, v___x_927_, v___x_928_, v_alts_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_939_, lean_object* v_x_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_snd_939_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_947_, lean_object* v_x_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_947_, v_x_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec_ref(v_x_948_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_955_, size_t v_i_956_, lean_object* v_bs_957_){
_start:
{
uint8_t v___x_958_; 
v___x_958_ = lean_usize_dec_lt(v_i_956_, v_sz_955_);
if (v___x_958_ == 0)
{
return v_bs_957_;
}
else
{
lean_object* v_v_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_975_; 
v_v_959_ = lean_array_uget(v_bs_957_, v_i_956_);
v_fst_960_ = lean_ctor_get(v_v_959_, 0);
v_snd_961_ = lean_ctor_get(v_v_959_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_v_959_);
if (v_isSharedCheck_975_ == 0)
{
v___x_963_ = v_v_959_;
v_isShared_964_ = v_isSharedCheck_975_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_snd_961_);
lean_inc(v_fst_960_);
lean_dec(v_v_959_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_975_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_965_; lean_object* v_bs_x27_966_; lean_object* v___f_967_; lean_object* v___x_969_; 
v___x_965_ = lean_unsigned_to_nat(0u);
v_bs_x27_966_ = lean_array_uset(v_bs_957_, v_i_956_, v___x_965_);
v___f_967_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_967_, 0, v_snd_961_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 1, v___f_967_);
v___x_969_ = v___x_963_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v_fst_960_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v___f_967_);
v___x_969_ = v_reuseFailAlloc_974_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
size_t v___x_970_; size_t v___x_971_; lean_object* v___x_972_; 
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_add(v_i_956_, v___x_970_);
v___x_972_ = lean_array_uset(v_bs_x27_966_, v_i_956_, v___x_969_);
v_i_956_ = v___x_971_;
v_bs_957_ = v___x_972_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_976_, lean_object* v_i_977_, lean_object* v_bs_978_){
_start:
{
size_t v_sz_boxed_979_; size_t v_i_boxed_980_; lean_object* v_res_981_; 
v_sz_boxed_979_ = lean_unbox_usize(v_sz_976_);
lean_dec(v_sz_976_);
v_i_boxed_980_ = lean_unbox_usize(v_i_977_);
lean_dec(v_i_977_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_979_, v_i_boxed_980_, v_bs_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object* v___x_982_, lean_object* v___x_983_, lean_object* v_a_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_){
_start:
{
lean_object* v___x_20237__overap_990_; lean_object* v___x_991_; 
v___x_20237__overap_990_ = l_instInhabitedOfMonad___redArg(v___x_982_, v___x_983_);
lean_inc(v___y_988_);
lean_inc_ref(v___y_987_);
lean_inc(v___y_986_);
lean_inc_ref(v___y_985_);
v___x_991_ = lean_apply_5(v___x_20237__overap_990_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, lean_box(0));
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object* v___x_992_, lean_object* v___x_993_, lean_object* v_a_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_992_, v___x_993_, v_a_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec_ref(v_a_994_);
return v_res_1000_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_instMonadEIO___redArg();
return v___x_1001_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0);
v___x_1003_ = l_StateRefT_x27_instMonad___redArg(v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object* v_acc_1008_, lean_object* v_declInfos_1009_, lean_object* v_k_1010_, lean_object* v_kind_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
uint8_t v_kind_boxed_1018_; lean_object* v_res_1019_; 
v_kind_boxed_1018_ = lean_unbox(v_kind_1011_);
v_res_1019_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_1008_, v_declInfos_1009_, v_k_1010_, v_kind_boxed_1018_, v_x_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_declInfos_1020_, lean_object* v_k_1021_, uint8_t v_kind_1022_, lean_object* v_acc_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v_toApplicative_1030_; lean_object* v_toFunctor_1031_; lean_object* v_toSeq_1032_; lean_object* v_toSeqLeft_1033_; lean_object* v_toSeqRight_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___f_1037_; lean_object* v___f_1038_; lean_object* v___x_1039_; lean_object* v___f_1040_; lean_object* v___f_1041_; lean_object* v___f_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v_toApplicative_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1096_; 
v___x_1029_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_1030_ = lean_ctor_get(v___x_1029_, 0);
v_toFunctor_1031_ = lean_ctor_get(v_toApplicative_1030_, 0);
v_toSeq_1032_ = lean_ctor_get(v_toApplicative_1030_, 2);
v_toSeqLeft_1033_ = lean_ctor_get(v_toApplicative_1030_, 3);
v_toSeqRight_1034_ = lean_ctor_get(v_toApplicative_1030_, 4);
v___f_1035_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_1036_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_1031_, 2);
v___f_1037_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1037_, 0, v_toFunctor_1031_);
v___f_1038_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1038_, 0, v_toFunctor_1031_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___f_1037_);
lean_ctor_set(v___x_1039_, 1, v___f_1038_);
lean_inc(v_toSeqRight_1034_);
v___f_1040_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1040_, 0, v_toSeqRight_1034_);
lean_inc(v_toSeqLeft_1033_);
v___f_1041_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1041_, 0, v_toSeqLeft_1033_);
lean_inc(v_toSeq_1032_);
v___f_1042_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1042_, 0, v_toSeq_1032_);
v___x_1043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1039_);
lean_ctor_set(v___x_1043_, 1, v___f_1035_);
lean_ctor_set(v___x_1043_, 2, v___f_1042_);
lean_ctor_set(v___x_1043_, 3, v___f_1041_);
lean_ctor_set(v___x_1043_, 4, v___f_1040_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___f_1036_);
v___x_1045_ = l_StateRefT_x27_instMonad___redArg(v___x_1044_);
v_toApplicative_1046_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v___x_1045_, 1);
lean_dec(v_unused_1097_);
v___x_1048_ = v___x_1045_;
v_isShared_1049_ = v_isSharedCheck_1096_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_toApplicative_1046_);
lean_dec(v___x_1045_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1096_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_toFunctor_1050_; lean_object* v_toSeq_1051_; lean_object* v_toSeqLeft_1052_; lean_object* v_toSeqRight_1053_; lean_object* v___x_1055_; uint8_t v_isShared_1056_; uint8_t v_isSharedCheck_1094_; 
v_toFunctor_1050_ = lean_ctor_get(v_toApplicative_1046_, 0);
v_toSeq_1051_ = lean_ctor_get(v_toApplicative_1046_, 2);
v_toSeqLeft_1052_ = lean_ctor_get(v_toApplicative_1046_, 3);
v_toSeqRight_1053_ = lean_ctor_get(v_toApplicative_1046_, 4);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_toApplicative_1046_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v_toApplicative_1046_, 1);
lean_dec(v_unused_1095_);
v___x_1055_ = v_toApplicative_1046_;
v_isShared_1056_ = v_isSharedCheck_1094_;
goto v_resetjp_1054_;
}
else
{
lean_inc(v_toSeqRight_1053_);
lean_inc(v_toSeqLeft_1052_);
lean_inc(v_toSeq_1051_);
lean_inc(v_toFunctor_1050_);
lean_dec(v_toApplicative_1046_);
v___x_1055_ = lean_box(0);
v_isShared_1056_ = v_isSharedCheck_1094_;
goto v_resetjp_1054_;
}
v_resetjp_1054_:
{
lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___f_1059_; lean_object* v___f_1060_; lean_object* v___x_1061_; lean_object* v___f_1062_; lean_object* v___f_1063_; lean_object* v___f_1064_; lean_object* v___x_1066_; 
v___f_1057_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_1058_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_1050_);
v___f_1059_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1059_, 0, v_toFunctor_1050_);
v___f_1060_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1060_, 0, v_toFunctor_1050_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___f_1059_);
lean_ctor_set(v___x_1061_, 1, v___f_1060_);
v___f_1062_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1062_, 0, v_toSeqRight_1053_);
v___f_1063_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1063_, 0, v_toSeqLeft_1052_);
v___f_1064_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1064_, 0, v_toSeq_1051_);
if (v_isShared_1056_ == 0)
{
lean_ctor_set(v___x_1055_, 4, v___f_1062_);
lean_ctor_set(v___x_1055_, 3, v___f_1063_);
lean_ctor_set(v___x_1055_, 2, v___f_1064_);
lean_ctor_set(v___x_1055_, 1, v___f_1057_);
lean_ctor_set(v___x_1055_, 0, v___x_1061_);
v___x_1066_ = v___x_1055_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v___f_1057_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v___f_1064_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v___f_1063_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v___f_1062_);
v___x_1066_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v___f_1058_);
lean_ctor_set(v___x_1048_, 0, v___x_1066_);
v___x_1068_ = v___x_1048_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v___f_1058_);
v___x_1068_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1069_ = lean_array_get_size(v_acc_1023_);
v___x_1070_ = lean_array_get_size(v_declInfos_1020_);
v___x_1071_ = lean_nat_dec_lt(v___x_1069_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; 
lean_dec_ref(v___x_1068_);
lean_dec_ref(v_declInfos_1020_);
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1024_);
v___x_1072_ = lean_apply_6(v_k_1021_, v_acc_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, lean_box(0));
return v___x_1072_;
}
else
{
lean_object* v___x_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___f_1076_; lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v_snd_1082_; lean_object* v_fst_1083_; lean_object* v_fst_1084_; lean_object* v_snd_1085_; lean_object* v___x_1086_; lean_object* v___f_1087_; lean_object* v___x_1088_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = 0;
v___x_1075_ = l_Lean_instInhabitedExpr;
v___f_1076_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1076_, 0, v___x_1068_);
lean_closure_set(v___f_1076_, 1, v___x_1075_);
v___f_1077_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1077_, 0, v___f_1076_);
v___x_1078_ = lean_box(v___x_1074_);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___f_1077_);
v___x_1080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1073_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_array_get(v___x_1080_, v_declInfos_1020_, v___x_1069_);
lean_dec_ref_known(v___x_1080_, 2);
v_snd_1082_ = lean_ctor_get(v___x_1081_, 1);
lean_inc(v_snd_1082_);
v_fst_1083_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_fst_1083_);
lean_dec(v___x_1081_);
v_fst_1084_ = lean_ctor_get(v_snd_1082_, 0);
lean_inc(v_fst_1084_);
v_snd_1085_ = lean_ctor_get(v_snd_1082_, 1);
lean_inc(v_snd_1085_);
lean_dec(v_snd_1082_);
v___x_1086_ = lean_box(v_kind_1022_);
lean_inc_ref(v_acc_1023_);
v___f_1087_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1087_, 0, v_acc_1023_);
lean_closure_set(v___f_1087_, 1, v_declInfos_1020_);
lean_closure_set(v___f_1087_, 2, v_k_1021_);
lean_closure_set(v___f_1087_, 3, v___x_1086_);
lean_inc(v___y_1027_);
lean_inc_ref(v___y_1026_);
lean_inc(v___y_1025_);
lean_inc_ref(v___y_1024_);
v___x_1088_ = lean_apply_6(v_snd_1085_, v_acc_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, lean_box(0));
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; uint8_t v___x_1090_; lean_object* v___x_1091_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = lean_unbox(v_fst_1084_);
lean_dec(v_fst_1084_);
v___x_1091_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1083_, v___x_1090_, v_a_1089_, v___f_1087_, v_kind_1022_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
return v___x_1091_;
}
else
{
lean_dec_ref(v___f_1087_);
lean_dec(v_fst_1084_);
lean_dec(v_fst_1083_);
return v___x_1088_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(lean_object* v_acc_1098_, lean_object* v_declInfos_1099_, lean_object* v_k_1100_, uint8_t v_kind_1101_, lean_object* v_x_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_array_push(v_acc_1098_, v_x_1102_);
v___x_1109_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1099_, v_k_1100_, v_kind_1101_, v___x_1108_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object* v_declInfos_1110_, lean_object* v_k_1111_, lean_object* v_kind_1112_, lean_object* v_acc_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v_kind_boxed_1119_; lean_object* v_res_1120_; 
v_kind_boxed_1119_ = lean_unbox(v_kind_1112_);
v_res_1120_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1110_, v_k_1111_, v_kind_boxed_1119_, v_acc_1113_, v___y_1114_, v___y_1115_, v___y_1116_, v___y_1117_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
lean_dec_ref(v___y_1114_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object* v_declInfos_1123_, lean_object* v_k_1124_, uint8_t v_kind_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_1132_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1123_, v_k_1124_, v_kind_1125_, v___x_1131_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object* v_declInfos_1133_, lean_object* v_k_1134_, lean_object* v_kind_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v_kind_boxed_1141_; lean_object* v_res_1142_; 
v_kind_boxed_1141_ = lean_unbox(v_kind_1135_);
v_res_1142_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_declInfos_1133_, v_k_1134_, v_kind_boxed_1141_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t v_sz_1143_, size_t v_i_1144_, lean_object* v_bs_1145_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_usize_dec_lt(v_i_1144_, v_sz_1143_);
if (v___x_1146_ == 0)
{
return v_bs_1145_;
}
else
{
lean_object* v_v_1147_; lean_object* v_fst_1148_; lean_object* v_snd_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1165_; 
v_v_1147_ = lean_array_uget(v_bs_1145_, v_i_1144_);
v_fst_1148_ = lean_ctor_get(v_v_1147_, 0);
v_snd_1149_ = lean_ctor_get(v_v_1147_, 1);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_v_1147_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1151_ = v_v_1147_;
v_isShared_1152_ = v_isSharedCheck_1165_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_snd_1149_);
lean_inc(v_fst_1148_);
lean_dec(v_v_1147_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1165_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v_bs_x27_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1153_ = lean_unsigned_to_nat(0u);
v_bs_x27_1154_ = lean_array_uset(v_bs_1145_, v_i_1144_, v___x_1153_);
v___x_1155_ = 0;
v___x_1156_ = lean_box(v___x_1155_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1156_);
v___x_1158_ = v___x_1151_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_snd_1149_);
v___x_1158_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; size_t v___x_1160_; size_t v___x_1161_; lean_object* v___x_1162_; 
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_fst_1148_);
lean_ctor_set(v___x_1159_, 1, v___x_1158_);
v___x_1160_ = ((size_t)1ULL);
v___x_1161_ = lean_usize_add(v_i_1144_, v___x_1160_);
v___x_1162_ = lean_array_uset(v_bs_x27_1154_, v_i_1144_, v___x_1159_);
v_i_1144_ = v___x_1161_;
v_bs_1145_ = v___x_1162_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_sz_1166_, lean_object* v_i_1167_, lean_object* v_bs_1168_){
_start:
{
size_t v_sz_boxed_1169_; size_t v_i_boxed_1170_; lean_object* v_res_1171_; 
v_sz_boxed_1169_ = lean_unbox_usize(v_sz_1166_);
lean_dec(v_sz_1166_);
v_i_boxed_1170_ = lean_unbox_usize(v_i_1167_);
lean_dec(v_i_1167_);
v_res_1171_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_1169_, v_i_boxed_1170_, v_bs_1168_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_declInfos_1172_, lean_object* v_k_1173_, uint8_t v_kind_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
size_t v_sz_1180_; size_t v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v_sz_1180_ = lean_array_size(v_declInfos_1172_);
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1180_, v___x_1181_, v_declInfos_1172_);
v___x_1183_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v___x_1182_, v_k_1173_, v_kind_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_declInfos_1184_, lean_object* v_k_1185_, lean_object* v_kind_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v_kind_boxed_1192_; lean_object* v_res_1193_; 
v_kind_boxed_1192_ = lean_unbox(v_kind_1186_);
v_res_1193_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1184_, v_k_1185_, v_kind_boxed_1192_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_declInfos_1194_, lean_object* v_k_1195_, uint8_t v_kind_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
size_t v_sz_1202_; size_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_sz_1202_ = lean_array_size(v_declInfos_1194_);
v___x_1203_ = ((size_t)0ULL);
v___x_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1202_, v___x_1203_, v_declInfos_1194_);
v___x_1205_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_1204_, v_k_1195_, v_kind_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_declInfos_1206_, lean_object* v_k_1207_, lean_object* v_kind_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
uint8_t v_kind_boxed_1214_; lean_object* v_res_1215_; 
v_kind_boxed_1214_ = lean_unbox(v_kind_1208_);
v_res_1215_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1206_, v_k_1207_, v_kind_boxed_1214_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_1217_, lean_object* v_dummy_1218_, lean_object* v___x_1219_, lean_object* v___x_1220_, lean_object* v___x_1221_, lean_object* v_motive_1222_, lean_object* v_zs1_1223_, uint8_t v___x_1224_, uint8_t v___x_1225_, uint8_t v___x_1226_, lean_object* v_v_1227_, lean_object* v___x_1228_, lean_object* v_zs2_1229_, lean_object* v_ctorRet2_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = l_Lean_mkAppN(v___x_1217_, v_zs2_1229_);
lean_inc(v___y_1234_);
lean_inc_ref(v___y_1233_);
lean_inc(v___y_1232_);
lean_inc_ref(v___y_1231_);
v___x_1237_ = lean_whnf(v_ctorRet2_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v_nargs_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v_nargs_1239_ = l_Lean_Expr_getAppNumArgs(v_a_1238_);
lean_inc(v_nargs_1239_);
v___x_1240_ = lean_mk_array(v_nargs_1239_, v_dummy_1218_);
v___x_1241_ = lean_nat_sub(v_nargs_1239_, v___x_1219_);
lean_dec(v_nargs_1239_);
v___x_1242_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1238_, v___x_1240_, v___x_1241_);
v___x_1243_ = lean_array_get_size(v___x_1242_);
v___x_1244_ = l_Array_toSubarray___redArg(v___x_1242_, v___x_1220_, v___x_1243_);
v___x_1245_ = l_Subarray_copy___redArg(v___x_1244_);
v___x_1246_ = lean_array_push(v___x_1245_, v___x_1236_);
v___x_1247_ = l_Array_append___redArg(v___x_1221_, v___x_1246_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = l_Lean_mkAppN(v_motive_1222_, v___x_1247_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = l_Array_append___redArg(v_zs1_1223_, v_zs2_1229_);
v___x_1250_ = l_Lean_Meta_mkForallFVars(v___x_1249_, v___x_1248_, v___x_1224_, v___x_1225_, v___x_1225_, v___x_1226_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
lean_dec_ref(v___x_1249_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1270_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1270_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1270_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___y_1256_; 
if (lean_obj_tag(v_v_1227_) == 1)
{
lean_object* v_str_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_str_1261_ = lean_ctor_get(v_v_1227_, 1);
lean_inc_ref(v_str_1261_);
lean_dec_ref_known(v_v_1227_, 2);
v___x_1262_ = lean_box(0);
v___x_1263_ = l_Lean_Name_str___override(v___x_1262_, v_str_1261_);
v___y_1256_ = v___x_1263_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
lean_dec(v_v_1227_);
v___x_1264_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_1265_ = lean_nat_add(v___x_1228_, v___x_1219_);
v___x_1266_ = l_Nat_reprFast(v___x_1265_);
v___x_1267_ = lean_string_append(v___x_1264_, v___x_1266_);
lean_dec_ref(v___x_1266_);
v___x_1268_ = lean_box(0);
v___x_1269_ = l_Lean_Name_str___override(v___x_1268_, v___x_1267_);
v___y_1256_ = v___x_1269_;
goto v___jp_1255_;
}
v___jp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___y_1256_);
lean_ctor_set(v___x_1257_, 1, v_a_1251_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 0, v___x_1257_);
v___x_1259_ = v___x_1253_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1257_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_a_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1278_; 
lean_dec(v_v_1227_);
v_a_1271_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1273_ = v___x_1250_;
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_a_1271_);
lean_dec(v___x_1250_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1278_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1276_; 
if (v_isShared_1274_ == 0)
{
v___x_1276_ = v___x_1273_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1271_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1286_; 
lean_dec_ref(v___x_1236_);
lean_dec(v_v_1227_);
lean_dec_ref(v_zs1_1223_);
lean_dec_ref(v_motive_1222_);
lean_dec_ref(v___x_1221_);
lean_dec(v___x_1220_);
lean_dec_ref(v_dummy_1218_);
v_a_1279_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1281_ = v___x_1237_;
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_a_1279_);
lean_dec(v___x_1237_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1286_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1284_; 
if (v_isShared_1282_ == 0)
{
v___x_1284_ = v___x_1281_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1279_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1287_ = _args[0];
lean_object* v_dummy_1288_ = _args[1];
lean_object* v___x_1289_ = _args[2];
lean_object* v___x_1290_ = _args[3];
lean_object* v___x_1291_ = _args[4];
lean_object* v_motive_1292_ = _args[5];
lean_object* v_zs1_1293_ = _args[6];
lean_object* v___x_1294_ = _args[7];
lean_object* v___x_1295_ = _args[8];
lean_object* v___x_1296_ = _args[9];
lean_object* v_v_1297_ = _args[10];
lean_object* v___x_1298_ = _args[11];
lean_object* v_zs2_1299_ = _args[12];
lean_object* v_ctorRet2_1300_ = _args[13];
lean_object* v___y_1301_ = _args[14];
lean_object* v___y_1302_ = _args[15];
lean_object* v___y_1303_ = _args[16];
lean_object* v___y_1304_ = _args[17];
lean_object* v___y_1305_ = _args[18];
_start:
{
uint8_t v___x_21801__boxed_1306_; uint8_t v___x_21802__boxed_1307_; uint8_t v___x_21803__boxed_1308_; lean_object* v_res_1309_; 
v___x_21801__boxed_1306_ = lean_unbox(v___x_1294_);
v___x_21802__boxed_1307_ = lean_unbox(v___x_1295_);
v___x_21803__boxed_1308_ = lean_unbox(v___x_1296_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1287_, v_dummy_1288_, v___x_1289_, v___x_1290_, v___x_1291_, v_motive_1292_, v_zs1_1293_, v___x_21801__boxed_1306_, v___x_21802__boxed_1307_, v___x_21803__boxed_1308_, v_v_1297_, v___x_1298_, v_zs2_1299_, v_ctorRet2_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec_ref(v___y_1301_);
lean_dec_ref(v_zs2_1299_);
lean_dec(v___x_1298_);
lean_dec(v___x_1289_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1310_, lean_object* v___x_1311_, lean_object* v___x_1312_, lean_object* v_motive_1313_, uint8_t v___x_1314_, uint8_t v___x_1315_, uint8_t v___x_1316_, lean_object* v_v_1317_, lean_object* v___x_1318_, lean_object* v_a_1319_, lean_object* v_zs1_1320_, lean_object* v_ctorRet1_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_inc_ref(v___x_1310_);
v___x_1327_ = l_Lean_mkAppN(v___x_1310_, v_zs1_1320_);
lean_inc(v___y_1325_);
lean_inc_ref(v___y_1324_);
lean_inc(v___y_1323_);
lean_inc_ref(v___y_1322_);
v___x_1328_ = lean_whnf(v_ctorRet1_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1328_) == 0)
{
lean_object* v_a_1329_; lean_object* v_dummy_1330_; lean_object* v_nargs_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___f_1342_; lean_object* v___x_1343_; 
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref_known(v___x_1328_, 1);
v_dummy_1330_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1331_ = l_Lean_Expr_getAppNumArgs(v_a_1329_);
lean_inc(v_nargs_1331_);
v___x_1332_ = lean_mk_array(v_nargs_1331_, v_dummy_1330_);
v___x_1333_ = lean_nat_sub(v_nargs_1331_, v___x_1311_);
lean_dec(v_nargs_1331_);
v___x_1334_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1329_, v___x_1332_, v___x_1333_);
v___x_1335_ = lean_array_get_size(v___x_1334_);
lean_inc(v___x_1312_);
v___x_1336_ = l_Array_toSubarray___redArg(v___x_1334_, v___x_1312_, v___x_1335_);
v___x_1337_ = l_Subarray_copy___redArg(v___x_1336_);
v___x_1338_ = lean_array_push(v___x_1337_, v___x_1327_);
v___x_1339_ = lean_box(v___x_1314_);
v___x_1340_ = lean_box(v___x_1315_);
v___x_1341_ = lean_box(v___x_1316_);
v___f_1342_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1342_, 0, v___x_1310_);
lean_closure_set(v___f_1342_, 1, v_dummy_1330_);
lean_closure_set(v___f_1342_, 2, v___x_1311_);
lean_closure_set(v___f_1342_, 3, v___x_1312_);
lean_closure_set(v___f_1342_, 4, v___x_1338_);
lean_closure_set(v___f_1342_, 5, v_motive_1313_);
lean_closure_set(v___f_1342_, 6, v_zs1_1320_);
lean_closure_set(v___f_1342_, 7, v___x_1339_);
lean_closure_set(v___f_1342_, 8, v___x_1340_);
lean_closure_set(v___f_1342_, 9, v___x_1341_);
lean_closure_set(v___f_1342_, 10, v_v_1317_);
lean_closure_set(v___f_1342_, 11, v___x_1318_);
v___x_1343_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1319_, v___f_1342_, v___x_1314_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
return v___x_1343_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v___x_1327_);
lean_dec_ref(v_zs1_1320_);
lean_dec_ref(v_a_1319_);
lean_dec(v___x_1318_);
lean_dec(v_v_1317_);
lean_dec_ref(v_motive_1313_);
lean_dec(v___x_1312_);
lean_dec(v___x_1311_);
lean_dec_ref(v___x_1310_);
v_a_1344_ = lean_ctor_get(v___x_1328_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1328_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1328_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1352_ = _args[0];
lean_object* v___x_1353_ = _args[1];
lean_object* v___x_1354_ = _args[2];
lean_object* v_motive_1355_ = _args[3];
lean_object* v___x_1356_ = _args[4];
lean_object* v___x_1357_ = _args[5];
lean_object* v___x_1358_ = _args[6];
lean_object* v_v_1359_ = _args[7];
lean_object* v___x_1360_ = _args[8];
lean_object* v_a_1361_ = _args[9];
lean_object* v_zs1_1362_ = _args[10];
lean_object* v_ctorRet1_1363_ = _args[11];
lean_object* v___y_1364_ = _args[12];
lean_object* v___y_1365_ = _args[13];
lean_object* v___y_1366_ = _args[14];
lean_object* v___y_1367_ = _args[15];
lean_object* v___y_1368_ = _args[16];
_start:
{
uint8_t v___x_21942__boxed_1369_; uint8_t v___x_21943__boxed_1370_; uint8_t v___x_21944__boxed_1371_; lean_object* v_res_1372_; 
v___x_21942__boxed_1369_ = lean_unbox(v___x_1356_);
v___x_21943__boxed_1370_ = lean_unbox(v___x_1357_);
v___x_21944__boxed_1371_ = lean_unbox(v___x_1358_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1352_, v___x_1353_, v___x_1354_, v_motive_1355_, v___x_21942__boxed_1369_, v___x_21943__boxed_1370_, v___x_21944__boxed_1371_, v_v_1359_, v___x_1360_, v_a_1361_, v_zs1_1362_, v_ctorRet1_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1373_, lean_object* v_params_1374_, lean_object* v___x_1375_, lean_object* v_motive_1376_, size_t v_sz_1377_, size_t v_i_1378_, lean_object* v_bs_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_usize_dec_lt(v_i_1378_, v_sz_1377_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
lean_dec_ref(v_motive_1376_);
lean_dec(v___x_1375_);
lean_dec(v_tail_1373_);
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v_bs_1379_);
return v___x_1386_;
}
else
{
uint8_t v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v_v_1390_; lean_object* v___x_1391_; lean_object* v_bs_x27_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1387_ = 0;
v___x_1388_ = 1;
v___x_1389_ = lean_unsigned_to_nat(1u);
v_v_1390_ = lean_array_uget(v_bs_1379_, v_i_1378_);
v___x_1391_ = lean_unsigned_to_nat(0u);
v_bs_x27_1392_ = lean_array_uset(v_bs_1379_, v_i_1378_, v___x_1391_);
v___x_1393_ = lean_usize_to_nat(v_i_1378_);
lean_inc(v_tail_1373_);
lean_inc(v_v_1390_);
v___x_1394_ = l_Lean_mkConst(v_v_1390_, v_tail_1373_);
v___x_1395_ = l_Lean_mkAppN(v___x_1394_, v_params_1374_);
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1382_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
lean_inc_ref(v___x_1395_);
v___x_1396_ = lean_infer_type(v___x_1395_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v_a_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___f_1401_; lean_object* v___x_1402_; 
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc_n(v_a_1397_, 2);
lean_dec_ref_known(v___x_1396_, 1);
v___x_1398_ = lean_box(v___x_1387_);
v___x_1399_ = lean_box(v___x_1385_);
v___x_1400_ = lean_box(v___x_1388_);
lean_inc_ref(v_motive_1376_);
lean_inc(v___x_1375_);
v___f_1401_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1401_, 0, v___x_1395_);
lean_closure_set(v___f_1401_, 1, v___x_1389_);
lean_closure_set(v___f_1401_, 2, v___x_1375_);
lean_closure_set(v___f_1401_, 3, v_motive_1376_);
lean_closure_set(v___f_1401_, 4, v___x_1398_);
lean_closure_set(v___f_1401_, 5, v___x_1399_);
lean_closure_set(v___f_1401_, 6, v___x_1400_);
lean_closure_set(v___f_1401_, 7, v_v_1390_);
lean_closure_set(v___f_1401_, 8, v___x_1393_);
lean_closure_set(v___f_1401_, 9, v_a_1397_);
v___x_1402_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1397_, v___f_1401_, v___x_1387_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v_a_1403_; size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___x_1402_, 1);
v___x_1404_ = ((size_t)1ULL);
v___x_1405_ = lean_usize_add(v_i_1378_, v___x_1404_);
v___x_1406_ = lean_array_uset(v_bs_x27_1392_, v_i_1378_, v_a_1403_);
v_i_1378_ = v___x_1405_;
v_bs_1379_ = v___x_1406_;
goto _start;
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec_ref(v_bs_x27_1392_);
lean_dec_ref(v_motive_1376_);
lean_dec(v___x_1375_);
lean_dec(v_tail_1373_);
v_a_1408_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1402_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1402_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v___x_1395_);
lean_dec(v___x_1393_);
lean_dec_ref(v_bs_x27_1392_);
lean_dec(v_v_1390_);
lean_dec_ref(v_motive_1376_);
lean_dec(v___x_1375_);
lean_dec(v_tail_1373_);
v_a_1416_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1396_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1396_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1424_, lean_object* v_params_1425_, lean_object* v___x_1426_, lean_object* v_motive_1427_, lean_object* v_sz_1428_, lean_object* v_i_1429_, lean_object* v_bs_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
size_t v_sz_boxed_1436_; size_t v_i_boxed_1437_; lean_object* v_res_1438_; 
v_sz_boxed_1436_ = lean_unbox_usize(v_sz_1428_);
lean_dec(v_sz_1428_);
v_i_boxed_1437_ = lean_unbox_usize(v_i_1429_);
lean_dec(v_i_1429_);
v_res_1438_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1424_, v_params_1425_, v___x_1426_, v_motive_1427_, v_sz_boxed_1436_, v_i_boxed_1437_, v_bs_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec_ref(v_params_1425_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1439_, lean_object* v_indName_1440_, lean_object* v_tail_1441_, lean_object* v_params_1442_, lean_object* v_ism1_1443_, lean_object* v_ism2_1444_, lean_object* v___x_1445_, uint8_t v___x_1446_, uint8_t v___x_1447_, uint8_t v___x_1448_, lean_object* v_name_1449_, lean_object* v___x_1450_, lean_object* v_numParams_1451_, lean_object* v_val_1452_, lean_object* v___x_1453_, lean_object* v___x_1454_, lean_object* v_motive_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___f_1465_; size_t v_sz_1466_; size_t v___x_1467_; lean_object* v___x_1468_; 
v___x_1461_ = lean_array_mk(v_ctors_1439_);
v___x_1462_ = lean_box(v___x_1446_);
v___x_1463_ = lean_box(v___x_1447_);
v___x_1464_ = lean_box(v___x_1448_);
lean_inc(v_numParams_1451_);
lean_inc_ref(v___x_1461_);
lean_inc_ref(v_motive_1455_);
lean_inc_ref(v_params_1442_);
lean_inc(v_tail_1441_);
v___f_1465_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1465_, 0, v_indName_1440_);
lean_closure_set(v___f_1465_, 1, v_tail_1441_);
lean_closure_set(v___f_1465_, 2, v_params_1442_);
lean_closure_set(v___f_1465_, 3, v_ism1_1443_);
lean_closure_set(v___f_1465_, 4, v_ism2_1444_);
lean_closure_set(v___f_1465_, 5, v_motive_1455_);
lean_closure_set(v___f_1465_, 6, v___x_1445_);
lean_closure_set(v___f_1465_, 7, v___x_1462_);
lean_closure_set(v___f_1465_, 8, v___x_1463_);
lean_closure_set(v___f_1465_, 9, v___x_1464_);
lean_closure_set(v___f_1465_, 10, v_name_1449_);
lean_closure_set(v___f_1465_, 11, v___x_1450_);
lean_closure_set(v___f_1465_, 12, v___x_1461_);
lean_closure_set(v___f_1465_, 13, v_numParams_1451_);
lean_closure_set(v___f_1465_, 14, v_val_1452_);
lean_closure_set(v___f_1465_, 15, v___x_1453_);
lean_closure_set(v___f_1465_, 16, v___x_1454_);
v_sz_1466_ = lean_array_size(v___x_1461_);
v___x_1467_ = ((size_t)0ULL);
v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1441_, v_params_1442_, v_numParams_1451_, v_motive_1455_, v_sz_1466_, v___x_1467_, v___x_1461_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec_ref(v_params_1442_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; uint8_t v___x_1470_; lean_object* v___x_1471_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
v___x_1470_ = 0;
v___x_1471_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_a_1469_, v___f_1465_, v___x_1470_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1471_;
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref(v___f_1465_);
v_a_1472_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1468_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1468_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1480_ = _args[0];
lean_object* v_indName_1481_ = _args[1];
lean_object* v_tail_1482_ = _args[2];
lean_object* v_params_1483_ = _args[3];
lean_object* v_ism1_1484_ = _args[4];
lean_object* v_ism2_1485_ = _args[5];
lean_object* v___x_1486_ = _args[6];
lean_object* v___x_1487_ = _args[7];
lean_object* v___x_1488_ = _args[8];
lean_object* v___x_1489_ = _args[9];
lean_object* v_name_1490_ = _args[10];
lean_object* v___x_1491_ = _args[11];
lean_object* v_numParams_1492_ = _args[12];
lean_object* v_val_1493_ = _args[13];
lean_object* v___x_1494_ = _args[14];
lean_object* v___x_1495_ = _args[15];
lean_object* v_motive_1496_ = _args[16];
lean_object* v___y_1497_ = _args[17];
lean_object* v___y_1498_ = _args[18];
lean_object* v___y_1499_ = _args[19];
lean_object* v___y_1500_ = _args[20];
lean_object* v___y_1501_ = _args[21];
_start:
{
uint8_t v___x_22122__boxed_1502_; uint8_t v___x_22123__boxed_1503_; uint8_t v___x_22124__boxed_1504_; lean_object* v_res_1505_; 
v___x_22122__boxed_1502_ = lean_unbox(v___x_1487_);
v___x_22123__boxed_1503_ = lean_unbox(v___x_1488_);
v___x_22124__boxed_1504_ = lean_unbox(v___x_1489_);
v_res_1505_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1480_, v_indName_1481_, v_tail_1482_, v_params_1483_, v_ism1_1484_, v_ism2_1485_, v___x_1486_, v___x_22122__boxed_1502_, v___x_22123__boxed_1503_, v___x_22124__boxed_1504_, v_name_1490_, v___x_1491_, v_numParams_1492_, v_val_1493_, v___x_1494_, v___x_1495_, v_motive_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1509_, lean_object* v_head_1510_, lean_object* v_ctors_1511_, lean_object* v_indName_1512_, lean_object* v_tail_1513_, lean_object* v_params_1514_, lean_object* v_name_1515_, lean_object* v___x_1516_, lean_object* v_numParams_1517_, lean_object* v_val_1518_, lean_object* v___x_1519_, lean_object* v___x_1520_, lean_object* v_ism2_1521_, lean_object* v_x_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; uint8_t v___x_1531_; uint8_t v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; 
lean_inc_ref(v_ism1_1509_);
v___x_1528_ = l_Array_append___redArg(v_ism1_1509_, v_ism2_1521_);
v___x_1529_ = l_Lean_mkSort(v_head_1510_);
v___x_1530_ = 0;
v___x_1531_ = 1;
v___x_1532_ = 1;
v___x_1533_ = lean_box(v___x_1530_);
v___x_1534_ = lean_box(v___x_1531_);
v___x_1535_ = lean_box(v___x_1532_);
lean_inc_ref(v___x_1528_);
v___f_1536_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 22, 16);
lean_closure_set(v___f_1536_, 0, v_ctors_1511_);
lean_closure_set(v___f_1536_, 1, v_indName_1512_);
lean_closure_set(v___f_1536_, 2, v_tail_1513_);
lean_closure_set(v___f_1536_, 3, v_params_1514_);
lean_closure_set(v___f_1536_, 4, v_ism1_1509_);
lean_closure_set(v___f_1536_, 5, v_ism2_1521_);
lean_closure_set(v___f_1536_, 6, v___x_1528_);
lean_closure_set(v___f_1536_, 7, v___x_1533_);
lean_closure_set(v___f_1536_, 8, v___x_1534_);
lean_closure_set(v___f_1536_, 9, v___x_1535_);
lean_closure_set(v___f_1536_, 10, v_name_1515_);
lean_closure_set(v___f_1536_, 11, v___x_1516_);
lean_closure_set(v___f_1536_, 12, v_numParams_1517_);
lean_closure_set(v___f_1536_, 13, v_val_1518_);
lean_closure_set(v___f_1536_, 14, v___x_1519_);
lean_closure_set(v___f_1536_, 15, v___x_1520_);
v___x_1537_ = l_Lean_Meta_mkForallFVars(v___x_1528_, v___x_1529_, v___x_1530_, v___x_1531_, v___x_1531_, v___x_1532_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec_ref(v___x_1528_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1539_; uint8_t v___x_1540_; lean_object* v___x_1541_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
v___x_1539_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1540_ = 0;
v___x_1541_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1539_, v___x_1532_, v_a_1538_, v___f_1536_, v___x_1540_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
return v___x_1541_;
}
else
{
lean_dec_ref(v___f_1536_);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1542_ = _args[0];
lean_object* v_head_1543_ = _args[1];
lean_object* v_ctors_1544_ = _args[2];
lean_object* v_indName_1545_ = _args[3];
lean_object* v_tail_1546_ = _args[4];
lean_object* v_params_1547_ = _args[5];
lean_object* v_name_1548_ = _args[6];
lean_object* v___x_1549_ = _args[7];
lean_object* v_numParams_1550_ = _args[8];
lean_object* v_val_1551_ = _args[9];
lean_object* v___x_1552_ = _args[10];
lean_object* v___x_1553_ = _args[11];
lean_object* v_ism2_1554_ = _args[12];
lean_object* v_x_1555_ = _args[13];
lean_object* v___y_1556_ = _args[14];
lean_object* v___y_1557_ = _args[15];
lean_object* v___y_1558_ = _args[16];
lean_object* v___y_1559_ = _args[17];
lean_object* v___y_1560_ = _args[18];
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1542_, v_head_1543_, v_ctors_1544_, v_indName_1545_, v_tail_1546_, v_params_1547_, v_name_1548_, v___x_1549_, v_numParams_1550_, v_val_1551_, v___x_1552_, v___x_1553_, v_ism2_1554_, v_x_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec_ref(v_x_1555_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1562_, lean_object* v_ctors_1563_, lean_object* v_indName_1564_, lean_object* v_tail_1565_, lean_object* v_params_1566_, lean_object* v_name_1567_, lean_object* v___x_1568_, lean_object* v_numParams_1569_, lean_object* v_val_1570_, lean_object* v___x_1571_, lean_object* v___x_1572_, lean_object* v_t_1573_, lean_object* v___x_1574_, lean_object* v_ism1_1575_, lean_object* v_x_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v___f_1582_; uint8_t v___x_1583_; lean_object* v___x_1584_; 
v___f_1582_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 19, 12);
lean_closure_set(v___f_1582_, 0, v_ism1_1575_);
lean_closure_set(v___f_1582_, 1, v_head_1562_);
lean_closure_set(v___f_1582_, 2, v_ctors_1563_);
lean_closure_set(v___f_1582_, 3, v_indName_1564_);
lean_closure_set(v___f_1582_, 4, v_tail_1565_);
lean_closure_set(v___f_1582_, 5, v_params_1566_);
lean_closure_set(v___f_1582_, 6, v_name_1567_);
lean_closure_set(v___f_1582_, 7, v___x_1568_);
lean_closure_set(v___f_1582_, 8, v_numParams_1569_);
lean_closure_set(v___f_1582_, 9, v_val_1570_);
lean_closure_set(v___f_1582_, 10, v___x_1571_);
lean_closure_set(v___f_1582_, 11, v___x_1572_);
v___x_1583_ = 0;
v___x_1584_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1573_, v___x_1574_, v___f_1582_, v___x_1583_, v___x_1583_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1585_ = _args[0];
lean_object* v_ctors_1586_ = _args[1];
lean_object* v_indName_1587_ = _args[2];
lean_object* v_tail_1588_ = _args[3];
lean_object* v_params_1589_ = _args[4];
lean_object* v_name_1590_ = _args[5];
lean_object* v___x_1591_ = _args[6];
lean_object* v_numParams_1592_ = _args[7];
lean_object* v_val_1593_ = _args[8];
lean_object* v___x_1594_ = _args[9];
lean_object* v___x_1595_ = _args[10];
lean_object* v_t_1596_ = _args[11];
lean_object* v___x_1597_ = _args[12];
lean_object* v_ism1_1598_ = _args[13];
lean_object* v_x_1599_ = _args[14];
lean_object* v___y_1600_ = _args[15];
lean_object* v___y_1601_ = _args[16];
lean_object* v___y_1602_ = _args[17];
lean_object* v___y_1603_ = _args[18];
lean_object* v___y_1604_ = _args[19];
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1585_, v_ctors_1586_, v_indName_1587_, v_tail_1588_, v_params_1589_, v_name_1590_, v___x_1591_, v_numParams_1592_, v_val_1593_, v___x_1594_, v___x_1595_, v_t_1596_, v___x_1597_, v_ism1_1598_, v_x_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec_ref(v_x_1599_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1606_, lean_object* v___x_1607_, lean_object* v_head_1608_, lean_object* v_ctors_1609_, lean_object* v_indName_1610_, lean_object* v_tail_1611_, lean_object* v_params_1612_, lean_object* v_name_1613_, lean_object* v___x_1614_, lean_object* v_numParams_1615_, lean_object* v_val_1616_, lean_object* v___x_1617_, lean_object* v_x_1618_, lean_object* v_t_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___f_1627_; uint8_t v___x_1628_; lean_object* v___x_1629_; 
v___x_1625_ = lean_nat_add(v_numIndices_1606_, v___x_1607_);
v___x_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
lean_inc_ref(v___x_1626_);
lean_inc_ref(v_t_1619_);
v___f_1627_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 20, 13);
lean_closure_set(v___f_1627_, 0, v_head_1608_);
lean_closure_set(v___f_1627_, 1, v_ctors_1609_);
lean_closure_set(v___f_1627_, 2, v_indName_1610_);
lean_closure_set(v___f_1627_, 3, v_tail_1611_);
lean_closure_set(v___f_1627_, 4, v_params_1612_);
lean_closure_set(v___f_1627_, 5, v_name_1613_);
lean_closure_set(v___f_1627_, 6, v___x_1614_);
lean_closure_set(v___f_1627_, 7, v_numParams_1615_);
lean_closure_set(v___f_1627_, 8, v_val_1616_);
lean_closure_set(v___f_1627_, 9, v___x_1617_);
lean_closure_set(v___f_1627_, 10, v___x_1607_);
lean_closure_set(v___f_1627_, 11, v_t_1619_);
lean_closure_set(v___f_1627_, 12, v___x_1626_);
v___x_1628_ = 0;
v___x_1629_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1619_, v___x_1626_, v___f_1627_, v___x_1628_, v___x_1628_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1630_ = _args[0];
lean_object* v___x_1631_ = _args[1];
lean_object* v_head_1632_ = _args[2];
lean_object* v_ctors_1633_ = _args[3];
lean_object* v_indName_1634_ = _args[4];
lean_object* v_tail_1635_ = _args[5];
lean_object* v_params_1636_ = _args[6];
lean_object* v_name_1637_ = _args[7];
lean_object* v___x_1638_ = _args[8];
lean_object* v_numParams_1639_ = _args[9];
lean_object* v_val_1640_ = _args[10];
lean_object* v___x_1641_ = _args[11];
lean_object* v_x_1642_ = _args[12];
lean_object* v_t_1643_ = _args[13];
lean_object* v___y_1644_ = _args[14];
lean_object* v___y_1645_ = _args[15];
lean_object* v___y_1646_ = _args[16];
lean_object* v___y_1647_ = _args[17];
lean_object* v___y_1648_ = _args[18];
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1630_, v___x_1631_, v_head_1632_, v_ctors_1633_, v_indName_1634_, v_tail_1635_, v_params_1636_, v_name_1637_, v___x_1638_, v_numParams_1639_, v_val_1640_, v___x_1641_, v_x_1642_, v_t_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v_x_1642_);
lean_dec(v_numIndices_1630_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1652_, lean_object* v_head_1653_, lean_object* v_ctors_1654_, lean_object* v_indName_1655_, lean_object* v_tail_1656_, lean_object* v_name_1657_, lean_object* v___x_1658_, lean_object* v_numParams_1659_, lean_object* v_val_1660_, lean_object* v___x_1661_, lean_object* v_params_1662_, lean_object* v_t_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; lean_object* v___f_1670_; lean_object* v___x_1671_; uint8_t v___x_1672_; lean_object* v___x_1673_; 
v___x_1669_ = lean_unsigned_to_nat(1u);
v___f_1670_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 19, 12);
lean_closure_set(v___f_1670_, 0, v_numIndices_1652_);
lean_closure_set(v___f_1670_, 1, v___x_1669_);
lean_closure_set(v___f_1670_, 2, v_head_1653_);
lean_closure_set(v___f_1670_, 3, v_ctors_1654_);
lean_closure_set(v___f_1670_, 4, v_indName_1655_);
lean_closure_set(v___f_1670_, 5, v_tail_1656_);
lean_closure_set(v___f_1670_, 6, v_params_1662_);
lean_closure_set(v___f_1670_, 7, v_name_1657_);
lean_closure_set(v___f_1670_, 8, v___x_1658_);
lean_closure_set(v___f_1670_, 9, v_numParams_1659_);
lean_closure_set(v___f_1670_, 10, v_val_1660_);
lean_closure_set(v___f_1670_, 11, v___x_1661_);
v___x_1671_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1672_ = 0;
v___x_1673_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1663_, v___x_1671_, v___f_1670_, v___x_1672_, v___x_1672_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1674_ = _args[0];
lean_object* v_head_1675_ = _args[1];
lean_object* v_ctors_1676_ = _args[2];
lean_object* v_indName_1677_ = _args[3];
lean_object* v_tail_1678_ = _args[4];
lean_object* v_name_1679_ = _args[5];
lean_object* v___x_1680_ = _args[6];
lean_object* v_numParams_1681_ = _args[7];
lean_object* v_val_1682_ = _args[8];
lean_object* v___x_1683_ = _args[9];
lean_object* v_params_1684_ = _args[10];
lean_object* v_t_1685_ = _args[11];
lean_object* v___y_1686_ = _args[12];
lean_object* v___y_1687_ = _args[13];
lean_object* v___y_1688_ = _args[14];
lean_object* v___y_1689_ = _args[15];
lean_object* v___y_1690_ = _args[16];
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1674_, v_head_1675_, v_ctors_1676_, v_indName_1677_, v_tail_1678_, v_name_1679_, v___x_1680_, v_numParams_1681_, v_val_1682_, v___x_1683_, v_params_1684_, v_t_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1692_, lean_object* v_declName_1693_, lean_object* v_levelParams_1694_, uint8_t v___x_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
lean_object* v___x_1701_; 
lean_inc(v___y_1699_);
lean_inc_ref(v___y_1698_);
lean_inc_ref(v_a_1692_);
v___x_1701_ = lean_infer_type(v_a_1692_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 1);
v___x_1703_ = lean_box(1);
v___x_1704_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1693_, v_levelParams_1694_, v_a_1702_, v_a_1692_, v___x_1703_, v___y_1699_);
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
lean_ctor_set_tag(v___x_1707_, 1);
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
lean_object* v___x_1711_; 
v___x_1711_ = l_Lean_addDecl(v___x_1710_, v___x_1695_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
return v___x_1711_;
}
}
}
else
{
lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1721_; 
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v_levelParams_1694_);
lean_dec(v_declName_1693_);
lean_dec_ref(v_a_1692_);
v_a_1714_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1721_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1721_ == 0)
{
v___x_1716_ = v___x_1701_;
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_dec(v___x_1701_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1721_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1722_, lean_object* v_declName_1723_, lean_object* v_levelParams_1724_, lean_object* v___x_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v___x_22410__boxed_1731_; lean_object* v_res_1732_; 
v___x_22410__boxed_1731_ = lean_unbox(v___x_1725_);
v_res_1732_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1722_, v_declName_1723_, v_levelParams_1724_, v___x_22410__boxed_1731_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
if (lean_obj_tag(v_a_1733_) == 0)
{
lean_object* v___x_1735_; 
v___x_1735_ = l_List_reverse___redArg(v_a_1734_);
return v___x_1735_;
}
else
{
lean_object* v_head_1736_; lean_object* v_tail_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1746_; 
v_head_1736_ = lean_ctor_get(v_a_1733_, 0);
v_tail_1737_ = lean_ctor_get(v_a_1733_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_a_1733_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1739_ = v_a_1733_;
v_isShared_1740_ = v_isSharedCheck_1746_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_tail_1737_);
lean_inc(v_head_1736_);
lean_dec(v_a_1733_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1746_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1741_ = l_Lean_mkLevelParam(v_head_1736_);
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 1, v_a_1734_);
lean_ctor_set(v___x_1739_, 0, v___x_1741_);
v___x_1743_ = v___x_1739_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_a_1734_);
v___x_1743_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
v_a_1733_ = v_tail_1737_;
v_a_1734_ = v___x_1743_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object* v_msgData_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___x_1753_; lean_object* v_env_1754_; uint8_t v___x_1755_; lean_object* v_env_1756_; lean_object* v___x_1757_; lean_object* v_toCold_1758_; lean_object* v_mctx_1759_; lean_object* v_lctx_1760_; lean_object* v_options_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1753_ = lean_st_ref_get(v___y_1751_);
v_env_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc_ref(v_env_1754_);
lean_dec(v___x_1753_);
v___x_1755_ = 0;
v_env_1756_ = l_Lean_Environment_setRecordingDeps(v_env_1754_, v___x_1755_);
v___x_1757_ = lean_st_ref_get(v___y_1749_);
v_toCold_1758_ = lean_ctor_get(v___y_1750_, 0);
v_mctx_1759_ = lean_ctor_get(v___x_1757_, 0);
lean_inc_ref(v_mctx_1759_);
lean_dec(v___x_1757_);
v_lctx_1760_ = lean_ctor_get(v___y_1748_, 2);
v_options_1761_ = lean_ctor_get(v_toCold_1758_, 2);
lean_inc_ref(v_options_1761_);
lean_inc_ref(v_lctx_1760_);
v___x_1762_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1762_, 0, v_env_1756_);
lean_ctor_set(v___x_1762_, 1, v_mctx_1759_);
lean_ctor_set(v___x_1762_, 2, v_lctx_1760_);
lean_ctor_set(v___x_1762_, 3, v_options_1761_);
v___x_1763_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v_msgData_1747_);
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v___y_1767_);
lean_dec_ref(v___y_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_ref_1778_; lean_object* v___x_1779_; lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1788_; 
v_ref_1778_ = lean_ctor_get(v___y_1775_, 2);
v___x_1779_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1788_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1788_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v___x_1786_; 
lean_inc(v_ref_1778_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v_ref_1778_);
lean_ctor_set(v___x_1784_, 1, v_a_1780_);
if (v_isShared_1783_ == 0)
{
lean_ctor_set_tag(v___x_1782_, 1);
lean_ctor_set(v___x_1782_, 0, v___x_1784_);
v___x_1786_ = v___x_1782_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
lean_dec(v___y_1793_);
lean_dec_ref(v___y_1792_);
lean_dec(v___y_1791_);
lean_dec_ref(v___y_1790_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1796_, lean_object* v_msg_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v_toCold_1803_; lean_object* v_currRecDepth_1804_; lean_object* v_ref_1805_; uint16_t v_optionFlags_1806_; uint8_t v_suppressElabErrors_1807_; uint8_t v_isRecordingDeps_1808_; lean_object* v_ref_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_toCold_1803_ = lean_ctor_get(v___y_1800_, 0);
v_currRecDepth_1804_ = lean_ctor_get(v___y_1800_, 1);
v_ref_1805_ = lean_ctor_get(v___y_1800_, 2);
v_optionFlags_1806_ = lean_ctor_get_uint16(v___y_1800_, sizeof(void*)*3);
v_suppressElabErrors_1807_ = lean_ctor_get_uint8(v___y_1800_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1808_ = lean_ctor_get_uint8(v___y_1800_, sizeof(void*)*3 + 3);
v_ref_1809_ = l_Lean_replaceRef(v_ref_1796_, v_ref_1805_);
lean_inc(v_currRecDepth_1804_);
lean_inc_ref(v_toCold_1803_);
v___x_1810_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1810_, 0, v_toCold_1803_);
lean_ctor_set(v___x_1810_, 1, v_currRecDepth_1804_);
lean_ctor_set(v___x_1810_, 2, v_ref_1809_);
lean_ctor_set_uint16(v___x_1810_, sizeof(void*)*3, v_optionFlags_1806_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*3 + 2, v_suppressElabErrors_1807_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*3 + 3, v_isRecordingDeps_1808_);
v___x_1811_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1797_, v___y_1798_, v___y_1799_, v___x_1810_, v___y_1801_);
lean_dec_ref_known(v___x_1810_, 3);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1812_, lean_object* v_msg_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1812_, v_msg_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v_ref_1812_);
return v_res_1819_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1822_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
lean_ctor_set(v___x_1825_, 2, v___x_1824_);
lean_ctor_set(v___x_1825_, 3, v___x_1824_);
lean_ctor_set(v___x_1825_, 4, v___x_1823_);
lean_ctor_set(v___x_1825_, 5, v___x_1823_);
lean_ctor_set(v___x_1825_, 6, v___x_1823_);
lean_ctor_set(v___x_1825_, 7, v___x_1823_);
lean_ctor_set(v___x_1825_, 8, v___x_1823_);
lean_ctor_set(v___x_1825_, 9, v___x_1823_);
lean_ctor_set(v___x_1825_, 10, v___x_1823_);
lean_ctor_set(v___x_1825_, 11, v___x_1822_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_unsigned_to_nat(32u);
v___x_1827_ = lean_mk_empty_array_with_capacity(v___x_1826_);
v___x_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
size_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1829_ = ((size_t)5ULL);
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_unsigned_to_nat(32u);
v___x_1832_ = lean_mk_empty_array_with_capacity(v___x_1831_);
v___x_1833_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1834_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v___x_1832_);
lean_ctor_set(v___x_1834_, 2, v___x_1830_);
lean_ctor_set(v___x_1834_, 3, v___x_1830_);
lean_ctor_set_usize(v___x_1834_, 4, v___x_1829_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1835_ = lean_box(1);
v___x_1836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v___x_1836_);
lean_ctor_set(v___x_1838_, 2, v___x_1835_);
return v___x_1838_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5));
v___x_1841_ = l_Lean_stringToMessageData(v___x_1840_);
return v___x_1841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9));
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11));
v___x_1850_ = l_Lean_stringToMessageData(v___x_1849_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13));
v___x_1853_ = l_Lean_stringToMessageData(v___x_1852_);
return v___x_1853_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15));
v___x_1856_ = l_Lean_stringToMessageData(v___x_1855_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17));
v___x_1859_ = l_Lean_stringToMessageData(v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1860_, lean_object* v_declHint_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v_env_1866_; uint8_t v___x_1867_; 
v___x_1864_ = lean_box(0);
v___x_1865_ = lean_st_ref_get(v___y_1862_);
v_env_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc_ref(v_env_1866_);
lean_dec(v___x_1865_);
v___x_1867_ = l_Lean_Name_isAnonymous(v_declHint_1861_);
if (v___x_1867_ == 0)
{
uint8_t v_isExporting_1868_; 
v_isExporting_1868_ = lean_ctor_get_uint8(v_env_1866_, sizeof(void*)*13);
if (v_isExporting_1868_ == 0)
{
lean_object* v___x_1869_; 
lean_dec_ref(v_env_1866_);
lean_dec(v_declHint_1861_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_msg_1860_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
lean_inc_ref(v_env_1866_);
v___x_1870_ = l_Lean_Environment_setExporting(v_env_1866_, v___x_1867_);
lean_inc(v_declHint_1861_);
lean_inc_ref(v___x_1870_);
v___x_1871_ = l_Lean_Environment_contains(v___x_1870_, v_declHint_1861_, v_isExporting_1868_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v___x_1870_);
lean_dec_ref(v_env_1866_);
lean_dec(v_declHint_1861_);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_msg_1860_);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_c_1878_; lean_object* v___x_1879_; 
v___x_1873_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1874_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1875_ = l_Lean_Options_empty;
v___x_1876_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1870_);
lean_ctor_set(v___x_1876_, 1, v___x_1873_);
lean_ctor_set(v___x_1876_, 2, v___x_1874_);
lean_ctor_set(v___x_1876_, 3, v___x_1875_);
lean_inc(v_declHint_1861_);
v___x_1877_ = l_Lean_MessageData_ofConstName(v_declHint_1861_, v___x_1867_);
v_c_1878_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1878_, 0, v___x_1876_);
lean_ctor_set(v_c_1878_, 1, v___x_1877_);
v___x_1879_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1866_, v_declHint_1861_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec_ref(v_env_1866_);
lean_dec(v_declHint_1861_);
v___x_1880_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v_c_1878_);
v___x_1882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8);
v___x_1883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = l_Lean_MessageData_note(v___x_1883_);
v___x_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1885_, 0, v_msg_1860_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
return v___x_1886_;
}
else
{
lean_object* v_val_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1921_; 
v_val_1887_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1889_ = v___x_1879_;
v_isShared_1890_ = v_isSharedCheck_1921_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_val_1887_);
lean_dec(v___x_1879_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1921_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v_moduleNames_1892_; lean_object* v_mod_1893_; uint8_t v___x_1894_; 
v___x_1891_ = l_Lean_Environment_header(v_env_1866_);
lean_dec_ref(v_env_1866_);
v_moduleNames_1892_ = lean_ctor_get(v___x_1891_, 4);
lean_inc_ref(v_moduleNames_1892_);
lean_dec_ref(v___x_1891_);
v_mod_1893_ = lean_array_get(v___x_1864_, v_moduleNames_1892_, v_val_1887_);
lean_dec(v_val_1887_);
lean_dec_ref(v_moduleNames_1892_);
v___x_1894_ = l_Lean_isPrivateName(v_declHint_1861_);
lean_dec(v_declHint_1861_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v_c_1878_);
v___x_1897_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = l_Lean_MessageData_ofName(v_mod_1893_);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = l_Lean_MessageData_note(v___x_1902_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_msg_1860_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1904_);
v___x_1906_ = v___x_1889_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
v___x_1908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
lean_ctor_set(v___x_1909_, 1, v_c_1878_);
v___x_1910_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = l_Lean_MessageData_ofName(v_mod_1893_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_MessageData_note(v___x_1915_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v_msg_1860_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1917_);
v___x_1919_ = v___x_1889_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1922_; 
lean_dec_ref(v_env_1866_);
lean_dec(v_declHint_1861_);
v___x_1922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_msg_1860_);
return v___x_1922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1923_, lean_object* v_declHint_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1923_, v_declHint_1924_, v___y_1925_);
lean_dec(v___y_1925_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1928_, lean_object* v_declHint_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v___x_1935_; lean_object* v_a_1936_; lean_object* v___x_1938_; uint8_t v_isShared_1939_; uint8_t v_isSharedCheck_1945_; 
v___x_1935_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1928_, v_declHint_1929_, v___y_1933_);
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1938_ = v___x_1935_;
v_isShared_1939_ = v_isSharedCheck_1945_;
goto v_resetjp_1937_;
}
else
{
lean_inc(v_a_1936_);
lean_dec(v___x_1935_);
v___x_1938_ = lean_box(0);
v_isShared_1939_ = v_isSharedCheck_1945_;
goto v_resetjp_1937_;
}
v_resetjp_1937_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1943_; 
v___x_1940_ = l_Lean_unknownIdentifierMessageTag;
v___x_1941_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v_a_1936_);
if (v_isShared_1939_ == 0)
{
lean_ctor_set(v___x_1938_, 0, v___x_1941_);
v___x_1943_ = v___x_1938_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v___x_1941_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1946_, lean_object* v_declHint_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v_res_1953_; 
v_res_1953_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1946_, v_declHint_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1954_, lean_object* v_msg_1955_, lean_object* v_declHint_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v___x_1962_; lean_object* v_a_1963_; lean_object* v___x_1964_; 
v___x_1962_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1955_, v_declHint_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref(v___x_1962_);
v___x_1964_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1954_, v_a_1963_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1965_, lean_object* v_msg_1966_, lean_object* v_declHint_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1965_, v_msg_1966_, v_declHint_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v_ref_1965_);
return v_res_1973_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_1976_ = l_Lean_stringToMessageData(v___x_1975_);
return v___x_1976_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_1979_ = l_Lean_stringToMessageData(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_1980_, lean_object* v_constName_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; uint8_t v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1987_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_1988_ = 0;
lean_inc(v_constName_1981_);
v___x_1989_ = l_Lean_MessageData_ofConstName(v_constName_1981_, v___x_1988_);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1987_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1980_, v___x_1992_, v_constName_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_1994_, lean_object* v_constName_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1994_, v_constName_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_ref_1994_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_ref_2008_; lean_object* v___x_2009_; 
v_ref_2008_ = lean_ctor_get(v___y_2005_, 2);
v___x_2009_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2008_, v_constName_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_);
lean_dec(v___y_2014_);
lean_dec_ref(v___y_2013_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_){
_start:
{
lean_object* v___x_2023_; lean_object* v_env_2024_; uint8_t v___x_2025_; lean_object* v___x_2026_; 
v___x_2023_ = lean_st_ref_get(v___y_2021_);
v_env_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc_ref(v_env_2024_);
lean_dec(v___x_2023_);
v___x_2025_ = 0;
lean_inc(v_constName_2017_);
v___x_2026_ = l_Lean_Environment_findConstVal_x3f(v_env_2024_, v_constName_2017_, v___x_2025_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2017_, v___y_2018_, v___y_2019_, v___y_2020_, v___y_2021_);
return v___x_2027_;
}
else
{
lean_object* v_val_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_constName_2017_);
v_val_2028_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2026_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_val_2028_);
lean_dec(v___x_2026_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 0);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_val_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2043_, uint8_t v_s_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v___x_2048_; lean_object* v_env_2049_; lean_object* v_nextMacroScope_2050_; lean_object* v_ngen_2051_; lean_object* v_auxDeclNGen_2052_; lean_object* v_traceState_2053_; lean_object* v_recordedDeps_2054_; lean_object* v_messages_2055_; lean_object* v_infoState_2056_; lean_object* v_snapshotTasks_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2086_; 
v___x_2048_ = lean_st_ref_take(v___y_2046_);
v_env_2049_ = lean_ctor_get(v___x_2048_, 0);
v_nextMacroScope_2050_ = lean_ctor_get(v___x_2048_, 1);
v_ngen_2051_ = lean_ctor_get(v___x_2048_, 2);
v_auxDeclNGen_2052_ = lean_ctor_get(v___x_2048_, 3);
v_traceState_2053_ = lean_ctor_get(v___x_2048_, 4);
v_recordedDeps_2054_ = lean_ctor_get(v___x_2048_, 6);
v_messages_2055_ = lean_ctor_get(v___x_2048_, 7);
v_infoState_2056_ = lean_ctor_get(v___x_2048_, 8);
v_snapshotTasks_2057_ = lean_ctor_get(v___x_2048_, 9);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v___x_2048_, 5);
lean_dec(v_unused_2087_);
v___x_2059_ = v___x_2048_;
v_isShared_2060_ = v_isSharedCheck_2086_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_snapshotTasks_2057_);
lean_inc(v_infoState_2056_);
lean_inc(v_messages_2055_);
lean_inc(v_recordedDeps_2054_);
lean_inc(v_traceState_2053_);
lean_inc(v_auxDeclNGen_2052_);
lean_inc(v_ngen_2051_);
lean_inc(v_nextMacroScope_2050_);
lean_inc(v_env_2049_);
lean_dec(v___x_2048_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2086_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2066_; 
v___x_2061_ = 0;
v___x_2062_ = lean_box(0);
v___x_2063_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2049_, v_declName_2043_, v_s_2044_, v___x_2061_, v___x_2062_);
v___x_2064_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 5, v___x_2064_);
lean_ctor_set(v___x_2059_, 0, v___x_2063_);
v___x_2066_ = v___x_2059_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_nextMacroScope_2050_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_ngen_2051_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_auxDeclNGen_2052_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_traceState_2053_);
lean_ctor_set(v_reuseFailAlloc_2085_, 5, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2085_, 6, v_recordedDeps_2054_);
lean_ctor_set(v_reuseFailAlloc_2085_, 7, v_messages_2055_);
lean_ctor_set(v_reuseFailAlloc_2085_, 8, v_infoState_2056_);
lean_ctor_set(v_reuseFailAlloc_2085_, 9, v_snapshotTasks_2057_);
v___x_2066_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v_mctx_2069_; lean_object* v_zetaDeltaFVarIds_2070_; lean_object* v_postponed_2071_; lean_object* v_diag_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2083_; 
v___x_2067_ = lean_st_ref_put(v___y_2046_, v___x_2066_);
v___x_2068_ = lean_st_ref_take(v___y_2045_);
v_mctx_2069_ = lean_ctor_get(v___x_2068_, 0);
v_zetaDeltaFVarIds_2070_ = lean_ctor_get(v___x_2068_, 2);
v_postponed_2071_ = lean_ctor_get(v___x_2068_, 3);
v_diag_2072_ = lean_ctor_get(v___x_2068_, 4);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v___x_2068_, 1);
lean_dec(v_unused_2084_);
v___x_2074_ = v___x_2068_;
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_diag_2072_);
lean_inc(v_postponed_2071_);
lean_inc(v_zetaDeltaFVarIds_2070_);
lean_inc(v_mctx_2069_);
lean_dec(v___x_2068_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2076_ = lean_box(0);
v___x_2077_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v___x_2077_);
v___x_2079_ = v___x_2074_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_mctx_2069_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_zetaDeltaFVarIds_2070_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_postponed_2071_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v_diag_2072_);
v___x_2079_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_st_ref_put(v___y_2045_, v___x_2079_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2076_);
return v___x_2081_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2088_, lean_object* v_s_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
uint8_t v_s_boxed_2093_; lean_object* v_res_2094_; 
v_s_boxed_2093_ = lean_unbox(v_s_2089_);
v_res_2094_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2088_, v_s_boxed_2093_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec(v___y_2090_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
uint8_t v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = 0;
v___x_2102_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2095_, v___x_2101_, v___y_2097_, v___y_2099_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
return v_res_2109_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2112_ = l_Lean_stringToMessageData(v___x_2111_);
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2115_ = l_Lean_stringToMessageData(v___x_2114_);
return v___x_2115_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2118_ = l_Lean_stringToMessageData(v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2119_, lean_object* v_declName_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2126_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2127_ = l_Lean_MessageData_ofName(v_attrName_2119_);
v___x_2128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = 0;
v___x_2132_ = l_Lean_MessageData_ofConstName(v_declName_2120_, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2130_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2133_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2135_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2137_, lean_object* v_declName_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2137_, v_declName_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0(lean_object* v_addEntryFn_2145_, lean_object* v_decl_2146_, lean_object* v_s_2147_){
_start:
{
lean_object* v_importedEntries_2148_; lean_object* v_state_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2157_; 
v_importedEntries_2148_ = lean_ctor_get(v_s_2147_, 0);
v_state_2149_ = lean_ctor_get(v_s_2147_, 1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_s_2147_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2151_ = v_s_2147_;
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_state_2149_);
lean_inc(v_importedEntries_2148_);
lean_dec(v_s_2147_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2157_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v_state_2153_; lean_object* v___x_2155_; 
v_state_2153_ = lean_apply_2(v_addEntryFn_2145_, v_state_2149_, v_decl_2146_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 1, v_state_2153_);
v___x_2155_ = v___x_2151_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_importedEntries_2148_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v_state_2153_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2160_ = l_Lean_stringToMessageData(v___x_2159_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2163_ = l_Lean_stringToMessageData(v___x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2164_, lean_object* v_declName_2165_, lean_object* v_asyncPrefix_x3f_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v___y_2173_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2166_) == 0)
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lean_MessageData_nil;
v___y_2173_ = v___x_2186_;
goto v___jp_2172_;
}
else
{
lean_object* v_val_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v_val_2187_ = lean_ctor_get(v_asyncPrefix_x3f_2166_, 0);
lean_inc(v_val_2187_);
lean_dec_ref_known(v_asyncPrefix_x3f_2166_, 1);
v___x_2188_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2189_ = l_Lean_MessageData_ofName(v_val_2187_);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
v___y_2173_ = v___x_2192_;
goto v___jp_2172_;
}
v___jp_2172_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2174_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2175_ = l_Lean_MessageData_ofName(v_attrName_2164_);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = 0;
v___x_2180_ = l_Lean_MessageData_ofConstName(v_declName_2165_, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2178_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2181_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v___y_2173_);
v___x_2185_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2184_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v___x_2185_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2193_, lean_object* v_declName_2194_, lean_object* v_asyncPrefix_x3f_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2193_, v_declName_2194_, v_asyncPrefix_x3f_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2202_, lean_object* v_decl_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___x_2264_; lean_object* v_env_2265_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___x_2280_; 
v___x_2264_ = lean_st_ref_get(v___y_2207_);
v_env_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc_ref(v_env_2265_);
lean_dec(v___x_2264_);
v___x_2280_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2265_, v_decl_2203_);
if (lean_obj_tag(v___x_2280_) == 0)
{
v___y_2267_ = v___y_2204_;
v___y_2268_ = v___y_2205_;
v___y_2269_ = v___y_2206_;
v___y_2270_ = v___y_2207_;
goto v___jp_2266_;
}
else
{
lean_object* v_attr_2281_; lean_object* v_toAttributeImplCore_2282_; lean_object* v_name_2283_; lean_object* v___x_2284_; 
lean_dec_ref_known(v___x_2280_, 1);
lean_dec_ref(v_env_2265_);
v_attr_2281_ = lean_ctor_get(v_attr_2202_, 0);
lean_inc_ref(v_attr_2281_);
lean_dec_ref(v_attr_2202_);
v_toAttributeImplCore_2282_ = lean_ctor_get(v_attr_2281_, 0);
lean_inc_ref(v_toAttributeImplCore_2282_);
lean_dec_ref(v_attr_2281_);
v_name_2283_ = lean_ctor_get(v_toAttributeImplCore_2282_, 1);
lean_inc(v_name_2283_);
lean_dec_ref(v_toAttributeImplCore_2282_);
v___x_2284_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2283_, v_decl_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
return v___x_2284_;
}
v___jp_2209_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v_mctx_2225_; lean_object* v_zetaDeltaFVarIds_2226_; lean_object* v_postponed_2227_; lean_object* v_diag_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2239_; 
v___x_2221_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
v___x_2222_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2222_, 0, v___y_2220_);
lean_ctor_set(v___x_2222_, 1, v___y_2210_);
lean_ctor_set(v___x_2222_, 2, v___y_2213_);
lean_ctor_set(v___x_2222_, 3, v___y_2211_);
lean_ctor_set(v___x_2222_, 4, v___y_2217_);
lean_ctor_set(v___x_2222_, 5, v___x_2221_);
lean_ctor_set(v___x_2222_, 6, v___y_2214_);
lean_ctor_set(v___x_2222_, 7, v___y_2219_);
lean_ctor_set(v___x_2222_, 8, v___y_2218_);
lean_ctor_set(v___x_2222_, 9, v___y_2216_);
v___x_2223_ = lean_st_ref_put(v___y_2212_, v___x_2222_);
v___x_2224_ = lean_st_ref_take(v___y_2215_);
v_mctx_2225_ = lean_ctor_get(v___x_2224_, 0);
v_zetaDeltaFVarIds_2226_ = lean_ctor_get(v___x_2224_, 2);
v_postponed_2227_ = lean_ctor_get(v___x_2224_, 3);
v_diag_2228_ = lean_ctor_get(v___x_2224_, 4);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; 
v_unused_2240_ = lean_ctor_get(v___x_2224_, 1);
lean_dec(v_unused_2240_);
v___x_2230_ = v___x_2224_;
v_isShared_2231_ = v_isSharedCheck_2239_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_diag_2228_);
lean_inc(v_postponed_2227_);
lean_inc(v_zetaDeltaFVarIds_2226_);
lean_inc(v_mctx_2225_);
lean_dec(v___x_2224_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2239_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2232_ = lean_box(0);
v___x_2233_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2231_ == 0)
{
lean_ctor_set(v___x_2230_, 1, v___x_2233_);
v___x_2235_ = v___x_2230_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_mctx_2225_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v___x_2233_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_zetaDeltaFVarIds_2226_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_postponed_2227_);
lean_ctor_set(v_reuseFailAlloc_2238_, 4, v_diag_2228_);
v___x_2235_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2236_ = lean_st_ref_put(v___y_2215_, v___x_2235_);
v___x_2237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2232_);
return v___x_2237_;
}
}
}
v___jp_2241_:
{
lean_object* v___x_2244_; lean_object* v_ext_2245_; lean_object* v_toEnvExtension_2246_; lean_object* v_env_2247_; lean_object* v_nextMacroScope_2248_; lean_object* v_ngen_2249_; lean_object* v_auxDeclNGen_2250_; lean_object* v_traceState_2251_; lean_object* v_recordedDeps_2252_; lean_object* v_messages_2253_; lean_object* v_infoState_2254_; lean_object* v_snapshotTasks_2255_; lean_object* v_addEntryFn_2256_; lean_object* v_asyncMode_2257_; uint8_t v_logWrites_2258_; lean_object* v___f_2259_; uint8_t v___x_2260_; 
v___x_2244_ = lean_st_ref_take(v___y_2243_);
v_ext_2245_ = lean_ctor_get(v_attr_2202_, 1);
lean_inc_ref(v_ext_2245_);
lean_dec_ref(v_attr_2202_);
v_toEnvExtension_2246_ = lean_ctor_get(v_ext_2245_, 0);
lean_inc_ref(v_toEnvExtension_2246_);
v_env_2247_ = lean_ctor_get(v___x_2244_, 0);
lean_inc_ref(v_env_2247_);
v_nextMacroScope_2248_ = lean_ctor_get(v___x_2244_, 1);
lean_inc(v_nextMacroScope_2248_);
v_ngen_2249_ = lean_ctor_get(v___x_2244_, 2);
lean_inc_ref(v_ngen_2249_);
v_auxDeclNGen_2250_ = lean_ctor_get(v___x_2244_, 3);
lean_inc_ref(v_auxDeclNGen_2250_);
v_traceState_2251_ = lean_ctor_get(v___x_2244_, 4);
lean_inc_ref(v_traceState_2251_);
v_recordedDeps_2252_ = lean_ctor_get(v___x_2244_, 6);
lean_inc_ref(v_recordedDeps_2252_);
v_messages_2253_ = lean_ctor_get(v___x_2244_, 7);
lean_inc_ref(v_messages_2253_);
v_infoState_2254_ = lean_ctor_get(v___x_2244_, 8);
lean_inc_ref(v_infoState_2254_);
v_snapshotTasks_2255_ = lean_ctor_get(v___x_2244_, 9);
lean_inc_ref(v_snapshotTasks_2255_);
lean_dec(v___x_2244_);
v_addEntryFn_2256_ = lean_ctor_get(v_ext_2245_, 3);
lean_inc(v_addEntryFn_2256_);
lean_dec_ref(v_ext_2245_);
v_asyncMode_2257_ = lean_ctor_get(v_toEnvExtension_2246_, 2);
lean_inc(v_asyncMode_2257_);
v_logWrites_2258_ = lean_ctor_get_uint8(v_toEnvExtension_2246_, sizeof(void*)*6);
lean_inc(v_decl_2203_);
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0), 3, 2);
lean_closure_set(v___f_2259_, 0, v_addEntryFn_2256_);
lean_closure_set(v___f_2259_, 1, v_decl_2203_);
v___x_2260_ = 1;
if (v_logWrites_2258_ == 0)
{
lean_object* v___x_2261_; 
v___x_2261_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2246_, v_env_2247_, v___f_2259_, v_asyncMode_2257_, v_decl_2203_, v___x_2260_);
lean_dec(v_asyncMode_2257_);
v___y_2210_ = v_nextMacroScope_2248_;
v___y_2211_ = v_auxDeclNGen_2250_;
v___y_2212_ = v___y_2243_;
v___y_2213_ = v_ngen_2249_;
v___y_2214_ = v_recordedDeps_2252_;
v___y_2215_ = v___y_2242_;
v___y_2216_ = v_snapshotTasks_2255_;
v___y_2217_ = v_traceState_2251_;
v___y_2218_ = v_infoState_2254_;
v___y_2219_ = v_messages_2253_;
v___y_2220_ = v___x_2261_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_inc_ref(v_toEnvExtension_2246_);
v___x_2262_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2246_, v_env_2247_);
lean_dec_ref(v_env_2247_);
v___x_2263_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2246_, v___x_2262_, v___f_2259_, v_asyncMode_2257_, v_decl_2203_, v___x_2260_);
lean_dec(v_asyncMode_2257_);
v___y_2210_ = v_nextMacroScope_2248_;
v___y_2211_ = v_auxDeclNGen_2250_;
v___y_2212_ = v___y_2243_;
v___y_2213_ = v_ngen_2249_;
v___y_2214_ = v_recordedDeps_2252_;
v___y_2215_ = v___y_2242_;
v___y_2216_ = v_snapshotTasks_2255_;
v___y_2217_ = v_traceState_2251_;
v___y_2218_ = v_infoState_2254_;
v___y_2219_ = v_messages_2253_;
v___y_2220_ = v___x_2263_;
goto v___jp_2209_;
}
}
v___jp_2266_:
{
lean_object* v_ext_2271_; lean_object* v_toEnvExtension_2272_; lean_object* v_attr_2273_; lean_object* v_asyncMode_2274_; uint8_t v___x_2275_; 
v_ext_2271_ = lean_ctor_get(v_attr_2202_, 1);
v_toEnvExtension_2272_ = lean_ctor_get(v_ext_2271_, 0);
v_attr_2273_ = lean_ctor_get(v_attr_2202_, 0);
v_asyncMode_2274_ = lean_ctor_get(v_toEnvExtension_2272_, 2);
lean_inc(v_decl_2203_);
lean_inc_ref(v_env_2265_);
v___x_2275_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2265_, v_decl_2203_, v_asyncMode_2274_);
if (v___x_2275_ == 0)
{
lean_object* v_toAttributeImplCore_2276_; lean_object* v_name_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_inc_ref(v_attr_2273_);
lean_dec_ref(v_attr_2202_);
v_toAttributeImplCore_2276_ = lean_ctor_get(v_attr_2273_, 0);
lean_inc_ref(v_toAttributeImplCore_2276_);
lean_dec_ref(v_attr_2273_);
v_name_2277_ = lean_ctor_get(v_toAttributeImplCore_2276_, 1);
lean_inc(v_name_2277_);
lean_dec_ref(v_toAttributeImplCore_2276_);
v___x_2278_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2265_);
v___x_2279_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2277_, v_decl_2203_, v___x_2278_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
return v___x_2279_;
}
else
{
lean_dec_ref(v_env_2265_);
v___y_2242_ = v___y_2268_;
v___y_2243_ = v___y_2270_;
goto v___jp_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2285_, lean_object* v_decl_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2285_, v_decl_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; lean_object* v_env_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; 
v___x_2299_ = lean_st_ref_get(v___y_2297_);
v_env_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc_ref(v_env_2300_);
lean_dec(v___x_2299_);
v___x_2301_ = 0;
lean_inc(v_constName_2293_);
v___x_2302_ = l_Lean_Environment_find_x3f(v_env_2300_, v_constName_2293_, v___x_2301_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v___x_2303_; 
v___x_2303_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
return v___x_2303_;
}
else
{
lean_object* v_val_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec(v_constName_2293_);
v_val_2304_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2302_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_val_2304_);
lean_dec(v___x_2302_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
lean_ctor_set_tag(v___x_2306_, 0);
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_val_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
return v_res_2318_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2322_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2323_ = lean_unsigned_to_nat(58u);
v___x_2324_ = lean_unsigned_to_nat(33u);
v___x_2325_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2326_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2327_ = l_mkPanicMessageWithDecl(v___x_2326_, v___x_2325_, v___x_2324_, v___x_2323_, v___x_2322_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2329_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2330_ = lean_unsigned_to_nat(60u);
v___x_2331_ = lean_unsigned_to_nat(30u);
v___x_2332_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2333_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2334_ = l_mkPanicMessageWithDecl(v___x_2333_, v___x_2332_, v___x_2331_, v___x_2330_, v___x_2329_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2335_, lean_object* v_indName_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v___x_2342_; 
lean_inc(v_indName_2336_);
v___x_2342_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2336_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
if (lean_obj_tag(v_a_2343_) == 5)
{
lean_object* v_val_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2534_; 
v_val_2344_ = lean_ctor_get(v_a_2343_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_a_2343_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2346_ = v_a_2343_;
v_isShared_2347_ = v_isSharedCheck_2534_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_val_2344_);
lean_dec(v_a_2343_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2534_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; 
lean_inc(v_indName_2336_);
v___x_2348_ = l_Lean_mkCasesOnName(v_indName_2336_);
lean_inc(v___x_2348_);
v___x_2349_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2348_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v_name_2351_; lean_object* v_levelParams_2352_; lean_object* v_type_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v_name_2351_ = lean_ctor_get(v_a_2350_, 0);
lean_inc(v_name_2351_);
v_levelParams_2352_ = lean_ctor_get(v_a_2350_, 1);
lean_inc_n(v_levelParams_2352_, 2);
v_type_2353_ = lean_ctor_get(v_a_2350_, 2);
lean_inc_ref(v_type_2353_);
lean_dec(v_a_2350_);
v___x_2354_ = lean_box(0);
v___x_2355_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2352_, v___x_2354_);
if (lean_obj_tag(v___x_2355_) == 1)
{
lean_object* v_head_2356_; lean_object* v_tail_2357_; lean_object* v_numParams_2358_; lean_object* v_numIndices_2359_; lean_object* v_ctors_2360_; lean_object* v___f_2361_; lean_object* v___x_2363_; 
v_head_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_head_2356_);
v_tail_2357_ = lean_ctor_get(v___x_2355_, 1);
lean_inc(v_tail_2357_);
v_numParams_2358_ = lean_ctor_get(v_val_2344_, 1);
lean_inc_n(v_numParams_2358_, 2);
v_numIndices_2359_ = lean_ctor_get(v_val_2344_, 2);
lean_inc(v_numIndices_2359_);
v_ctors_2360_ = lean_ctor_get(v_val_2344_, 4);
lean_inc(v_ctors_2360_);
v___f_2361_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2361_, 0, v_numIndices_2359_);
lean_closure_set(v___f_2361_, 1, v_head_2356_);
lean_closure_set(v___f_2361_, 2, v_ctors_2360_);
lean_closure_set(v___f_2361_, 3, v_indName_2336_);
lean_closure_set(v___f_2361_, 4, v_tail_2357_);
lean_closure_set(v___f_2361_, 5, v_name_2351_);
lean_closure_set(v___f_2361_, 6, v___x_2355_);
lean_closure_set(v___f_2361_, 7, v_numParams_2358_);
lean_closure_set(v___f_2361_, 8, v_val_2344_);
lean_closure_set(v___f_2361_, 9, v___x_2348_);
if (v_isShared_2347_ == 0)
{
lean_ctor_set_tag(v___x_2346_, 1);
lean_ctor_set(v___x_2346_, 0, v_numParams_2358_);
v___x_2363_ = v___x_2346_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_numParams_2358_);
v___x_2363_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
uint8_t v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = 0;
v___x_2365_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2353_, v___x_2363_, v___f_2361_, v___x_2364_, v___x_2364_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2365_) == 0)
{
lean_object* v_a_2366_; lean_object* v___x_2367_; lean_object* v___f_2368_; uint8_t v___y_2370_; uint8_t v___x_2513_; 
v_a_2366_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___x_2365_, 1);
v___x_2367_ = lean_box(v___x_2364_);
lean_inc(v_declName_2335_);
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2368_, 0, v_a_2366_);
lean_closure_set(v___f_2368_, 1, v_declName_2335_);
lean_closure_set(v___f_2368_, 2, v_levelParams_2352_);
lean_closure_set(v___f_2368_, 3, v___x_2367_);
v___x_2513_ = l_Lean_isPrivateName(v_declName_2335_);
if (v___x_2513_ == 0)
{
uint8_t v___x_2514_; 
v___x_2514_ = 1;
v___y_2370_ = v___x_2514_;
goto v___jp_2369_;
}
else
{
v___y_2370_ = v___x_2364_;
goto v___jp_2369_;
}
v___jp_2369_:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2368_, v___y_2370_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v___x_2372_; lean_object* v_env_2373_; lean_object* v_nextMacroScope_2374_; lean_object* v_ngen_2375_; lean_object* v_auxDeclNGen_2376_; lean_object* v_traceState_2377_; lean_object* v_recordedDeps_2378_; lean_object* v_messages_2379_; lean_object* v_infoState_2380_; lean_object* v_snapshotTasks_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref_known(v___x_2371_, 1);
v___x_2372_ = lean_st_ref_take(v_a_2340_);
v_env_2373_ = lean_ctor_get(v___x_2372_, 0);
v_nextMacroScope_2374_ = lean_ctor_get(v___x_2372_, 1);
v_ngen_2375_ = lean_ctor_get(v___x_2372_, 2);
v_auxDeclNGen_2376_ = lean_ctor_get(v___x_2372_, 3);
v_traceState_2377_ = lean_ctor_get(v___x_2372_, 4);
v_recordedDeps_2378_ = lean_ctor_get(v___x_2372_, 6);
v_messages_2379_ = lean_ctor_get(v___x_2372_, 7);
v_infoState_2380_ = lean_ctor_get(v___x_2372_, 8);
v_snapshotTasks_2381_ = lean_ctor_get(v___x_2372_, 9);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; 
v_unused_2512_ = lean_ctor_get(v___x_2372_, 5);
lean_dec(v_unused_2512_);
v___x_2383_ = v___x_2372_;
v_isShared_2384_ = v_isSharedCheck_2511_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_snapshotTasks_2381_);
lean_inc(v_infoState_2380_);
lean_inc(v_messages_2379_);
lean_inc(v_recordedDeps_2378_);
lean_inc(v_traceState_2377_);
lean_inc(v_auxDeclNGen_2376_);
lean_inc(v_ngen_2375_);
lean_inc(v_nextMacroScope_2374_);
lean_inc(v_env_2373_);
lean_dec(v___x_2372_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2511_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
lean_inc(v_declName_2335_);
v___x_2385_ = l_Lean_Meta_markMatcherLike(v_env_2373_, v_declName_2335_);
v___x_2386_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 5, v___x_2386_);
lean_ctor_set(v___x_2383_, 0, v___x_2385_);
v___x_2388_ = v___x_2383_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_nextMacroScope_2374_);
lean_ctor_set(v_reuseFailAlloc_2510_, 2, v_ngen_2375_);
lean_ctor_set(v_reuseFailAlloc_2510_, 3, v_auxDeclNGen_2376_);
lean_ctor_set(v_reuseFailAlloc_2510_, 4, v_traceState_2377_);
lean_ctor_set(v_reuseFailAlloc_2510_, 5, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2510_, 6, v_recordedDeps_2378_);
lean_ctor_set(v_reuseFailAlloc_2510_, 7, v_messages_2379_);
lean_ctor_set(v_reuseFailAlloc_2510_, 8, v_infoState_2380_);
lean_ctor_set(v_reuseFailAlloc_2510_, 9, v_snapshotTasks_2381_);
v___x_2388_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v_mctx_2391_; lean_object* v_zetaDeltaFVarIds_2392_; lean_object* v_postponed_2393_; lean_object* v_diag_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2508_; 
v___x_2389_ = lean_st_ref_put(v_a_2340_, v___x_2388_);
v___x_2390_ = lean_st_ref_take(v_a_2338_);
v_mctx_2391_ = lean_ctor_get(v___x_2390_, 0);
v_zetaDeltaFVarIds_2392_ = lean_ctor_get(v___x_2390_, 2);
v_postponed_2393_ = lean_ctor_get(v___x_2390_, 3);
v_diag_2394_ = lean_ctor_get(v___x_2390_, 4);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2508_ == 0)
{
lean_object* v_unused_2509_; 
v_unused_2509_ = lean_ctor_get(v___x_2390_, 1);
lean_dec(v_unused_2509_);
v___x_2396_ = v___x_2390_;
v_isShared_2397_ = v_isSharedCheck_2508_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_diag_2394_);
lean_inc(v_postponed_2393_);
lean_inc(v_zetaDeltaFVarIds_2392_);
lean_inc(v_mctx_2391_);
lean_dec(v___x_2390_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2508_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2400_; 
v___x_2398_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 1, v___x_2398_);
v___x_2400_ = v___x_2396_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_mctx_2391_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2507_, 2, v_zetaDeltaFVarIds_2392_);
lean_ctor_set(v_reuseFailAlloc_2507_, 3, v_postponed_2393_);
lean_ctor_set(v_reuseFailAlloc_2507_, 4, v_diag_2394_);
v___x_2400_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v_env_2403_; lean_object* v_nextMacroScope_2404_; lean_object* v_ngen_2405_; lean_object* v_auxDeclNGen_2406_; lean_object* v_traceState_2407_; lean_object* v_recordedDeps_2408_; lean_object* v_messages_2409_; lean_object* v_infoState_2410_; lean_object* v_snapshotTasks_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2505_; 
v___x_2401_ = lean_st_ref_put(v_a_2338_, v___x_2400_);
v___x_2402_ = lean_st_ref_take(v_a_2340_);
v_env_2403_ = lean_ctor_get(v___x_2402_, 0);
v_nextMacroScope_2404_ = lean_ctor_get(v___x_2402_, 1);
v_ngen_2405_ = lean_ctor_get(v___x_2402_, 2);
v_auxDeclNGen_2406_ = lean_ctor_get(v___x_2402_, 3);
v_traceState_2407_ = lean_ctor_get(v___x_2402_, 4);
v_recordedDeps_2408_ = lean_ctor_get(v___x_2402_, 6);
v_messages_2409_ = lean_ctor_get(v___x_2402_, 7);
v_infoState_2410_ = lean_ctor_get(v___x_2402_, 8);
v_snapshotTasks_2411_ = lean_ctor_get(v___x_2402_, 9);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v___x_2402_, 5);
lean_dec(v_unused_2506_);
v___x_2413_ = v___x_2402_;
v_isShared_2414_ = v_isSharedCheck_2505_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_snapshotTasks_2411_);
lean_inc(v_infoState_2410_);
lean_inc(v_messages_2409_);
lean_inc(v_recordedDeps_2408_);
lean_inc(v_traceState_2407_);
lean_inc(v_auxDeclNGen_2406_);
lean_inc(v_ngen_2405_);
lean_inc(v_nextMacroScope_2404_);
lean_inc(v_env_2403_);
lean_dec(v___x_2402_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2505_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2417_; 
lean_inc(v_declName_2335_);
v___x_2415_ = l_Lean_markAuxRecursor(v_env_2403_, v_declName_2335_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set(v___x_2413_, 5, v___x_2386_);
lean_ctor_set(v___x_2413_, 0, v___x_2415_);
v___x_2417_ = v___x_2413_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2504_, 1, v_nextMacroScope_2404_);
lean_ctor_set(v_reuseFailAlloc_2504_, 2, v_ngen_2405_);
lean_ctor_set(v_reuseFailAlloc_2504_, 3, v_auxDeclNGen_2406_);
lean_ctor_set(v_reuseFailAlloc_2504_, 4, v_traceState_2407_);
lean_ctor_set(v_reuseFailAlloc_2504_, 5, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2504_, 6, v_recordedDeps_2408_);
lean_ctor_set(v_reuseFailAlloc_2504_, 7, v_messages_2409_);
lean_ctor_set(v_reuseFailAlloc_2504_, 8, v_infoState_2410_);
lean_ctor_set(v_reuseFailAlloc_2504_, 9, v_snapshotTasks_2411_);
v___x_2417_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_mctx_2420_; lean_object* v_zetaDeltaFVarIds_2421_; lean_object* v_postponed_2422_; lean_object* v_diag_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2502_; 
v___x_2418_ = lean_st_ref_put(v_a_2340_, v___x_2417_);
v___x_2419_ = lean_st_ref_take(v_a_2338_);
v_mctx_2420_ = lean_ctor_get(v___x_2419_, 0);
v_zetaDeltaFVarIds_2421_ = lean_ctor_get(v___x_2419_, 2);
v_postponed_2422_ = lean_ctor_get(v___x_2419_, 3);
v_diag_2423_ = lean_ctor_get(v___x_2419_, 4);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2502_ == 0)
{
lean_object* v_unused_2503_; 
v_unused_2503_ = lean_ctor_get(v___x_2419_, 1);
lean_dec(v_unused_2503_);
v___x_2425_ = v___x_2419_;
v_isShared_2426_ = v_isSharedCheck_2502_;
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
v_isShared_2426_ = v_isSharedCheck_2502_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 1, v___x_2398_);
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_mctx_2420_);
lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2501_, 2, v_zetaDeltaFVarIds_2421_);
lean_ctor_set(v_reuseFailAlloc_2501_, 3, v_postponed_2422_);
lean_ctor_set(v_reuseFailAlloc_2501_, 4, v_diag_2423_);
v___x_2428_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v_env_2431_; lean_object* v_nextMacroScope_2432_; lean_object* v_ngen_2433_; lean_object* v_auxDeclNGen_2434_; lean_object* v_traceState_2435_; lean_object* v_recordedDeps_2436_; lean_object* v_messages_2437_; lean_object* v_infoState_2438_; lean_object* v_snapshotTasks_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2499_; 
v___x_2429_ = lean_st_ref_put(v_a_2338_, v___x_2428_);
v___x_2430_ = lean_st_ref_take(v_a_2340_);
v_env_2431_ = lean_ctor_get(v___x_2430_, 0);
v_nextMacroScope_2432_ = lean_ctor_get(v___x_2430_, 1);
v_ngen_2433_ = lean_ctor_get(v___x_2430_, 2);
v_auxDeclNGen_2434_ = lean_ctor_get(v___x_2430_, 3);
v_traceState_2435_ = lean_ctor_get(v___x_2430_, 4);
v_recordedDeps_2436_ = lean_ctor_get(v___x_2430_, 6);
v_messages_2437_ = lean_ctor_get(v___x_2430_, 7);
v_infoState_2438_ = lean_ctor_get(v___x_2430_, 8);
v_snapshotTasks_2439_ = lean_ctor_get(v___x_2430_, 9);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2499_ == 0)
{
lean_object* v_unused_2500_; 
v_unused_2500_ = lean_ctor_get(v___x_2430_, 5);
lean_dec(v_unused_2500_);
v___x_2441_ = v___x_2430_;
v_isShared_2442_ = v_isSharedCheck_2499_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_snapshotTasks_2439_);
lean_inc(v_infoState_2438_);
lean_inc(v_messages_2437_);
lean_inc(v_recordedDeps_2436_);
lean_inc(v_traceState_2435_);
lean_inc(v_auxDeclNGen_2434_);
lean_inc(v_ngen_2433_);
lean_inc(v_nextMacroScope_2432_);
lean_inc(v_env_2431_);
lean_dec(v___x_2430_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2499_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___x_2445_; 
lean_inc(v_declName_2335_);
v___x_2443_ = l_Lean_Meta_addToCompletionBlackList(v_env_2431_, v_declName_2335_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 5, v___x_2386_);
lean_ctor_set(v___x_2441_, 0, v___x_2443_);
v___x_2445_ = v___x_2441_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_nextMacroScope_2432_);
lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_ngen_2433_);
lean_ctor_set(v_reuseFailAlloc_2498_, 3, v_auxDeclNGen_2434_);
lean_ctor_set(v_reuseFailAlloc_2498_, 4, v_traceState_2435_);
lean_ctor_set(v_reuseFailAlloc_2498_, 5, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2498_, 6, v_recordedDeps_2436_);
lean_ctor_set(v_reuseFailAlloc_2498_, 7, v_messages_2437_);
lean_ctor_set(v_reuseFailAlloc_2498_, 8, v_infoState_2438_);
lean_ctor_set(v_reuseFailAlloc_2498_, 9, v_snapshotTasks_2439_);
v___x_2445_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v_mctx_2448_; lean_object* v_zetaDeltaFVarIds_2449_; lean_object* v_postponed_2450_; lean_object* v_diag_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2496_; 
v___x_2446_ = lean_st_ref_put(v_a_2340_, v___x_2445_);
v___x_2447_ = lean_st_ref_take(v_a_2338_);
v_mctx_2448_ = lean_ctor_get(v___x_2447_, 0);
v_zetaDeltaFVarIds_2449_ = lean_ctor_get(v___x_2447_, 2);
v_postponed_2450_ = lean_ctor_get(v___x_2447_, 3);
v_diag_2451_ = lean_ctor_get(v___x_2447_, 4);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2496_ == 0)
{
lean_object* v_unused_2497_; 
v_unused_2497_ = lean_ctor_get(v___x_2447_, 1);
lean_dec(v_unused_2497_);
v___x_2453_ = v___x_2447_;
v_isShared_2454_ = v_isSharedCheck_2496_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_diag_2451_);
lean_inc(v_postponed_2450_);
lean_inc(v_zetaDeltaFVarIds_2449_);
lean_inc(v_mctx_2448_);
lean_dec(v___x_2447_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2496_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 1, v___x_2398_);
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_mctx_2448_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2495_, 2, v_zetaDeltaFVarIds_2449_);
lean_ctor_set(v_reuseFailAlloc_2495_, 3, v_postponed_2450_);
lean_ctor_set(v_reuseFailAlloc_2495_, 4, v_diag_2451_);
v___x_2456_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v_env_2459_; lean_object* v_nextMacroScope_2460_; lean_object* v_ngen_2461_; lean_object* v_auxDeclNGen_2462_; lean_object* v_traceState_2463_; lean_object* v_recordedDeps_2464_; lean_object* v_messages_2465_; lean_object* v_infoState_2466_; lean_object* v_snapshotTasks_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2493_; 
v___x_2457_ = lean_st_ref_put(v_a_2338_, v___x_2456_);
v___x_2458_ = lean_st_ref_take(v_a_2340_);
v_env_2459_ = lean_ctor_get(v___x_2458_, 0);
v_nextMacroScope_2460_ = lean_ctor_get(v___x_2458_, 1);
v_ngen_2461_ = lean_ctor_get(v___x_2458_, 2);
v_auxDeclNGen_2462_ = lean_ctor_get(v___x_2458_, 3);
v_traceState_2463_ = lean_ctor_get(v___x_2458_, 4);
v_recordedDeps_2464_ = lean_ctor_get(v___x_2458_, 6);
v_messages_2465_ = lean_ctor_get(v___x_2458_, 7);
v_infoState_2466_ = lean_ctor_get(v___x_2458_, 8);
v_snapshotTasks_2467_ = lean_ctor_get(v___x_2458_, 9);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v___x_2458_, 5);
lean_dec(v_unused_2494_);
v___x_2469_ = v___x_2458_;
v_isShared_2470_ = v_isSharedCheck_2493_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_snapshotTasks_2467_);
lean_inc(v_infoState_2466_);
lean_inc(v_messages_2465_);
lean_inc(v_recordedDeps_2464_);
lean_inc(v_traceState_2463_);
lean_inc(v_auxDeclNGen_2462_);
lean_inc(v_ngen_2461_);
lean_inc(v_nextMacroScope_2460_);
lean_inc(v_env_2459_);
lean_dec(v___x_2458_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2493_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2471_; lean_object* v___x_2473_; 
lean_inc(v_declName_2335_);
v___x_2471_ = l_Lean_addProtected(v_env_2459_, v_declName_2335_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set(v___x_2469_, 5, v___x_2386_);
lean_ctor_set(v___x_2469_, 0, v___x_2471_);
v___x_2473_ = v___x_2469_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_nextMacroScope_2460_);
lean_ctor_set(v_reuseFailAlloc_2492_, 2, v_ngen_2461_);
lean_ctor_set(v_reuseFailAlloc_2492_, 3, v_auxDeclNGen_2462_);
lean_ctor_set(v_reuseFailAlloc_2492_, 4, v_traceState_2463_);
lean_ctor_set(v_reuseFailAlloc_2492_, 5, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2492_, 6, v_recordedDeps_2464_);
lean_ctor_set(v_reuseFailAlloc_2492_, 7, v_messages_2465_);
lean_ctor_set(v_reuseFailAlloc_2492_, 8, v_infoState_2466_);
lean_ctor_set(v_reuseFailAlloc_2492_, 9, v_snapshotTasks_2467_);
v___x_2473_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v_mctx_2476_; lean_object* v_zetaDeltaFVarIds_2477_; lean_object* v_postponed_2478_; lean_object* v_diag_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2490_; 
v___x_2474_ = lean_st_ref_put(v_a_2340_, v___x_2473_);
v___x_2475_ = lean_st_ref_take(v_a_2338_);
v_mctx_2476_ = lean_ctor_get(v___x_2475_, 0);
v_zetaDeltaFVarIds_2477_ = lean_ctor_get(v___x_2475_, 2);
v_postponed_2478_ = lean_ctor_get(v___x_2475_, 3);
v_diag_2479_ = lean_ctor_get(v___x_2475_, 4);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2475_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v___x_2475_, 1);
lean_dec(v_unused_2491_);
v___x_2481_ = v___x_2475_;
v_isShared_2482_ = v_isSharedCheck_2490_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_diag_2479_);
lean_inc(v_postponed_2478_);
lean_inc(v_zetaDeltaFVarIds_2477_);
lean_inc(v_mctx_2476_);
lean_dec(v___x_2475_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2490_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 1, v___x_2398_);
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_mctx_2476_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v_zetaDeltaFVarIds_2477_);
lean_ctor_set(v_reuseFailAlloc_2489_, 3, v_postponed_2478_);
lean_ctor_set(v_reuseFailAlloc_2489_, 4, v_diag_2479_);
v___x_2484_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2485_ = lean_st_ref_put(v_a_2338_, v___x_2484_);
v___x_2486_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2335_);
v___x_2487_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2486_, v_declName_2335_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v___x_2488_; 
lean_dec_ref_known(v___x_2487_, 1);
v___x_2488_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2335_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_2488_;
}
else
{
lean_dec(v_declName_2335_);
return v___x_2487_;
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
lean_dec(v_declName_2335_);
return v___x_2371_;
}
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v_levelParams_2352_);
lean_dec(v_declName_2335_);
v_a_2515_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2365_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2365_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
else
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_dec(v___x_2355_);
lean_dec_ref(v_type_2353_);
lean_dec(v_levelParams_2352_);
lean_dec(v_name_2351_);
lean_dec(v___x_2348_);
lean_del_object(v___x_2346_);
lean_dec_ref(v_val_2344_);
lean_dec(v_indName_2336_);
lean_dec(v_declName_2335_);
v___x_2524_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2525_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2524_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_2525_;
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
lean_dec(v___x_2348_);
lean_del_object(v___x_2346_);
lean_dec_ref(v_val_2344_);
lean_dec(v_indName_2336_);
lean_dec(v_declName_2335_);
v_a_2526_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2349_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2349_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec(v_a_2343_);
lean_dec(v_indName_2336_);
lean_dec(v_declName_2335_);
v___x_2535_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2536_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2535_, v_a_2337_, v_a_2338_, v_a_2339_, v_a_2340_);
return v___x_2536_;
}
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec(v_indName_2336_);
lean_dec(v_declName_2335_);
v_a_2537_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2342_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2342_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2545_, lean_object* v_indName_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2545_, v_indName_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
lean_dec(v_a_2548_);
lean_dec_ref(v_a_2547_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2553_, lean_object* v_name_2554_, lean_object* v_type_2555_, lean_object* v_k_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2554_, v_type_2555_, v_k_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2563_, lean_object* v_name_2564_, lean_object* v_type_2565_, lean_object* v_k_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2563_, v_name_2564_, v_type_2565_, v_k_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2573_, lean_object* v_params_2574_, lean_object* v_alts_2575_, lean_object* v___x_2576_, lean_object* v_ism2_2577_, lean_object* v_motive_2578_, lean_object* v_val_2579_, lean_object* v_indName_2580_, lean_object* v___x_2581_, lean_object* v___x_2582_, lean_object* v___x_2583_, lean_object* v_as_2584_, size_t v_sz_2585_, size_t v_i_2586_, lean_object* v_bs_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v___x_2593_; 
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2573_, v_params_2574_, v_alts_2575_, v___x_2576_, v_ism2_2577_, v_motive_2578_, v_val_2579_, v_indName_2580_, v___x_2581_, v___x_2582_, v___x_2583_, v_sz_2585_, v_i_2586_, v_bs_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
return v___x_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2594_ = _args[0];
lean_object* v_params_2595_ = _args[1];
lean_object* v_alts_2596_ = _args[2];
lean_object* v___x_2597_ = _args[3];
lean_object* v_ism2_2598_ = _args[4];
lean_object* v_motive_2599_ = _args[5];
lean_object* v_val_2600_ = _args[6];
lean_object* v_indName_2601_ = _args[7];
lean_object* v___x_2602_ = _args[8];
lean_object* v___x_2603_ = _args[9];
lean_object* v___x_2604_ = _args[10];
lean_object* v_as_2605_ = _args[11];
lean_object* v_sz_2606_ = _args[12];
lean_object* v_i_2607_ = _args[13];
lean_object* v_bs_2608_ = _args[14];
lean_object* v___y_2609_ = _args[15];
lean_object* v___y_2610_ = _args[16];
lean_object* v___y_2611_ = _args[17];
lean_object* v___y_2612_ = _args[18];
lean_object* v___y_2613_ = _args[19];
_start:
{
size_t v_sz_boxed_2614_; size_t v_i_boxed_2615_; lean_object* v_res_2616_; 
v_sz_boxed_2614_ = lean_unbox_usize(v_sz_2606_);
lean_dec(v_sz_2606_);
v_i_boxed_2615_ = lean_unbox_usize(v_i_2607_);
lean_dec(v_i_2607_);
v_res_2616_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2594_, v_params_2595_, v_alts_2596_, v___x_2597_, v_ism2_2598_, v_motive_2599_, v_val_2600_, v_indName_2601_, v___x_2602_, v___x_2603_, v___x_2604_, v_as_2605_, v_sz_boxed_2614_, v_i_boxed_2615_, v_bs_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v_as_2605_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2617_, lean_object* v_params_2618_, lean_object* v___x_2619_, lean_object* v_motive_2620_, lean_object* v_as_2621_, size_t v_sz_2622_, size_t v_i_2623_, lean_object* v_bs_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___x_2630_; 
v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2617_, v_params_2618_, v___x_2619_, v_motive_2620_, v_sz_2622_, v_i_2623_, v_bs_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
return v___x_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2631_, lean_object* v_params_2632_, lean_object* v___x_2633_, lean_object* v_motive_2634_, lean_object* v_as_2635_, lean_object* v_sz_2636_, lean_object* v_i_2637_, lean_object* v_bs_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
size_t v_sz_boxed_2644_; size_t v_i_boxed_2645_; lean_object* v_res_2646_; 
v_sz_boxed_2644_ = lean_unbox_usize(v_sz_2636_);
lean_dec(v_sz_2636_);
v_i_boxed_2645_ = lean_unbox_usize(v_i_2637_);
lean_dec(v_i_2637_);
v_res_2646_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2631_, v_params_2632_, v___x_2633_, v_motive_2634_, v_as_2635_, v_sz_boxed_2644_, v_i_boxed_2645_, v_bs_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec_ref(v_as_2635_);
lean_dec_ref(v_params_2632_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2647_, uint8_t v_s_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2647_, v_s_2648_, v___y_2650_, v___y_2652_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2655_, lean_object* v_s_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
uint8_t v_s_boxed_2662_; lean_object* v_res_2663_; 
v_s_boxed_2662_ = lean_unbox(v_s_2656_);
v_res_2663_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2655_, v_s_boxed_2662_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2664_, lean_object* v_constName_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2672_, lean_object* v_constName_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2672_, v_constName_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2680_, lean_object* v_attrName_2681_, lean_object* v_declName_2682_, lean_object* v_asyncPrefix_x3f_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2681_, v_declName_2682_, v_asyncPrefix_x3f_2683_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2690_, lean_object* v_attrName_2691_, lean_object* v_declName_2692_, lean_object* v_asyncPrefix_x3f_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2690_, v_attrName_2691_, v_declName_2692_, v_asyncPrefix_x3f_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2700_, lean_object* v_attrName_2701_, lean_object* v_declName_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2701_, v_declName_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2709_, lean_object* v_attrName_2710_, lean_object* v_declName_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2709_, v_attrName_2710_, v_declName_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2718_, lean_object* v_ref_2719_, lean_object* v_constName_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2719_, v_constName_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2727_, lean_object* v_ref_2728_, lean_object* v_constName_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2727_, v_ref_2728_, v_constName_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v_ref_2728_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2736_, lean_object* v_msg_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2744_, lean_object* v_msg_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2744_, v_msg_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2752_, lean_object* v_ref_2753_, lean_object* v_msg_2754_, lean_object* v_declHint_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2753_, v_msg_2754_, v_declHint_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2762_, lean_object* v_ref_2763_, lean_object* v_msg_2764_, lean_object* v_declHint_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2762_, v_ref_2763_, v_msg_2764_, v_declHint_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec(v_ref_2763_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2772_, lean_object* v_declHint_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2772_, v_declHint_2773_, v___y_2777_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2780_, lean_object* v_declHint_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2780_, v_declHint_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2788_, lean_object* v_ref_2789_, lean_object* v_msg_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; 
v___x_2796_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2789_, v_msg_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2797_, lean_object* v_ref_2798_, lean_object* v_msg_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2797_, v_ref_2798_, v_msg_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v_ref_2798_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2806_, lean_object* v___y_2807_){
_start:
{
uint8_t v___x_2809_; 
v___x_2809_ = l_Lean_Expr_hasMVar(v_e_2806_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
v___x_2810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2810_, 0, v_e_2806_);
return v___x_2810_;
}
else
{
lean_object* v___x_2811_; lean_object* v_mctx_2812_; lean_object* v___x_2813_; lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v___x_2816_; lean_object* v_cache_2817_; lean_object* v_zetaDeltaFVarIds_2818_; lean_object* v_postponed_2819_; lean_object* v_diag_2820_; lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2829_; 
v___x_2811_ = lean_st_ref_get(v___y_2807_);
v_mctx_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc_ref(v_mctx_2812_);
lean_dec(v___x_2811_);
v___x_2813_ = l_Lean_instantiateMVarsCore(v_mctx_2812_, v_e_2806_);
v_fst_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_fst_2814_);
v_snd_2815_ = lean_ctor_get(v___x_2813_, 1);
lean_inc(v_snd_2815_);
lean_dec_ref(v___x_2813_);
v___x_2816_ = lean_st_ref_take(v___y_2807_);
v_cache_2817_ = lean_ctor_get(v___x_2816_, 1);
v_zetaDeltaFVarIds_2818_ = lean_ctor_get(v___x_2816_, 2);
v_postponed_2819_ = lean_ctor_get(v___x_2816_, 3);
v_diag_2820_ = lean_ctor_get(v___x_2816_, 4);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2829_ == 0)
{
lean_object* v_unused_2830_; 
v_unused_2830_ = lean_ctor_get(v___x_2816_, 0);
lean_dec(v_unused_2830_);
v___x_2822_ = v___x_2816_;
v_isShared_2823_ = v_isSharedCheck_2829_;
goto v_resetjp_2821_;
}
else
{
lean_inc(v_diag_2820_);
lean_inc(v_postponed_2819_);
lean_inc(v_zetaDeltaFVarIds_2818_);
lean_inc(v_cache_2817_);
lean_dec(v___x_2816_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2829_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v_snd_2815_);
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_snd_2815_);
lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_cache_2817_);
lean_ctor_set(v_reuseFailAlloc_2828_, 2, v_zetaDeltaFVarIds_2818_);
lean_ctor_set(v_reuseFailAlloc_2828_, 3, v_postponed_2819_);
lean_ctor_set(v_reuseFailAlloc_2828_, 4, v_diag_2820_);
v___x_2825_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_st_ref_put(v___y_2807_, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v_fst_2814_);
return v___x_2827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2831_, v___y_2832_);
lean_dec(v___y_2832_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2835_, v___y_2837_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec(v___y_2846_);
lean_dec_ref(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2849_, lean_object* v_info_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_){
_start:
{
lean_object* v___x_2854_; lean_object* v_env_2855_; lean_object* v_nextMacroScope_2856_; lean_object* v_ngen_2857_; lean_object* v_auxDeclNGen_2858_; lean_object* v_traceState_2859_; lean_object* v_recordedDeps_2860_; lean_object* v_messages_2861_; lean_object* v_infoState_2862_; lean_object* v_snapshotTasks_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2890_; 
v___x_2854_ = lean_st_ref_take(v___y_2852_);
v_env_2855_ = lean_ctor_get(v___x_2854_, 0);
v_nextMacroScope_2856_ = lean_ctor_get(v___x_2854_, 1);
v_ngen_2857_ = lean_ctor_get(v___x_2854_, 2);
v_auxDeclNGen_2858_ = lean_ctor_get(v___x_2854_, 3);
v_traceState_2859_ = lean_ctor_get(v___x_2854_, 4);
v_recordedDeps_2860_ = lean_ctor_get(v___x_2854_, 6);
v_messages_2861_ = lean_ctor_get(v___x_2854_, 7);
v_infoState_2862_ = lean_ctor_get(v___x_2854_, 8);
v_snapshotTasks_2863_ = lean_ctor_get(v___x_2854_, 9);
v_isSharedCheck_2890_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2890_ == 0)
{
lean_object* v_unused_2891_; 
v_unused_2891_ = lean_ctor_get(v___x_2854_, 5);
lean_dec(v_unused_2891_);
v___x_2865_ = v___x_2854_;
v_isShared_2866_ = v_isSharedCheck_2890_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_snapshotTasks_2863_);
lean_inc(v_infoState_2862_);
lean_inc(v_messages_2861_);
lean_inc(v_recordedDeps_2860_);
lean_inc(v_traceState_2859_);
lean_inc(v_auxDeclNGen_2858_);
lean_inc(v_ngen_2857_);
lean_inc(v_nextMacroScope_2856_);
lean_inc(v_env_2855_);
lean_dec(v___x_2854_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2890_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2867_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2855_, v_matcherName_2849_, v_info_2850_);
v___x_2868_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 5, v___x_2868_);
lean_ctor_set(v___x_2865_, 0, v___x_2867_);
v___x_2870_ = v___x_2865_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_nextMacroScope_2856_);
lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_ngen_2857_);
lean_ctor_set(v_reuseFailAlloc_2889_, 3, v_auxDeclNGen_2858_);
lean_ctor_set(v_reuseFailAlloc_2889_, 4, v_traceState_2859_);
lean_ctor_set(v_reuseFailAlloc_2889_, 5, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2889_, 6, v_recordedDeps_2860_);
lean_ctor_set(v_reuseFailAlloc_2889_, 7, v_messages_2861_);
lean_ctor_set(v_reuseFailAlloc_2889_, 8, v_infoState_2862_);
lean_ctor_set(v_reuseFailAlloc_2889_, 9, v_snapshotTasks_2863_);
v___x_2870_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v_mctx_2873_; lean_object* v_zetaDeltaFVarIds_2874_; lean_object* v_postponed_2875_; lean_object* v_diag_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2887_; 
v___x_2871_ = lean_st_ref_put(v___y_2852_, v___x_2870_);
v___x_2872_ = lean_st_ref_take(v___y_2851_);
v_mctx_2873_ = lean_ctor_get(v___x_2872_, 0);
v_zetaDeltaFVarIds_2874_ = lean_ctor_get(v___x_2872_, 2);
v_postponed_2875_ = lean_ctor_get(v___x_2872_, 3);
v_diag_2876_ = lean_ctor_get(v___x_2872_, 4);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v___x_2872_, 1);
lean_dec(v_unused_2888_);
v___x_2878_ = v___x_2872_;
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_diag_2876_);
lean_inc(v_postponed_2875_);
lean_inc(v_zetaDeltaFVarIds_2874_);
lean_inc(v_mctx_2873_);
lean_dec(v___x_2872_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2887_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2880_ = lean_box(0);
v___x_2881_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 1, v___x_2881_);
v___x_2883_ = v___x_2878_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_mctx_2873_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2886_, 2, v_zetaDeltaFVarIds_2874_);
lean_ctor_set(v_reuseFailAlloc_2886_, 3, v_postponed_2875_);
lean_ctor_set(v_reuseFailAlloc_2886_, 4, v_diag_2876_);
v___x_2883_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_st_ref_put(v___y_2851_, v___x_2883_);
v___x_2885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2885_, 0, v___x_2880_);
return v___x_2885_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2892_, lean_object* v_info_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2892_, v_info_2893_, v___y_2894_, v___y_2895_);
lean_dec(v___y_2895_);
lean_dec(v___y_2894_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2898_, lean_object* v_info_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2898_, v_info_2899_, v___y_2901_, v___y_2903_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2906_, lean_object* v_info_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2906_, v_info_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2914_, lean_object* v___x_2915_, lean_object* v_newEqs1_2916_, uint8_t v___x_2917_, uint8_t v___x_2918_, uint8_t v___x_2919_, lean_object* v_ism1_x27_2920_, lean_object* v_ism2_x27_2921_, lean_object* v_newRefls1_2922_, lean_object* v_newEqs2_2923_, lean_object* v_newRefls2_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2930_ = l_Lean_mkAppN(v_motive_2914_, v___x_2915_);
v___x_2931_ = l_Array_append___redArg(v_newEqs1_2916_, v_newEqs2_2923_);
v___x_2932_ = l_Lean_Meta_mkForallFVars(v___x_2931_, v___x_2930_, v___x_2917_, v___x_2918_, v___x_2918_, v___x_2919_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec_ref(v___x_2931_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v___x_2932_, 1);
v___x_2934_ = l_Array_append___redArg(v_ism1_x27_2920_, v_ism2_x27_2921_);
v___x_2935_ = l_Lean_Meta_mkLambdaFVars(v___x_2934_, v_a_2933_, v___x_2917_, v___x_2918_, v___x_2917_, v___x_2918_, v___x_2919_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec_ref(v___x_2934_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2945_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2938_ = v___x_2935_;
v_isShared_2939_ = v_isSharedCheck_2945_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2935_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2945_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2943_; 
v___x_2940_ = l_Array_append___redArg(v_newRefls1_2922_, v_newRefls2_2924_);
v___x_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2941_, 0, v_a_2936_);
lean_ctor_set(v___x_2941_, 1, v___x_2940_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2941_);
v___x_2943_ = v___x_2938_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2941_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec_ref(v_newRefls1_2922_);
v_a_2946_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2935_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2935_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v_newRefls1_2922_);
lean_dec_ref(v_ism1_x27_2920_);
v_a_2954_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2932_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2932_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2962_, lean_object* v___x_2963_, lean_object* v_newEqs1_2964_, lean_object* v___x_2965_, lean_object* v___x_2966_, lean_object* v___x_2967_, lean_object* v_ism1_x27_2968_, lean_object* v_ism2_x27_2969_, lean_object* v_newRefls1_2970_, lean_object* v_newEqs2_2971_, lean_object* v_newRefls2_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
uint8_t v___x_14975__boxed_2978_; uint8_t v___x_14976__boxed_2979_; uint8_t v___x_14977__boxed_2980_; lean_object* v_res_2981_; 
v___x_14975__boxed_2978_ = lean_unbox(v___x_2965_);
v___x_14976__boxed_2979_ = lean_unbox(v___x_2966_);
v___x_14977__boxed_2980_ = lean_unbox(v___x_2967_);
v_res_2981_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2962_, v___x_2963_, v_newEqs1_2964_, v___x_14975__boxed_2978_, v___x_14976__boxed_2979_, v___x_14977__boxed_2980_, v_ism1_x27_2968_, v_ism2_x27_2969_, v_newRefls1_2970_, v_newEqs2_2971_, v_newRefls2_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec_ref(v_newRefls2_2972_);
lean_dec_ref(v_newEqs2_2971_);
lean_dec_ref(v_ism2_x27_2969_);
lean_dec_ref(v___x_2963_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2982_, lean_object* v___x_2983_, uint8_t v___x_2984_, uint8_t v___x_2985_, uint8_t v___x_2986_, lean_object* v_ism1_x27_2987_, lean_object* v_ism2_x27_2988_, lean_object* v_is_2989_, lean_object* v___x_2990_, lean_object* v_newEqs1_2991_, lean_object* v_newRefls1_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___f_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_2998_ = lean_box(v___x_2984_);
v___x_2999_ = lean_box(v___x_2985_);
v___x_3000_ = lean_box(v___x_2986_);
lean_inc_ref(v_ism2_x27_2988_);
v___f_3001_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3001_, 0, v_motive_2982_);
lean_closure_set(v___f_3001_, 1, v___x_2983_);
lean_closure_set(v___f_3001_, 2, v_newEqs1_2991_);
lean_closure_set(v___f_3001_, 3, v___x_2998_);
lean_closure_set(v___f_3001_, 4, v___x_2999_);
lean_closure_set(v___f_3001_, 5, v___x_3000_);
lean_closure_set(v___f_3001_, 6, v_ism1_x27_2987_);
lean_closure_set(v___f_3001_, 7, v_ism2_x27_2988_);
lean_closure_set(v___f_3001_, 8, v_newRefls1_2992_);
v___x_3002_ = lean_array_push(v_is_2989_, v___x_2990_);
v___x_3003_ = l_Lean_Meta_withNewEqs___redArg(v___x_3002_, v_ism2_x27_2988_, v___f_3001_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_3004_, lean_object* v___x_3005_, lean_object* v___x_3006_, lean_object* v___x_3007_, lean_object* v___x_3008_, lean_object* v_ism1_x27_3009_, lean_object* v_ism2_x27_3010_, lean_object* v_is_3011_, lean_object* v___x_3012_, lean_object* v_newEqs1_3013_, lean_object* v_newRefls1_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_){
_start:
{
uint8_t v___x_15066__boxed_3020_; uint8_t v___x_15067__boxed_3021_; uint8_t v___x_15068__boxed_3022_; lean_object* v_res_3023_; 
v___x_15066__boxed_3020_ = lean_unbox(v___x_3006_);
v___x_15067__boxed_3021_ = lean_unbox(v___x_3007_);
v___x_15068__boxed_3022_ = lean_unbox(v___x_3008_);
v_res_3023_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_3004_, v___x_3005_, v___x_15066__boxed_3020_, v___x_15067__boxed_3021_, v___x_15068__boxed_3022_, v_ism1_x27_3009_, v_ism2_x27_3010_, v_is_3011_, v___x_3012_, v_newEqs1_3013_, v_newRefls1_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_3024_, uint8_t v___x_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l_Lean_addDecl(v___x_3024_, v___x_3025_, v___y_3028_, v___y_3029_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3032_, lean_object* v___x_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_){
_start:
{
uint8_t v___x_15108__boxed_3039_; lean_object* v_res_3040_; 
v___x_15108__boxed_3039_ = lean_unbox(v___x_3033_);
v_res_3040_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3032_, v___x_15108__boxed_3039_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
lean_dec(v___y_3035_);
lean_dec_ref(v___y_3034_);
return v_res_3040_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3043_ = l_Lean_stringToMessageData(v___x_3042_);
return v___x_3043_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3046_ = l_Lean_stringToMessageData(v___x_3045_);
return v___x_3046_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3052_ = lean_box(0);
v___x_3053_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3054_ = l_Lean_mkConst(v___x_3053_, v___x_3052_);
return v___x_3054_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3057_ = l_Lean_stringToMessageData(v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3058_, lean_object* v_a_3059_, lean_object* v___x_3060_, lean_object* v_zs1_3061_, lean_object* v_snd_3062_, uint8_t v___x_3063_, uint8_t v___x_3064_, uint8_t v___x_3065_, lean_object* v_alts_3066_, lean_object* v_zs2_3067_, lean_object* v___ctorRet2_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3074_ = lean_array_get_borrowed(v___x_3058_, v_a_3059_, v___x_3060_);
lean_inc_ref(v_zs1_3061_);
v___x_3075_ = l_Array_append___redArg(v_zs1_3061_, v_zs2_3067_);
lean_inc(v___x_3074_);
v___x_3076_ = l_Lean_Meta_instantiateForall(v___x_3074_, v___x_3075_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = lean_box(0);
v___x_3079_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3077_, v___x_3078_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3079_) == 0)
{
lean_object* v_a_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
lean_inc(v_a_3080_);
lean_dec_ref_known(v___x_3079_, 1);
v___x_3081_ = l_Lean_Expr_mvarId_x21(v_a_3080_);
v___x_3082_ = lean_array_get_size(v_snd_3062_);
v___x_3083_ = lean_box(0);
v___x_3084_ = lean_box(0);
lean_inc_ref(v___y_3071_);
v___x_3085_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3082_, v___x_3081_, v___x_3083_, v___x_3084_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3085_, 1);
if (lean_obj_tag(v_a_3086_) == 1)
{
lean_object* v_val_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3134_; 
v_val_3087_ = lean_ctor_get(v_a_3086_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_a_3086_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3089_ = v_a_3086_;
v_isShared_3090_ = v_isSharedCheck_3134_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_val_3087_);
lean_dec(v_a_3086_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3134_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v_fst_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3132_; 
v_fst_3091_ = lean_ctor_get(v_val_3087_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_val_3087_);
if (v_isSharedCheck_3132_ == 0)
{
lean_object* v_unused_3133_; 
v_unused_3133_ = lean_ctor_get(v_val_3087_, 1);
lean_dec(v_unused_3133_);
v___x_3093_ = v_val_3087_;
v_isShared_3094_ = v_isSharedCheck_3132_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_fst_3091_);
lean_dec(v_val_3087_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3132_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___y_3096_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; uint8_t v___x_3127_; 
v___x_3124_ = lean_array_get_borrowed(v___x_3058_, v_alts_3066_, v___x_3060_);
v___x_3125_ = lean_array_get_size(v_zs1_3061_);
lean_dec_ref(v_zs1_3061_);
v___x_3126_ = lean_unsigned_to_nat(0u);
v___x_3127_ = lean_nat_dec_eq(v___x_3125_, v___x_3126_);
if (v___x_3127_ == 0)
{
lean_inc(v___x_3124_);
v___y_3096_ = v___x_3124_;
goto v___jp_3095_;
}
else
{
lean_object* v___x_3128_; uint8_t v___x_3129_; 
v___x_3128_ = lean_array_get_size(v_zs2_3067_);
v___x_3129_ = lean_nat_dec_eq(v___x_3128_, v___x_3126_);
if (v___x_3129_ == 0)
{
lean_inc(v___x_3124_);
v___y_3096_ = v___x_3124_;
goto v___jp_3095_;
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3124_);
v___x_3131_ = l_Lean_Expr_app___override(v___x_3124_, v___x_3130_);
v___y_3096_ = v___x_3131_;
goto v___jp_3095_;
}
}
v___jp_3095_:
{
uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3097_ = 0;
v___x_3098_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3098_, 0, v___x_3097_);
lean_ctor_set_uint8(v___x_3098_, 1, v___x_3063_);
lean_ctor_set_uint8(v___x_3098_, 2, v___x_3064_);
lean_ctor_set_uint8(v___x_3098_, 3, v___x_3063_);
lean_inc_ref(v___y_3096_);
lean_inc(v_fst_3091_);
v___x_3099_ = l_Lean_MVarId_apply(v_fst_3091_, v___y_3096_, v___x_3098_, v___x_3084_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3099_, 1);
if (lean_obj_tag(v_a_3100_) == 0)
{
lean_object* v___x_3101_; 
lean_dec_ref(v___y_3096_);
lean_del_object(v___x_3093_);
lean_dec(v_fst_3091_);
lean_del_object(v___x_3089_);
v___x_3101_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3080_, v___y_3070_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; lean_object* v___x_3103_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v___x_3103_ = l_Lean_Meta_mkLambdaFVars(v___x_3075_, v_a_3102_, v___x_3064_, v___x_3063_, v___x_3064_, v___x_3063_, v___x_3065_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec_ref(v___x_3075_);
return v___x_3103_;
}
else
{
lean_dec_ref(v___x_3075_);
return v___x_3101_;
}
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3107_; 
lean_dec(v_a_3100_);
lean_dec(v_a_3080_);
lean_dec_ref(v___x_3075_);
v___x_3104_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3105_ = l_Lean_MessageData_ofExpr(v___y_3096_);
if (v_isShared_3094_ == 0)
{
lean_ctor_set_tag(v___x_3093_, 7);
lean_ctor_set(v___x_3093_, 1, v___x_3105_);
lean_ctor_set(v___x_3093_, 0, v___x_3104_);
v___x_3107_ = v___x_3093_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3104_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v___x_3105_);
v___x_3107_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3108_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v_fst_3091_);
v___x_3111_ = v___x_3089_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_fst_3091_);
v___x_3111_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3109_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v___x_3113_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3112_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
return v___x_3113_;
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec_ref(v___y_3096_);
lean_del_object(v___x_3093_);
lean_dec(v_fst_3091_);
lean_del_object(v___x_3089_);
lean_dec(v_a_3080_);
lean_dec_ref(v___x_3075_);
v_a_3116_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3099_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3099_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3135_; lean_object* v___x_3136_; 
lean_dec(v_a_3086_);
lean_dec(v_a_3080_);
lean_dec_ref(v___x_3075_);
lean_dec_ref(v_zs1_3061_);
v___x_3135_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3136_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3135_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
return v___x_3136_;
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec(v_a_3080_);
lean_dec_ref(v___x_3075_);
lean_dec_ref(v_zs1_3061_);
v_a_3137_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3085_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3085_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_dec_ref(v___x_3075_);
lean_dec_ref(v_zs1_3061_);
return v___x_3079_;
}
}
else
{
lean_dec_ref(v___x_3075_);
lean_dec_ref(v_zs1_3061_);
return v___x_3076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3145_, lean_object* v_a_3146_, lean_object* v___x_3147_, lean_object* v_zs1_3148_, lean_object* v_snd_3149_, lean_object* v___x_3150_, lean_object* v___x_3151_, lean_object* v___x_3152_, lean_object* v_alts_3153_, lean_object* v_zs2_3154_, lean_object* v___ctorRet2_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
uint8_t v___x_15168__boxed_3161_; uint8_t v___x_15169__boxed_3162_; uint8_t v___x_15170__boxed_3163_; lean_object* v_res_3164_; 
v___x_15168__boxed_3161_ = lean_unbox(v___x_3150_);
v___x_15169__boxed_3162_ = lean_unbox(v___x_3151_);
v___x_15170__boxed_3163_ = lean_unbox(v___x_3152_);
v_res_3164_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3145_, v_a_3146_, v___x_3147_, v_zs1_3148_, v_snd_3149_, v___x_15168__boxed_3161_, v___x_15169__boxed_3162_, v___x_15170__boxed_3163_, v_alts_3153_, v_zs2_3154_, v___ctorRet2_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec_ref(v___ctorRet2_3155_);
lean_dec_ref(v_zs2_3154_);
lean_dec_ref(v_alts_3153_);
lean_dec_ref(v_snd_3149_);
lean_dec(v___x_3147_);
lean_dec_ref(v_a_3146_);
lean_dec_ref(v___x_3145_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3165_, lean_object* v_a_3166_, lean_object* v___x_3167_, lean_object* v_snd_3168_, uint8_t v___x_3169_, uint8_t v___x_3170_, uint8_t v___x_3171_, lean_object* v_alts_3172_, lean_object* v_a_3173_, lean_object* v_zs1_3174_, lean_object* v___ctorRet1_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___f_3184_; lean_object* v___x_3185_; 
v___x_3181_ = lean_box(v___x_3169_);
v___x_3182_ = lean_box(v___x_3170_);
v___x_3183_ = lean_box(v___x_3171_);
v___f_3184_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3184_, 0, v___x_3165_);
lean_closure_set(v___f_3184_, 1, v_a_3166_);
lean_closure_set(v___f_3184_, 2, v___x_3167_);
lean_closure_set(v___f_3184_, 3, v_zs1_3174_);
lean_closure_set(v___f_3184_, 4, v_snd_3168_);
lean_closure_set(v___f_3184_, 5, v___x_3181_);
lean_closure_set(v___f_3184_, 6, v___x_3182_);
lean_closure_set(v___f_3184_, 7, v___x_3183_);
lean_closure_set(v___f_3184_, 8, v_alts_3172_);
v___x_3185_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3173_, v___f_3184_, v___x_3170_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3186_, lean_object* v_a_3187_, lean_object* v___x_3188_, lean_object* v_snd_3189_, lean_object* v___x_3190_, lean_object* v___x_3191_, lean_object* v___x_3192_, lean_object* v_alts_3193_, lean_object* v_a_3194_, lean_object* v_zs1_3195_, lean_object* v___ctorRet1_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
uint8_t v___x_15367__boxed_3202_; uint8_t v___x_15368__boxed_3203_; uint8_t v___x_15369__boxed_3204_; lean_object* v_res_3205_; 
v___x_15367__boxed_3202_ = lean_unbox(v___x_3190_);
v___x_15368__boxed_3203_ = lean_unbox(v___x_3191_);
v___x_15369__boxed_3204_ = lean_unbox(v___x_3192_);
v_res_3205_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3186_, v_a_3187_, v___x_3188_, v_snd_3189_, v___x_15367__boxed_3202_, v___x_15368__boxed_3203_, v___x_15369__boxed_3204_, v_alts_3193_, v_a_3194_, v_zs1_3195_, v___ctorRet1_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec_ref(v___ctorRet1_3196_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3206_, lean_object* v_params_3207_, lean_object* v_a_3208_, lean_object* v_snd_3209_, lean_object* v_alts_3210_, size_t v_sz_3211_, size_t v_i_3212_, lean_object* v_bs_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
uint8_t v___x_3219_; 
v___x_3219_ = lean_usize_dec_lt(v_i_3212_, v_sz_3211_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3220_; 
lean_dec_ref(v_alts_3210_);
lean_dec_ref(v_snd_3209_);
lean_dec_ref(v_a_3208_);
lean_dec(v_tail_3206_);
v___x_3220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3220_, 0, v_bs_3213_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; uint8_t v___x_3222_; uint8_t v___x_3223_; lean_object* v_v_3224_; lean_object* v___x_3225_; lean_object* v_bs_x27_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3221_ = l_Lean_instInhabitedExpr;
v___x_3222_ = 0;
v___x_3223_ = 1;
v_v_3224_ = lean_array_uget(v_bs_3213_, v_i_3212_);
v___x_3225_ = lean_unsigned_to_nat(0u);
v_bs_x27_3226_ = lean_array_uset(v_bs_3213_, v_i_3212_, v___x_3225_);
v___x_3227_ = lean_usize_to_nat(v_i_3212_);
lean_inc(v_tail_3206_);
v___x_3228_ = l_Lean_mkConst(v_v_3224_, v_tail_3206_);
v___x_3229_ = l_Lean_mkAppN(v___x_3228_, v_params_3207_);
lean_inc(v___y_3217_);
lean_inc_ref(v___y_3216_);
lean_inc(v___y_3215_);
lean_inc_ref(v___y_3214_);
v___x_3230_ = lean_infer_type(v___x_3229_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___f_3235_; lean_object* v___x_3236_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc_n(v_a_3231_, 2);
lean_dec_ref_known(v___x_3230_, 1);
v___x_3232_ = lean_box(v___x_3219_);
v___x_3233_ = lean_box(v___x_3222_);
v___x_3234_ = lean_box(v___x_3223_);
lean_inc_ref(v_alts_3210_);
lean_inc_ref(v_snd_3209_);
lean_inc_ref(v_a_3208_);
v___f_3235_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3235_, 0, v___x_3221_);
lean_closure_set(v___f_3235_, 1, v_a_3208_);
lean_closure_set(v___f_3235_, 2, v___x_3227_);
lean_closure_set(v___f_3235_, 3, v_snd_3209_);
lean_closure_set(v___f_3235_, 4, v___x_3232_);
lean_closure_set(v___f_3235_, 5, v___x_3233_);
lean_closure_set(v___f_3235_, 6, v___x_3234_);
lean_closure_set(v___f_3235_, 7, v_alts_3210_);
lean_closure_set(v___f_3235_, 8, v_a_3231_);
v___x_3236_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3231_, v___f_3235_, v___x_3222_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; size_t v___x_3238_; size_t v___x_3239_; lean_object* v___x_3240_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
lean_inc(v_a_3237_);
lean_dec_ref_known(v___x_3236_, 1);
v___x_3238_ = ((size_t)1ULL);
v___x_3239_ = lean_usize_add(v_i_3212_, v___x_3238_);
v___x_3240_ = lean_array_uset(v_bs_x27_3226_, v_i_3212_, v_a_3237_);
v_i_3212_ = v___x_3239_;
v_bs_3213_ = v___x_3240_;
goto _start;
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec_ref(v_bs_x27_3226_);
lean_dec_ref(v_alts_3210_);
lean_dec_ref(v_snd_3209_);
lean_dec_ref(v_a_3208_);
lean_dec(v_tail_3206_);
v_a_3242_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3236_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3236_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec(v___x_3227_);
lean_dec_ref(v_bs_x27_3226_);
lean_dec_ref(v_alts_3210_);
lean_dec_ref(v_snd_3209_);
lean_dec_ref(v_a_3208_);
lean_dec(v_tail_3206_);
v_a_3250_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3230_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3230_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3258_, lean_object* v_params_3259_, lean_object* v_a_3260_, lean_object* v_snd_3261_, lean_object* v_alts_3262_, lean_object* v_sz_3263_, lean_object* v_i_3264_, lean_object* v_bs_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
size_t v_sz_boxed_3271_; size_t v_i_boxed_3272_; lean_object* v_res_3273_; 
v_sz_boxed_3271_ = lean_unbox_usize(v_sz_3263_);
lean_dec(v_sz_3263_);
v_i_boxed_3272_ = lean_unbox_usize(v_i_3264_);
lean_dec(v_i_3264_);
v_res_3273_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3258_, v_params_3259_, v_a_3260_, v_snd_3261_, v_alts_3262_, v_sz_boxed_3271_, v_i_boxed_3272_, v_bs_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec_ref(v_params_3259_);
return v_res_3273_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_unsigned_to_nat(16u);
v___x_3276_ = lean_mk_array(v___x_3275_, v___x_3274_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3277_, lean_object* v___x_3278_, uint8_t v___x_3279_, uint8_t v___x_3280_, uint8_t v___x_3281_, lean_object* v_ism1_x27_3282_, lean_object* v_is_3283_, lean_object* v___x_3284_, lean_object* v___x_3285_, lean_object* v___x_3286_, lean_object* v___x_3287_, lean_object* v_params_3288_, lean_object* v___x_3289_, lean_object* v___x_3290_, lean_object* v_heq_3291_, lean_object* v_val_3292_, lean_object* v_tail_3293_, lean_object* v_alts_3294_, size_t v_sz_3295_, size_t v___x_3296_, lean_object* v___x_3297_, lean_object* v___x_3298_, lean_object* v_declName_3299_, lean_object* v_levelParams_3300_, lean_object* v_numIndices_3301_, lean_object* v___x_3302_, lean_object* v___x_3303_, lean_object* v_numParams_3304_, lean_object* v_snd_3305_, lean_object* v_ism2_x27_3306_, lean_object* v_x_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___f_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3313_ = lean_box(v___x_3279_);
v___x_3314_ = lean_box(v___x_3280_);
v___x_3315_ = lean_box(v___x_3281_);
lean_inc_ref(v___x_3284_);
lean_inc_ref_n(v_is_3283_, 2);
lean_inc_ref(v_ism1_x27_3282_);
lean_inc_ref(v_motive_3277_);
v___f_3316_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3316_, 0, v_motive_3277_);
lean_closure_set(v___f_3316_, 1, v___x_3278_);
lean_closure_set(v___f_3316_, 2, v___x_3313_);
lean_closure_set(v___f_3316_, 3, v___x_3314_);
lean_closure_set(v___f_3316_, 4, v___x_3315_);
lean_closure_set(v___f_3316_, 5, v_ism1_x27_3282_);
lean_closure_set(v___f_3316_, 6, v_ism2_x27_3306_);
lean_closure_set(v___f_3316_, 7, v_is_3283_);
lean_closure_set(v___f_3316_, 8, v___x_3284_);
lean_inc_ref(v___x_3285_);
v___x_3317_ = lean_array_push(v_is_3283_, v___x_3285_);
v___x_3318_ = l_Lean_Meta_withNewEqs___redArg(v___x_3317_, v_ism1_x27_3282_, v___f_3316_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v_fst_3320_; lean_object* v_snd_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3422_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v_fst_3320_ = lean_ctor_get(v_a_3319_, 0);
v_snd_3321_ = lean_ctor_get(v_a_3319_, 1);
v_isSharedCheck_3422_ = !lean_is_exclusive(v_a_3319_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3323_ = v_a_3319_;
v_isShared_3324_ = v_isSharedCheck_3422_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_snd_3321_);
lean_inc(v_fst_3320_);
lean_dec(v_a_3319_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3422_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3325_ = l_Lean_mkConst(v___x_3286_, v___x_3287_);
v___x_3326_ = l_Lean_mkAppN(v___x_3325_, v_params_3288_);
v___x_3327_ = l_Lean_Expr_app___override(v___x_3326_, v_fst_3320_);
lean_inc_ref(v_is_3283_);
v___x_3328_ = l_Array_append___redArg(v_is_3283_, v___x_3289_);
v___x_3329_ = l_Array_append___redArg(v___x_3328_, v_is_3283_);
v___x_3330_ = l_Array_append___redArg(v___x_3329_, v___x_3290_);
v___x_3331_ = l_Lean_mkAppN(v___x_3327_, v___x_3330_);
lean_dec_ref(v___x_3330_);
lean_inc_ref(v_heq_3291_);
v___x_3332_ = l_Lean_Expr_app___override(v___x_3331_, v_heq_3291_);
v___x_3333_ = l_Lean_InductiveVal_numCtors(v_val_3292_);
lean_inc_ref(v___x_3332_);
v___x_3334_ = l_Lean_Meta_inferArgumentTypesN(v___x_3333_, v___x_3332_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3334_, 1);
lean_inc_ref(v_alts_3294_);
lean_inc(v_snd_3321_);
v___x_3336_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3293_, v_params_3288_, v_a_3335_, v_snd_3321_, v_alts_3294_, v_sz_3295_, v___x_3296_, v___x_3297_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
lean_inc(v_a_3337_);
lean_dec_ref_known(v___x_3336_, 1);
v___x_3338_ = l_Lean_mkAppN(v___x_3332_, v_a_3337_);
lean_dec(v_a_3337_);
v___x_3339_ = l_Lean_mkAppN(v___x_3338_, v_snd_3321_);
lean_dec(v_snd_3321_);
lean_inc_ref(v___x_3298_);
v___x_3340_ = lean_array_push(v___x_3298_, v_motive_3277_);
v___x_3341_ = l_Array_append___redArg(v_params_3288_, v___x_3340_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = l_Array_append___redArg(v___x_3341_, v_is_3283_);
lean_dec_ref(v_is_3283_);
v___x_3343_ = lean_unsigned_to_nat(2u);
v___x_3344_ = lean_mk_empty_array_with_capacity(v___x_3343_);
v___x_3345_ = lean_array_push(v___x_3344_, v___x_3285_);
v___x_3346_ = lean_array_push(v___x_3345_, v___x_3284_);
v___x_3347_ = l_Array_append___redArg(v___x_3342_, v___x_3346_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = lean_array_push(v___x_3298_, v_heq_3291_);
v___x_3349_ = l_Array_append___redArg(v___x_3347_, v___x_3348_);
lean_dec_ref(v___x_3348_);
v___x_3350_ = l_Array_append___redArg(v___x_3349_, v_alts_3294_);
lean_dec_ref(v_alts_3294_);
v___x_3351_ = l_Lean_Meta_mkLambdaFVars(v___x_3350_, v___x_3339_, v___x_3279_, v___x_3280_, v___x_3279_, v___x_3280_, v___x_3281_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
lean_dec_ref(v___x_3350_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3353_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc_n(v_a_3352_, 2);
lean_dec_ref_known(v___x_3351_, 1);
lean_inc(v___y_3311_);
lean_inc_ref(v___y_3310_);
lean_inc(v___y_3309_);
lean_inc_ref(v___y_3308_);
v___x_3353_ = lean_infer_type(v_a_3352_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3389_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3353_, 1);
v___x_3355_ = lean_box(1);
lean_inc(v_declName_3299_);
v___x_3356_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3299_, v_levelParams_3300_, v_a_3354_, v_a_3352_, v___x_3355_, v___y_3311_);
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3389_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3389_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set_tag(v___x_3359_, 1);
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
lean_object* v___x_3363_; lean_object* v___f_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3363_ = lean_box(v___x_3279_);
lean_inc_ref(v___x_3362_);
v___f_3364_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3364_, 0, v___x_3362_);
lean_closure_set(v___f_3364_, 1, v___x_3363_);
v___x_3365_ = lean_nat_add(v_numIndices_3301_, v___x_3302_);
lean_inc(v___x_3303_);
v___x_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3303_);
v___x_3367_ = lean_box(0);
v___x_3368_ = lean_mk_empty_array_with_capacity(v___x_3302_);
v___x_3369_ = lean_array_push(v___x_3368_, v___x_3367_);
v___x_3370_ = lean_array_push(v___x_3369_, v___x_3367_);
v___x_3371_ = lean_array_push(v___x_3370_, v___x_3367_);
v___x_3372_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3324_ == 0)
{
lean_ctor_set(v___x_3323_, 1, v___x_3372_);
lean_ctor_set(v___x_3323_, 0, v___x_3303_);
v___x_3374_ = v___x_3323_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3303_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; uint8_t v___y_3377_; uint8_t v___x_3386_; 
v___x_3375_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3375_, 0, v_numParams_3304_);
lean_ctor_set(v___x_3375_, 1, v___x_3365_);
lean_ctor_set(v___x_3375_, 2, v_snd_3305_);
lean_ctor_set(v___x_3375_, 3, v___x_3366_);
lean_ctor_set(v___x_3375_, 4, v___x_3371_);
lean_ctor_set(v___x_3375_, 5, v___x_3374_);
v___x_3386_ = l_Lean_isPrivateName(v_declName_3299_);
if (v___x_3386_ == 0)
{
v___y_3377_ = v___x_3280_;
goto v___jp_3376_;
}
else
{
v___y_3377_ = v___x_3279_;
goto v___jp_3376_;
}
v___jp_3376_:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3364_, v___y_3377_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v___x_3379_; lean_object* v___x_3380_; 
lean_dec_ref_known(v___x_3378_, 1);
v___x_3379_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3299_);
v___x_3380_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3379_, v_declName_3299_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v___x_3381_; uint8_t v___x_3382_; lean_object* v___x_3383_; 
lean_dec_ref_known(v___x_3380_, 1);
lean_inc_n(v_declName_3299_, 2);
v___x_3381_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3299_, v___x_3375_, v___y_3309_, v___y_3311_);
lean_dec_ref(v___x_3381_);
v___x_3382_ = 0;
v___x_3383_ = l_Lean_Meta_setInlineAttribute(v_declName_3299_, v___x_3382_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3384_; 
lean_dec_ref_known(v___x_3383_, 1);
v___x_3384_ = l_Lean_enableRealizationsForConst(v_declName_3299_, v___y_3310_, v___y_3311_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v___x_3385_; 
lean_dec_ref_known(v___x_3384_, 1);
v___x_3385_ = l_Lean_compileDecl(v___x_3362_, v___x_3280_, v___y_3310_, v___y_3311_);
return v___x_3385_;
}
else
{
lean_dec_ref(v___x_3362_);
return v___x_3384_;
}
}
else
{
lean_dec_ref(v___x_3362_);
lean_dec(v_declName_3299_);
return v___x_3383_;
}
}
else
{
lean_dec_ref_known(v___x_3375_, 6);
lean_dec_ref(v___x_3362_);
lean_dec(v_declName_3299_);
return v___x_3380_;
}
}
else
{
lean_dec_ref_known(v___x_3375_, 6);
lean_dec_ref(v___x_3362_);
lean_dec(v_declName_3299_);
return v___x_3378_;
}
}
}
}
}
}
else
{
lean_object* v_a_3390_; lean_object* v___x_3392_; uint8_t v_isShared_3393_; uint8_t v_isSharedCheck_3397_; 
lean_dec(v_a_3352_);
lean_del_object(v___x_3323_);
lean_dec_ref(v_snd_3305_);
lean_dec(v_numParams_3304_);
lean_dec(v___x_3303_);
lean_dec(v_levelParams_3300_);
lean_dec(v_declName_3299_);
v_a_3390_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3392_ = v___x_3353_;
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
else
{
lean_inc(v_a_3390_);
lean_dec(v___x_3353_);
v___x_3392_ = lean_box(0);
v_isShared_3393_ = v_isSharedCheck_3397_;
goto v_resetjp_3391_;
}
v_resetjp_3391_:
{
lean_object* v___x_3395_; 
if (v_isShared_3393_ == 0)
{
v___x_3395_ = v___x_3392_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v_a_3390_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_del_object(v___x_3323_);
lean_dec_ref(v_snd_3305_);
lean_dec(v_numParams_3304_);
lean_dec(v___x_3303_);
lean_dec(v_levelParams_3300_);
lean_dec(v_declName_3299_);
v_a_3398_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3351_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3351_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_object* v_a_3406_; lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
lean_dec_ref(v___x_3332_);
lean_del_object(v___x_3323_);
lean_dec(v_snd_3321_);
lean_dec_ref(v_snd_3305_);
lean_dec(v_numParams_3304_);
lean_dec(v___x_3303_);
lean_dec(v_levelParams_3300_);
lean_dec(v_declName_3299_);
lean_dec_ref(v___x_3298_);
lean_dec_ref(v_alts_3294_);
lean_dec_ref(v_heq_3291_);
lean_dec_ref(v_params_3288_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v___x_3284_);
lean_dec_ref(v_is_3283_);
lean_dec_ref(v_motive_3277_);
v_a_3406_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3413_ == 0)
{
v___x_3408_ = v___x_3336_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_inc(v_a_3406_);
lean_dec(v___x_3336_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
lean_dec_ref(v___x_3332_);
lean_del_object(v___x_3323_);
lean_dec(v_snd_3321_);
lean_dec_ref(v_snd_3305_);
lean_dec(v_numParams_3304_);
lean_dec(v___x_3303_);
lean_dec(v_levelParams_3300_);
lean_dec(v_declName_3299_);
lean_dec_ref(v___x_3298_);
lean_dec_ref(v___x_3297_);
lean_dec_ref(v_alts_3294_);
lean_dec(v_tail_3293_);
lean_dec_ref(v_heq_3291_);
lean_dec_ref(v_params_3288_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v___x_3284_);
lean_dec_ref(v_is_3283_);
lean_dec_ref(v_motive_3277_);
v_a_3414_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3334_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3334_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v_snd_3305_);
lean_dec(v_numParams_3304_);
lean_dec(v___x_3303_);
lean_dec(v_levelParams_3300_);
lean_dec(v_declName_3299_);
lean_dec_ref(v___x_3298_);
lean_dec_ref(v___x_3297_);
lean_dec_ref(v_alts_3294_);
lean_dec(v_tail_3293_);
lean_dec_ref(v_heq_3291_);
lean_dec_ref(v_params_3288_);
lean_dec(v___x_3287_);
lean_dec(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v___x_3284_);
lean_dec_ref(v_is_3283_);
lean_dec_ref(v_motive_3277_);
v_a_3423_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3318_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3318_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3431_ = _args[0];
lean_object* v___x_3432_ = _args[1];
lean_object* v___x_3433_ = _args[2];
lean_object* v___x_3434_ = _args[3];
lean_object* v___x_3435_ = _args[4];
lean_object* v_ism1_x27_3436_ = _args[5];
lean_object* v_is_3437_ = _args[6];
lean_object* v___x_3438_ = _args[7];
lean_object* v___x_3439_ = _args[8];
lean_object* v___x_3440_ = _args[9];
lean_object* v___x_3441_ = _args[10];
lean_object* v_params_3442_ = _args[11];
lean_object* v___x_3443_ = _args[12];
lean_object* v___x_3444_ = _args[13];
lean_object* v_heq_3445_ = _args[14];
lean_object* v_val_3446_ = _args[15];
lean_object* v_tail_3447_ = _args[16];
lean_object* v_alts_3448_ = _args[17];
lean_object* v_sz_3449_ = _args[18];
lean_object* v___x_3450_ = _args[19];
lean_object* v___x_3451_ = _args[20];
lean_object* v___x_3452_ = _args[21];
lean_object* v_declName_3453_ = _args[22];
lean_object* v_levelParams_3454_ = _args[23];
lean_object* v_numIndices_3455_ = _args[24];
lean_object* v___x_3456_ = _args[25];
lean_object* v___x_3457_ = _args[26];
lean_object* v_numParams_3458_ = _args[27];
lean_object* v_snd_3459_ = _args[28];
lean_object* v_ism2_x27_3460_ = _args[29];
lean_object* v_x_3461_ = _args[30];
lean_object* v___y_3462_ = _args[31];
lean_object* v___y_3463_ = _args[32];
lean_object* v___y_3464_ = _args[33];
lean_object* v___y_3465_ = _args[34];
lean_object* v___y_3466_ = _args[35];
_start:
{
uint8_t v___x_15517__boxed_3467_; uint8_t v___x_15518__boxed_3468_; uint8_t v___x_15519__boxed_3469_; size_t v_sz_boxed_3470_; size_t v___x_15528__boxed_3471_; lean_object* v_res_3472_; 
v___x_15517__boxed_3467_ = lean_unbox(v___x_3433_);
v___x_15518__boxed_3468_ = lean_unbox(v___x_3434_);
v___x_15519__boxed_3469_ = lean_unbox(v___x_3435_);
v_sz_boxed_3470_ = lean_unbox_usize(v_sz_3449_);
lean_dec(v_sz_3449_);
v___x_15528__boxed_3471_ = lean_unbox_usize(v___x_3450_);
lean_dec(v___x_3450_);
v_res_3472_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3431_, v___x_3432_, v___x_15517__boxed_3467_, v___x_15518__boxed_3468_, v___x_15519__boxed_3469_, v_ism1_x27_3436_, v_is_3437_, v___x_3438_, v___x_3439_, v___x_3440_, v___x_3441_, v_params_3442_, v___x_3443_, v___x_3444_, v_heq_3445_, v_val_3446_, v_tail_3447_, v_alts_3448_, v_sz_boxed_3470_, v___x_15528__boxed_3471_, v___x_3451_, v___x_3452_, v_declName_3453_, v_levelParams_3454_, v_numIndices_3455_, v___x_3456_, v___x_3457_, v_numParams_3458_, v_snd_3459_, v_ism2_x27_3460_, v_x_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_);
lean_dec(v___y_3465_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec_ref(v_x_3461_);
lean_dec(v___x_3456_);
lean_dec(v_numIndices_3455_);
lean_dec_ref(v_val_3446_);
lean_dec_ref(v___x_3444_);
lean_dec_ref(v___x_3443_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3473_, lean_object* v___x_3474_, uint8_t v___x_3475_, uint8_t v___x_3476_, uint8_t v___x_3477_, lean_object* v_is_3478_, lean_object* v___x_3479_, lean_object* v___x_3480_, lean_object* v___x_3481_, lean_object* v___x_3482_, lean_object* v_params_3483_, lean_object* v___x_3484_, lean_object* v___x_3485_, lean_object* v_heq_3486_, lean_object* v_val_3487_, lean_object* v_tail_3488_, lean_object* v_alts_3489_, size_t v_sz_3490_, size_t v___x_3491_, lean_object* v___x_3492_, lean_object* v___x_3493_, lean_object* v_declName_3494_, lean_object* v_levelParams_3495_, lean_object* v_numIndices_3496_, lean_object* v___x_3497_, lean_object* v___x_3498_, lean_object* v_numParams_3499_, lean_object* v_snd_3500_, lean_object* v___x_3501_, lean_object* v___x_3502_, lean_object* v_ism1_x27_3503_, lean_object* v_x_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_){
_start:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___f_3515_; lean_object* v___x_3516_; 
v___x_3510_ = lean_box(v___x_3475_);
v___x_3511_ = lean_box(v___x_3476_);
v___x_3512_ = lean_box(v___x_3477_);
v___x_3513_ = lean_box_usize(v_sz_3490_);
v___x_3514_ = lean_box_usize(v___x_3491_);
v___f_3515_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3515_, 0, v_motive_3473_);
lean_closure_set(v___f_3515_, 1, v___x_3474_);
lean_closure_set(v___f_3515_, 2, v___x_3510_);
lean_closure_set(v___f_3515_, 3, v___x_3511_);
lean_closure_set(v___f_3515_, 4, v___x_3512_);
lean_closure_set(v___f_3515_, 5, v_ism1_x27_3503_);
lean_closure_set(v___f_3515_, 6, v_is_3478_);
lean_closure_set(v___f_3515_, 7, v___x_3479_);
lean_closure_set(v___f_3515_, 8, v___x_3480_);
lean_closure_set(v___f_3515_, 9, v___x_3481_);
lean_closure_set(v___f_3515_, 10, v___x_3482_);
lean_closure_set(v___f_3515_, 11, v_params_3483_);
lean_closure_set(v___f_3515_, 12, v___x_3484_);
lean_closure_set(v___f_3515_, 13, v___x_3485_);
lean_closure_set(v___f_3515_, 14, v_heq_3486_);
lean_closure_set(v___f_3515_, 15, v_val_3487_);
lean_closure_set(v___f_3515_, 16, v_tail_3488_);
lean_closure_set(v___f_3515_, 17, v_alts_3489_);
lean_closure_set(v___f_3515_, 18, v___x_3513_);
lean_closure_set(v___f_3515_, 19, v___x_3514_);
lean_closure_set(v___f_3515_, 20, v___x_3492_);
lean_closure_set(v___f_3515_, 21, v___x_3493_);
lean_closure_set(v___f_3515_, 22, v_declName_3494_);
lean_closure_set(v___f_3515_, 23, v_levelParams_3495_);
lean_closure_set(v___f_3515_, 24, v_numIndices_3496_);
lean_closure_set(v___f_3515_, 25, v___x_3497_);
lean_closure_set(v___f_3515_, 26, v___x_3498_);
lean_closure_set(v___f_3515_, 27, v_numParams_3499_);
lean_closure_set(v___f_3515_, 28, v_snd_3500_);
v___x_3516_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3501_, v___x_3502_, v___f_3515_, v___x_3475_, v___x_3475_, v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3517_ = _args[0];
lean_object* v___x_3518_ = _args[1];
lean_object* v___x_3519_ = _args[2];
lean_object* v___x_3520_ = _args[3];
lean_object* v___x_3521_ = _args[4];
lean_object* v_is_3522_ = _args[5];
lean_object* v___x_3523_ = _args[6];
lean_object* v___x_3524_ = _args[7];
lean_object* v___x_3525_ = _args[8];
lean_object* v___x_3526_ = _args[9];
lean_object* v_params_3527_ = _args[10];
lean_object* v___x_3528_ = _args[11];
lean_object* v___x_3529_ = _args[12];
lean_object* v_heq_3530_ = _args[13];
lean_object* v_val_3531_ = _args[14];
lean_object* v_tail_3532_ = _args[15];
lean_object* v_alts_3533_ = _args[16];
lean_object* v_sz_3534_ = _args[17];
lean_object* v___x_3535_ = _args[18];
lean_object* v___x_3536_ = _args[19];
lean_object* v___x_3537_ = _args[20];
lean_object* v_declName_3538_ = _args[21];
lean_object* v_levelParams_3539_ = _args[22];
lean_object* v_numIndices_3540_ = _args[23];
lean_object* v___x_3541_ = _args[24];
lean_object* v___x_3542_ = _args[25];
lean_object* v_numParams_3543_ = _args[26];
lean_object* v_snd_3544_ = _args[27];
lean_object* v___x_3545_ = _args[28];
lean_object* v___x_3546_ = _args[29];
lean_object* v_ism1_x27_3547_ = _args[30];
lean_object* v_x_3548_ = _args[31];
lean_object* v___y_3549_ = _args[32];
lean_object* v___y_3550_ = _args[33];
lean_object* v___y_3551_ = _args[34];
lean_object* v___y_3552_ = _args[35];
lean_object* v___y_3553_ = _args[36];
_start:
{
uint8_t v___x_15839__boxed_3554_; uint8_t v___x_15840__boxed_3555_; uint8_t v___x_15841__boxed_3556_; size_t v_sz_boxed_3557_; size_t v___x_15850__boxed_3558_; lean_object* v_res_3559_; 
v___x_15839__boxed_3554_ = lean_unbox(v___x_3519_);
v___x_15840__boxed_3555_ = lean_unbox(v___x_3520_);
v___x_15841__boxed_3556_ = lean_unbox(v___x_3521_);
v_sz_boxed_3557_ = lean_unbox_usize(v_sz_3534_);
lean_dec(v_sz_3534_);
v___x_15850__boxed_3558_ = lean_unbox_usize(v___x_3535_);
lean_dec(v___x_3535_);
v_res_3559_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3517_, v___x_3518_, v___x_15839__boxed_3554_, v___x_15840__boxed_3555_, v___x_15841__boxed_3556_, v_is_3522_, v___x_3523_, v___x_3524_, v___x_3525_, v___x_3526_, v_params_3527_, v___x_3528_, v___x_3529_, v_heq_3530_, v_val_3531_, v_tail_3532_, v_alts_3533_, v_sz_boxed_3557_, v___x_15850__boxed_3558_, v___x_3536_, v___x_3537_, v_declName_3538_, v_levelParams_3539_, v_numIndices_3540_, v___x_3541_, v___x_3542_, v_numParams_3543_, v_snd_3544_, v___x_3545_, v___x_3546_, v_ism1_x27_3547_, v_x_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v_x_3548_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3560_, lean_object* v___x_3561_, lean_object* v_motive_3562_, lean_object* v___x_3563_, uint8_t v___x_3564_, uint8_t v___x_3565_, uint8_t v___x_3566_, lean_object* v_is_3567_, lean_object* v___x_3568_, lean_object* v___x_3569_, lean_object* v___x_3570_, lean_object* v___x_3571_, lean_object* v_params_3572_, lean_object* v___x_3573_, lean_object* v___x_3574_, lean_object* v_heq_3575_, lean_object* v_val_3576_, lean_object* v_tail_3577_, size_t v_sz_3578_, size_t v___x_3579_, lean_object* v___x_3580_, lean_object* v___x_3581_, lean_object* v_declName_3582_, lean_object* v_levelParams_3583_, lean_object* v___x_3584_, lean_object* v___x_3585_, lean_object* v_numParams_3586_, lean_object* v_snd_3587_, lean_object* v___x_3588_, lean_object* v_alts_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___f_3602_; lean_object* v___x_3603_; 
v___x_3595_ = lean_nat_add(v_numIndices_3560_, v___x_3561_);
v___x_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
v___x_3597_ = lean_box(v___x_3564_);
v___x_3598_ = lean_box(v___x_3565_);
v___x_3599_ = lean_box(v___x_3566_);
v___x_3600_ = lean_box_usize(v_sz_3578_);
v___x_3601_ = lean_box_usize(v___x_3579_);
lean_inc_ref(v___x_3596_);
lean_inc_ref(v___x_3588_);
v___f_3602_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3602_, 0, v_motive_3562_);
lean_closure_set(v___f_3602_, 1, v___x_3563_);
lean_closure_set(v___f_3602_, 2, v___x_3597_);
lean_closure_set(v___f_3602_, 3, v___x_3598_);
lean_closure_set(v___f_3602_, 4, v___x_3599_);
lean_closure_set(v___f_3602_, 5, v_is_3567_);
lean_closure_set(v___f_3602_, 6, v___x_3568_);
lean_closure_set(v___f_3602_, 7, v___x_3569_);
lean_closure_set(v___f_3602_, 8, v___x_3570_);
lean_closure_set(v___f_3602_, 9, v___x_3571_);
lean_closure_set(v___f_3602_, 10, v_params_3572_);
lean_closure_set(v___f_3602_, 11, v___x_3573_);
lean_closure_set(v___f_3602_, 12, v___x_3574_);
lean_closure_set(v___f_3602_, 13, v_heq_3575_);
lean_closure_set(v___f_3602_, 14, v_val_3576_);
lean_closure_set(v___f_3602_, 15, v_tail_3577_);
lean_closure_set(v___f_3602_, 16, v_alts_3589_);
lean_closure_set(v___f_3602_, 17, v___x_3600_);
lean_closure_set(v___f_3602_, 18, v___x_3601_);
lean_closure_set(v___f_3602_, 19, v___x_3580_);
lean_closure_set(v___f_3602_, 20, v___x_3581_);
lean_closure_set(v___f_3602_, 21, v_declName_3582_);
lean_closure_set(v___f_3602_, 22, v_levelParams_3583_);
lean_closure_set(v___f_3602_, 23, v_numIndices_3560_);
lean_closure_set(v___f_3602_, 24, v___x_3584_);
lean_closure_set(v___f_3602_, 25, v___x_3585_);
lean_closure_set(v___f_3602_, 26, v_numParams_3586_);
lean_closure_set(v___f_3602_, 27, v_snd_3587_);
lean_closure_set(v___f_3602_, 28, v___x_3588_);
lean_closure_set(v___f_3602_, 29, v___x_3596_);
v___x_3603_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3588_, v___x_3596_, v___f_3602_, v___x_3564_, v___x_3564_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3604_ = _args[0];
lean_object* v___x_3605_ = _args[1];
lean_object* v_motive_3606_ = _args[2];
lean_object* v___x_3607_ = _args[3];
lean_object* v___x_3608_ = _args[4];
lean_object* v___x_3609_ = _args[5];
lean_object* v___x_3610_ = _args[6];
lean_object* v_is_3611_ = _args[7];
lean_object* v___x_3612_ = _args[8];
lean_object* v___x_3613_ = _args[9];
lean_object* v___x_3614_ = _args[10];
lean_object* v___x_3615_ = _args[11];
lean_object* v_params_3616_ = _args[12];
lean_object* v___x_3617_ = _args[13];
lean_object* v___x_3618_ = _args[14];
lean_object* v_heq_3619_ = _args[15];
lean_object* v_val_3620_ = _args[16];
lean_object* v_tail_3621_ = _args[17];
lean_object* v_sz_3622_ = _args[18];
lean_object* v___x_3623_ = _args[19];
lean_object* v___x_3624_ = _args[20];
lean_object* v___x_3625_ = _args[21];
lean_object* v_declName_3626_ = _args[22];
lean_object* v_levelParams_3627_ = _args[23];
lean_object* v___x_3628_ = _args[24];
lean_object* v___x_3629_ = _args[25];
lean_object* v_numParams_3630_ = _args[26];
lean_object* v_snd_3631_ = _args[27];
lean_object* v___x_3632_ = _args[28];
lean_object* v_alts_3633_ = _args[29];
lean_object* v___y_3634_ = _args[30];
lean_object* v___y_3635_ = _args[31];
lean_object* v___y_3636_ = _args[32];
lean_object* v___y_3637_ = _args[33];
lean_object* v___y_3638_ = _args[34];
_start:
{
uint8_t v___x_15932__boxed_3639_; uint8_t v___x_15933__boxed_3640_; uint8_t v___x_15934__boxed_3641_; size_t v_sz_boxed_3642_; size_t v___x_15943__boxed_3643_; lean_object* v_res_3644_; 
v___x_15932__boxed_3639_ = lean_unbox(v___x_3608_);
v___x_15933__boxed_3640_ = lean_unbox(v___x_3609_);
v___x_15934__boxed_3641_ = lean_unbox(v___x_3610_);
v_sz_boxed_3642_ = lean_unbox_usize(v_sz_3622_);
lean_dec(v_sz_3622_);
v___x_15943__boxed_3643_ = lean_unbox_usize(v___x_3623_);
lean_dec(v___x_3623_);
v_res_3644_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3604_, v___x_3605_, v_motive_3606_, v___x_3607_, v___x_15932__boxed_3639_, v___x_15933__boxed_3640_, v___x_15934__boxed_3641_, v_is_3611_, v___x_3612_, v___x_3613_, v___x_3614_, v___x_3615_, v_params_3616_, v___x_3617_, v___x_3618_, v_heq_3619_, v_val_3620_, v_tail_3621_, v_sz_boxed_3642_, v___x_15943__boxed_3643_, v___x_3624_, v___x_3625_, v_declName_3626_, v_levelParams_3627_, v___x_3628_, v___x_3629_, v_numParams_3630_, v_snd_3631_, v___x_3632_, v_alts_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___x_3605_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3645_, lean_object* v_declInfos_3646_, lean_object* v_k_3647_, lean_object* v_kind_3648_, lean_object* v_x_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
uint8_t v_kind_boxed_3655_; lean_object* v_res_3656_; 
v_kind_boxed_3655_ = lean_unbox(v_kind_3648_);
v_res_3656_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3645_, v_declInfos_3646_, v_k_3647_, v_kind_boxed_3655_, v_x_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3657_, lean_object* v_k_3658_, uint8_t v_kind_3659_, lean_object* v_acc_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v___x_3666_; lean_object* v_toApplicative_3667_; lean_object* v_toFunctor_3668_; lean_object* v_toSeq_3669_; lean_object* v_toSeqLeft_3670_; lean_object* v_toSeqRight_3671_; lean_object* v___f_3672_; lean_object* v___f_3673_; lean_object* v___f_3674_; lean_object* v___f_3675_; lean_object* v___x_3676_; lean_object* v___f_3677_; lean_object* v___f_3678_; lean_object* v___f_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v_toApplicative_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3741_; 
v___x_3666_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3667_ = lean_ctor_get(v___x_3666_, 0);
v_toFunctor_3668_ = lean_ctor_get(v_toApplicative_3667_, 0);
v_toSeq_3669_ = lean_ctor_get(v_toApplicative_3667_, 2);
v_toSeqLeft_3670_ = lean_ctor_get(v_toApplicative_3667_, 3);
v_toSeqRight_3671_ = lean_ctor_get(v_toApplicative_3667_, 4);
v___f_3672_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3673_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3668_, 2);
v___f_3674_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3674_, 0, v_toFunctor_3668_);
v___f_3675_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3675_, 0, v_toFunctor_3668_);
v___x_3676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___f_3674_);
lean_ctor_set(v___x_3676_, 1, v___f_3675_);
lean_inc(v_toSeqRight_3671_);
v___f_3677_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3677_, 0, v_toSeqRight_3671_);
lean_inc(v_toSeqLeft_3670_);
v___f_3678_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3678_, 0, v_toSeqLeft_3670_);
lean_inc(v_toSeq_3669_);
v___f_3679_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3679_, 0, v_toSeq_3669_);
v___x_3680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3676_);
lean_ctor_set(v___x_3680_, 1, v___f_3672_);
lean_ctor_set(v___x_3680_, 2, v___f_3679_);
lean_ctor_set(v___x_3680_, 3, v___f_3678_);
lean_ctor_set(v___x_3680_, 4, v___f_3677_);
v___x_3681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
lean_ctor_set(v___x_3681_, 1, v___f_3673_);
v___x_3682_ = l_StateRefT_x27_instMonad___redArg(v___x_3681_);
v_toApplicative_3683_ = lean_ctor_get(v___x_3682_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3682_);
if (v_isSharedCheck_3741_ == 0)
{
lean_object* v_unused_3742_; 
v_unused_3742_ = lean_ctor_get(v___x_3682_, 1);
lean_dec(v_unused_3742_);
v___x_3685_ = v___x_3682_;
v_isShared_3686_ = v_isSharedCheck_3741_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_toApplicative_3683_);
lean_dec(v___x_3682_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3741_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v_toFunctor_3687_; lean_object* v_toSeq_3688_; lean_object* v_toSeqLeft_3689_; lean_object* v_toSeqRight_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3739_; 
v_toFunctor_3687_ = lean_ctor_get(v_toApplicative_3683_, 0);
v_toSeq_3688_ = lean_ctor_get(v_toApplicative_3683_, 2);
v_toSeqLeft_3689_ = lean_ctor_get(v_toApplicative_3683_, 3);
v_toSeqRight_3690_ = lean_ctor_get(v_toApplicative_3683_, 4);
v_isSharedCheck_3739_ = !lean_is_exclusive(v_toApplicative_3683_);
if (v_isSharedCheck_3739_ == 0)
{
lean_object* v_unused_3740_; 
v_unused_3740_ = lean_ctor_get(v_toApplicative_3683_, 1);
lean_dec(v_unused_3740_);
v___x_3692_ = v_toApplicative_3683_;
v_isShared_3693_ = v_isSharedCheck_3739_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_toSeqRight_3690_);
lean_inc(v_toSeqLeft_3689_);
lean_inc(v_toSeq_3688_);
lean_inc(v_toFunctor_3687_);
lean_dec(v_toApplicative_3683_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3739_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___f_3694_; lean_object* v___f_3695_; lean_object* v___f_3696_; lean_object* v___f_3697_; lean_object* v___x_3698_; lean_object* v___f_3699_; lean_object* v___f_3700_; lean_object* v___f_3701_; lean_object* v___x_3703_; 
v___f_3694_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3695_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3687_);
v___f_3696_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3696_, 0, v_toFunctor_3687_);
v___f_3697_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3697_, 0, v_toFunctor_3687_);
v___x_3698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3698_, 0, v___f_3696_);
lean_ctor_set(v___x_3698_, 1, v___f_3697_);
v___f_3699_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3699_, 0, v_toSeqRight_3690_);
v___f_3700_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3700_, 0, v_toSeqLeft_3689_);
v___f_3701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3701_, 0, v_toSeq_3688_);
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 4, v___f_3699_);
lean_ctor_set(v___x_3692_, 3, v___f_3700_);
lean_ctor_set(v___x_3692_, 2, v___f_3701_);
lean_ctor_set(v___x_3692_, 1, v___f_3694_);
lean_ctor_set(v___x_3692_, 0, v___x_3698_);
v___x_3703_ = v___x_3692_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3698_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v___f_3694_);
lean_ctor_set(v_reuseFailAlloc_3738_, 2, v___f_3701_);
lean_ctor_set(v_reuseFailAlloc_3738_, 3, v___f_3700_);
lean_ctor_set(v_reuseFailAlloc_3738_, 4, v___f_3699_);
v___x_3703_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
lean_object* v___x_3705_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 1, v___f_3695_);
lean_ctor_set(v___x_3685_, 0, v___x_3703_);
v___x_3705_ = v___x_3685_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v___x_3703_);
lean_ctor_set(v_reuseFailAlloc_3737_, 1, v___f_3695_);
v___x_3705_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v___x_3706_ = lean_array_get_size(v_acc_3660_);
v___x_3707_ = lean_array_get_size(v_declInfos_3657_);
v___x_3708_ = lean_nat_dec_lt(v___x_3706_, v___x_3707_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; 
lean_dec_ref(v___x_3705_);
lean_dec_ref(v_declInfos_3657_);
lean_inc(v___y_3664_);
lean_inc_ref(v___y_3663_);
lean_inc(v___y_3662_);
lean_inc_ref(v___y_3661_);
v___x_3709_ = lean_apply_6(v_k_3658_, v_acc_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, lean_box(0));
return v___x_3709_;
}
else
{
lean_object* v___x_3710_; uint8_t v___x_3711_; lean_object* v___x_3712_; lean_object* v___f_3713_; lean_object* v___f_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v_snd_3719_; lean_object* v_fst_3720_; lean_object* v_fst_3721_; lean_object* v_snd_3722_; lean_object* v___x_3723_; lean_object* v___f_3724_; lean_object* v___x_3725_; 
v___x_3710_ = lean_box(0);
v___x_3711_ = 0;
v___x_3712_ = l_Lean_instInhabitedExpr;
v___f_3713_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3713_, 0, v___x_3705_);
lean_closure_set(v___f_3713_, 1, v___x_3712_);
v___f_3714_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3714_, 0, v___f_3713_);
v___x_3715_ = lean_box(v___x_3711_);
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
lean_ctor_set(v___x_3716_, 1, v___f_3714_);
v___x_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3710_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = lean_array_get(v___x_3717_, v_declInfos_3657_, v___x_3706_);
lean_dec_ref_known(v___x_3717_, 2);
v_snd_3719_ = lean_ctor_get(v___x_3718_, 1);
lean_inc(v_snd_3719_);
v_fst_3720_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_fst_3720_);
lean_dec(v___x_3718_);
v_fst_3721_ = lean_ctor_get(v_snd_3719_, 0);
lean_inc(v_fst_3721_);
v_snd_3722_ = lean_ctor_get(v_snd_3719_, 1);
lean_inc(v_snd_3722_);
lean_dec(v_snd_3719_);
v___x_3723_ = lean_box(v_kind_3659_);
lean_inc_ref(v_acc_3660_);
v___f_3724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3724_, 0, v_acc_3660_);
lean_closure_set(v___f_3724_, 1, v_declInfos_3657_);
lean_closure_set(v___f_3724_, 2, v_k_3658_);
lean_closure_set(v___f_3724_, 3, v___x_3723_);
lean_inc(v___y_3664_);
lean_inc_ref(v___y_3663_);
lean_inc(v___y_3662_);
lean_inc_ref(v___y_3661_);
v___x_3725_ = lean_apply_6(v_snd_3722_, v_acc_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, lean_box(0));
if (lean_obj_tag(v___x_3725_) == 0)
{
lean_object* v_a_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; 
v_a_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_a_3726_);
lean_dec_ref_known(v___x_3725_, 1);
v___x_3727_ = lean_unbox(v_fst_3721_);
lean_dec(v_fst_3721_);
v___x_3728_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3720_, v___x_3727_, v_a_3726_, v___f_3724_, v_kind_3659_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
return v___x_3728_;
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec_ref(v___f_3724_);
lean_dec(v_fst_3721_);
lean_dec(v_fst_3720_);
v_a_3729_ = lean_ctor_get(v___x_3725_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3725_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3725_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3743_, lean_object* v_declInfos_3744_, lean_object* v_k_3745_, uint8_t v_kind_3746_, lean_object* v_x_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = lean_array_push(v_acc_3743_, v_x_3747_);
v___x_3754_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3744_, v_k_3745_, v_kind_3746_, v___x_3753_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3755_, lean_object* v_k_3756_, lean_object* v_kind_3757_, lean_object* v_acc_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
uint8_t v_kind_boxed_3764_; lean_object* v_res_3765_; 
v_kind_boxed_3764_ = lean_unbox(v_kind_3757_);
v_res_3765_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3755_, v_k_3756_, v_kind_boxed_3764_, v_acc_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3766_, lean_object* v_k_3767_, uint8_t v_kind_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3774_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3775_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3766_, v_k_3767_, v_kind_3768_, v___x_3774_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3776_, lean_object* v_k_3777_, lean_object* v_kind_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
uint8_t v_kind_boxed_3784_; lean_object* v_res_3785_; 
v_kind_boxed_3784_ = lean_unbox(v_kind_3778_);
v_res_3785_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3776_, v_k_3777_, v_kind_boxed_3784_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
return v_res_3785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3786_, lean_object* v_k_3787_, uint8_t v_kind_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
size_t v_sz_3794_; size_t v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v_sz_3794_ = lean_array_size(v_declInfos_3786_);
v___x_3795_ = ((size_t)0ULL);
v___x_3796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3794_, v___x_3795_, v_declInfos_3786_);
v___x_3797_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3796_, v_k_3787_, v_kind_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3798_, lean_object* v_k_3799_, lean_object* v_kind_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
uint8_t v_kind_boxed_3806_; lean_object* v_res_3807_; 
v_kind_boxed_3806_ = lean_unbox(v_kind_3800_);
v_res_3807_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3798_, v_k_3799_, v_kind_boxed_3806_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3808_, lean_object* v_k_3809_, uint8_t v_kind_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
size_t v_sz_3816_; size_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
v_sz_3816_ = lean_array_size(v_declInfos_3808_);
v___x_3817_ = ((size_t)0ULL);
v___x_3818_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3816_, v___x_3817_, v_declInfos_3808_);
v___x_3819_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3818_, v_k_3809_, v_kind_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3820_, lean_object* v_k_3821_, lean_object* v_kind_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
uint8_t v_kind_boxed_3828_; lean_object* v_res_3829_; 
v_kind_boxed_3828_ = lean_unbox(v_kind_3822_);
v_res_3829_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3820_, v_k_3821_, v_kind_boxed_3828_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec(v___y_3826_);
lean_dec_ref(v___y_3825_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
return v_res_3829_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3832_ = lean_box(0);
v___x_3833_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3834_ = l_Lean_mkConst(v___x_3833_, v___x_3832_);
return v___x_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3835_, lean_object* v_v_3836_, lean_object* v___x_3837_, lean_object* v___x_3838_, lean_object* v___x_3839_, lean_object* v_motive_3840_, uint8_t v___x_3841_, uint8_t v___x_3842_, uint8_t v___x_3843_, lean_object* v_zs12_3844_, lean_object* v_is_3845_, lean_object* v_fields1_3846_, lean_object* v_fields2_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v_e_3863_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
lean_inc_ref(v___x_3839_);
v___x_3873_ = l_Lean_mkAppN(v___x_3839_, v_fields1_3846_);
v___x_3874_ = l_Lean_mkAppN(v___x_3839_, v_fields2_3847_);
lean_inc(v___x_3837_);
v___x_3875_ = l_Lean_mkNatLit(v___x_3837_);
v___x_3876_ = l_Lean_Meta_mkEqRefl(v___x_3875_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v_a_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; 
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v___x_3878_ = lean_unsigned_to_nat(3u);
v___x_3879_ = lean_mk_empty_array_with_capacity(v___x_3878_);
v___x_3880_ = lean_array_push(v___x_3879_, v___x_3873_);
v___x_3881_ = lean_array_push(v___x_3880_, v___x_3874_);
v___x_3882_ = lean_array_push(v___x_3881_, v_a_3877_);
v___x_3883_ = l_Array_append___redArg(v_is_3845_, v___x_3882_);
lean_dec_ref(v___x_3882_);
v___x_3884_ = l_Lean_mkAppN(v_motive_3840_, v___x_3883_);
lean_dec_ref(v___x_3883_);
v___x_3885_ = l_Lean_Meta_mkForallFVars(v_zs12_3844_, v___x_3884_, v___x_3841_, v___x_3842_, v___x_3842_, v___x_3843_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
v___x_3887_ = lean_array_get_size(v_zs12_3844_);
v___x_3888_ = lean_nat_dec_eq(v___x_3887_, v___x_3835_);
if (v___x_3888_ == 0)
{
v_e_3863_ = v_a_3886_;
goto v___jp_3862_;
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3890_ = l_Lean_mkArrow(v___x_3889_, v_a_3886_, v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v_e_3863_ = v_a_3891_;
goto v___jp_3862_;
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec(v___x_3837_);
lean_dec(v_v_3836_);
lean_dec(v___x_3835_);
v_a_3892_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3890_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3890_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec(v___x_3837_);
lean_dec(v_v_3836_);
lean_dec(v___x_3835_);
v_a_3900_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3885_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3885_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec_ref(v___x_3874_);
lean_dec_ref(v___x_3873_);
lean_dec_ref(v_is_3845_);
lean_dec_ref(v_motive_3840_);
lean_dec(v___x_3837_);
lean_dec(v_v_3836_);
lean_dec(v___x_3835_);
v_a_3908_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3876_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3876_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
v___jp_3853_:
{
lean_object* v___x_3856_; uint8_t v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3856_ = lean_array_get_size(v_zs12_3844_);
v___x_3857_ = lean_nat_dec_eq(v___x_3856_, v___x_3835_);
v___x_3858_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3858_, 0, v___x_3856_);
lean_ctor_set(v___x_3858_, 1, v___x_3835_);
lean_ctor_set_uint8(v___x_3858_, sizeof(void*)*2, v___x_3857_);
v___x_3859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3859_, 0, v___y_3855_);
lean_ctor_set(v___x_3859_, 1, v___y_3854_);
v___x_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3859_);
lean_ctor_set(v___x_3860_, 1, v___x_3858_);
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
return v___x_3861_;
}
v___jp_3862_:
{
if (lean_obj_tag(v_v_3836_) == 1)
{
lean_object* v_str_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
lean_dec(v___x_3837_);
v_str_3864_ = lean_ctor_get(v_v_3836_, 1);
lean_inc_ref(v_str_3864_);
lean_dec_ref_known(v_v_3836_, 2);
v___x_3865_ = lean_box(0);
v___x_3866_ = l_Lean_Name_str___override(v___x_3865_, v_str_3864_);
v___y_3854_ = v_e_3863_;
v___y_3855_ = v___x_3866_;
goto v___jp_3853_;
}
else
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
lean_dec(v_v_3836_);
v___x_3867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3868_ = lean_nat_add(v___x_3837_, v___x_3838_);
lean_dec(v___x_3837_);
v___x_3869_ = l_Nat_reprFast(v___x_3868_);
v___x_3870_ = lean_string_append(v___x_3867_, v___x_3869_);
lean_dec_ref(v___x_3869_);
v___x_3871_ = lean_box(0);
v___x_3872_ = l_Lean_Name_str___override(v___x_3871_, v___x_3870_);
v___y_3854_ = v_e_3863_;
v___y_3855_ = v___x_3872_;
goto v___jp_3853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3916_ = _args[0];
lean_object* v_v_3917_ = _args[1];
lean_object* v___x_3918_ = _args[2];
lean_object* v___x_3919_ = _args[3];
lean_object* v___x_3920_ = _args[4];
lean_object* v_motive_3921_ = _args[5];
lean_object* v___x_3922_ = _args[6];
lean_object* v___x_3923_ = _args[7];
lean_object* v___x_3924_ = _args[8];
lean_object* v_zs12_3925_ = _args[9];
lean_object* v_is_3926_ = _args[10];
lean_object* v_fields1_3927_ = _args[11];
lean_object* v_fields2_3928_ = _args[12];
lean_object* v___y_3929_ = _args[13];
lean_object* v___y_3930_ = _args[14];
lean_object* v___y_3931_ = _args[15];
lean_object* v___y_3932_ = _args[16];
lean_object* v___y_3933_ = _args[17];
_start:
{
uint8_t v___x_16279__boxed_3934_; uint8_t v___x_16280__boxed_3935_; uint8_t v___x_16281__boxed_3936_; lean_object* v_res_3937_; 
v___x_16279__boxed_3934_ = lean_unbox(v___x_3922_);
v___x_16280__boxed_3935_ = lean_unbox(v___x_3923_);
v___x_16281__boxed_3936_ = lean_unbox(v___x_3924_);
v_res_3937_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3916_, v_v_3917_, v___x_3918_, v___x_3919_, v___x_3920_, v_motive_3921_, v___x_16279__boxed_3934_, v___x_16280__boxed_3935_, v___x_16281__boxed_3936_, v_zs12_3925_, v_is_3926_, v_fields1_3927_, v_fields2_3928_, v___y_3929_, v___y_3930_, v___y_3931_, v___y_3932_);
lean_dec(v___y_3932_);
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3930_);
lean_dec_ref(v___y_3929_);
lean_dec_ref(v_fields2_3928_);
lean_dec_ref(v_fields1_3927_);
lean_dec_ref(v_zs12_3925_);
lean_dec(v___x_3919_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3938_, lean_object* v_params_3939_, lean_object* v_motive_3940_, size_t v_sz_3941_, size_t v_i_3942_, lean_object* v_bs_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_){
_start:
{
uint8_t v___x_3949_; 
v___x_3949_ = lean_usize_dec_lt(v_i_3942_, v_sz_3941_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; 
lean_dec_ref(v_motive_3940_);
lean_dec(v_tail_3938_);
v___x_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3950_, 0, v_bs_3943_);
return v___x_3950_;
}
else
{
lean_object* v___x_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; uint8_t v___x_3954_; lean_object* v_v_3955_; lean_object* v_bs_x27_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___f_3963_; lean_object* v___x_3964_; 
v___x_3951_ = lean_unsigned_to_nat(0u);
v___x_3952_ = lean_unsigned_to_nat(1u);
v___x_3953_ = 0;
v___x_3954_ = 1;
v_v_3955_ = lean_array_uget(v_bs_3943_, v_i_3942_);
v_bs_x27_3956_ = lean_array_uset(v_bs_3943_, v_i_3942_, v___x_3951_);
v___x_3957_ = lean_usize_to_nat(v_i_3942_);
lean_inc(v_tail_3938_);
lean_inc(v_v_3955_);
v___x_3958_ = l_Lean_mkConst(v_v_3955_, v_tail_3938_);
v___x_3959_ = l_Lean_mkAppN(v___x_3958_, v_params_3939_);
v___x_3960_ = lean_box(v___x_3953_);
v___x_3961_ = lean_box(v___x_3949_);
v___x_3962_ = lean_box(v___x_3954_);
lean_inc_ref(v_motive_3940_);
lean_inc_ref(v___x_3959_);
v___f_3963_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3963_, 0, v___x_3951_);
lean_closure_set(v___f_3963_, 1, v_v_3955_);
lean_closure_set(v___f_3963_, 2, v___x_3957_);
lean_closure_set(v___f_3963_, 3, v___x_3952_);
lean_closure_set(v___f_3963_, 4, v___x_3959_);
lean_closure_set(v___f_3963_, 5, v_motive_3940_);
lean_closure_set(v___f_3963_, 6, v___x_3960_);
lean_closure_set(v___f_3963_, 7, v___x_3961_);
lean_closure_set(v___f_3963_, 8, v___x_3962_);
v___x_3964_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3959_, v___f_3963_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; size_t v___x_3966_; size_t v___x_3967_; lean_object* v___x_3968_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
v___x_3966_ = ((size_t)1ULL);
v___x_3967_ = lean_usize_add(v_i_3942_, v___x_3966_);
v___x_3968_ = lean_array_uset(v_bs_x27_3956_, v_i_3942_, v_a_3965_);
v_i_3942_ = v___x_3967_;
v_bs_3943_ = v___x_3968_;
goto _start;
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec_ref(v_bs_x27_3956_);
lean_dec_ref(v_motive_3940_);
lean_dec(v_tail_3938_);
v_a_3970_ = lean_ctor_get(v___x_3964_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3964_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3964_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3978_, lean_object* v_params_3979_, lean_object* v_motive_3980_, lean_object* v_sz_3981_, lean_object* v_i_3982_, lean_object* v_bs_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
size_t v_sz_boxed_3989_; size_t v_i_boxed_3990_; lean_object* v_res_3991_; 
v_sz_boxed_3989_ = lean_unbox_usize(v_sz_3981_);
lean_dec(v_sz_3981_);
v_i_boxed_3990_ = lean_unbox_usize(v_i_3982_);
lean_dec(v_i_3982_);
v_res_3991_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3978_, v_params_3979_, v_motive_3980_, v_sz_boxed_3989_, v_i_boxed_3990_, v_bs_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec_ref(v___y_3984_);
lean_dec_ref(v_params_3979_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3994_, lean_object* v_tail_3995_, lean_object* v_params_3996_, lean_object* v_numIndices_3997_, lean_object* v___x_3998_, lean_object* v___x_3999_, uint8_t v___x_4000_, uint8_t v___x_4001_, uint8_t v___x_4002_, lean_object* v_is_4003_, lean_object* v___x_4004_, lean_object* v___x_4005_, lean_object* v___x_4006_, lean_object* v___x_4007_, lean_object* v___x_4008_, lean_object* v___x_4009_, lean_object* v_heq_4010_, lean_object* v_val_4011_, lean_object* v___x_4012_, lean_object* v_declName_4013_, lean_object* v_levelParams_4014_, lean_object* v___x_4015_, lean_object* v___x_4016_, lean_object* v_numParams_4017_, lean_object* v___x_4018_, lean_object* v_motive_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v___x_4025_; size_t v_sz_4026_; size_t v___x_4027_; lean_object* v___x_4028_; 
v___x_4025_ = lean_array_mk(v_ctors_3994_);
v_sz_4026_ = lean_array_size(v___x_4025_);
v___x_4027_ = ((size_t)0ULL);
lean_inc_ref(v___x_4025_);
lean_inc_ref(v_motive_4019_);
lean_inc(v_tail_3995_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3995_, v_params_3996_, v_motive_4019_, v_sz_4026_, v___x_4027_, v___x_4025_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v___x_4030_; lean_object* v_fst_4031_; lean_object* v_snd_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___f_4038_; uint8_t v___x_4039_; lean_object* v___x_4040_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref_known(v___x_4028_, 1);
v___x_4030_ = l_Array_unzip___redArg(v_a_4029_);
lean_dec(v_a_4029_);
v_fst_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_fst_4031_);
v_snd_4032_ = lean_ctor_get(v___x_4030_, 1);
lean_inc(v_snd_4032_);
lean_dec_ref(v___x_4030_);
v___x_4033_ = lean_box(v___x_4000_);
v___x_4034_ = lean_box(v___x_4001_);
v___x_4035_ = lean_box(v___x_4002_);
v___x_4036_ = lean_box_usize(v_sz_4026_);
v___x_4037_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4038_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4038_, 0, v_numIndices_3997_);
lean_closure_set(v___f_4038_, 1, v___x_3998_);
lean_closure_set(v___f_4038_, 2, v_motive_4019_);
lean_closure_set(v___f_4038_, 3, v___x_3999_);
lean_closure_set(v___f_4038_, 4, v___x_4033_);
lean_closure_set(v___f_4038_, 5, v___x_4034_);
lean_closure_set(v___f_4038_, 6, v___x_4035_);
lean_closure_set(v___f_4038_, 7, v_is_4003_);
lean_closure_set(v___f_4038_, 8, v___x_4004_);
lean_closure_set(v___f_4038_, 9, v___x_4005_);
lean_closure_set(v___f_4038_, 10, v___x_4006_);
lean_closure_set(v___f_4038_, 11, v___x_4007_);
lean_closure_set(v___f_4038_, 12, v_params_3996_);
lean_closure_set(v___f_4038_, 13, v___x_4008_);
lean_closure_set(v___f_4038_, 14, v___x_4009_);
lean_closure_set(v___f_4038_, 15, v_heq_4010_);
lean_closure_set(v___f_4038_, 16, v_val_4011_);
lean_closure_set(v___f_4038_, 17, v_tail_3995_);
lean_closure_set(v___f_4038_, 18, v___x_4036_);
lean_closure_set(v___f_4038_, 19, v___x_4037_);
lean_closure_set(v___f_4038_, 20, v___x_4025_);
lean_closure_set(v___f_4038_, 21, v___x_4012_);
lean_closure_set(v___f_4038_, 22, v_declName_4013_);
lean_closure_set(v___f_4038_, 23, v_levelParams_4014_);
lean_closure_set(v___f_4038_, 24, v___x_4015_);
lean_closure_set(v___f_4038_, 25, v___x_4016_);
lean_closure_set(v___f_4038_, 26, v_numParams_4017_);
lean_closure_set(v___f_4038_, 27, v_snd_4032_);
lean_closure_set(v___f_4038_, 28, v___x_4018_);
v___x_4039_ = 0;
v___x_4040_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_4031_, v___f_4038_, v___x_4039_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
return v___x_4040_;
}
else
{
lean_object* v_a_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4048_; 
lean_dec_ref(v___x_4025_);
lean_dec_ref(v_motive_4019_);
lean_dec_ref(v___x_4018_);
lean_dec(v_numParams_4017_);
lean_dec(v___x_4016_);
lean_dec(v___x_4015_);
lean_dec(v_levelParams_4014_);
lean_dec(v_declName_4013_);
lean_dec_ref(v___x_4012_);
lean_dec_ref(v_val_4011_);
lean_dec_ref(v_heq_4010_);
lean_dec_ref(v___x_4009_);
lean_dec_ref(v___x_4008_);
lean_dec(v___x_4007_);
lean_dec(v___x_4006_);
lean_dec_ref(v___x_4005_);
lean_dec_ref(v___x_4004_);
lean_dec_ref(v_is_4003_);
lean_dec_ref(v___x_3999_);
lean_dec(v___x_3998_);
lean_dec(v_numIndices_3997_);
lean_dec_ref(v_params_3996_);
lean_dec(v_tail_3995_);
v_a_4041_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4048_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4048_ == 0)
{
v___x_4043_ = v___x_4028_;
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_a_4041_);
lean_dec(v___x_4028_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4048_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4046_; 
if (v_isShared_4044_ == 0)
{
v___x_4046_ = v___x_4043_;
goto v_reusejp_4045_;
}
else
{
lean_object* v_reuseFailAlloc_4047_; 
v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
v___x_4046_ = v_reuseFailAlloc_4047_;
goto v_reusejp_4045_;
}
v_reusejp_4045_:
{
return v___x_4046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4049_ = _args[0];
lean_object* v_tail_4050_ = _args[1];
lean_object* v_params_4051_ = _args[2];
lean_object* v_numIndices_4052_ = _args[3];
lean_object* v___x_4053_ = _args[4];
lean_object* v___x_4054_ = _args[5];
lean_object* v___x_4055_ = _args[6];
lean_object* v___x_4056_ = _args[7];
lean_object* v___x_4057_ = _args[8];
lean_object* v_is_4058_ = _args[9];
lean_object* v___x_4059_ = _args[10];
lean_object* v___x_4060_ = _args[11];
lean_object* v___x_4061_ = _args[12];
lean_object* v___x_4062_ = _args[13];
lean_object* v___x_4063_ = _args[14];
lean_object* v___x_4064_ = _args[15];
lean_object* v_heq_4065_ = _args[16];
lean_object* v_val_4066_ = _args[17];
lean_object* v___x_4067_ = _args[18];
lean_object* v_declName_4068_ = _args[19];
lean_object* v_levelParams_4069_ = _args[20];
lean_object* v___x_4070_ = _args[21];
lean_object* v___x_4071_ = _args[22];
lean_object* v_numParams_4072_ = _args[23];
lean_object* v___x_4073_ = _args[24];
lean_object* v_motive_4074_ = _args[25];
lean_object* v___y_4075_ = _args[26];
lean_object* v___y_4076_ = _args[27];
lean_object* v___y_4077_ = _args[28];
lean_object* v___y_4078_ = _args[29];
lean_object* v___y_4079_ = _args[30];
_start:
{
uint8_t v___x_16516__boxed_4080_; uint8_t v___x_16517__boxed_4081_; uint8_t v___x_16518__boxed_4082_; lean_object* v_res_4083_; 
v___x_16516__boxed_4080_ = lean_unbox(v___x_4055_);
v___x_16517__boxed_4081_ = lean_unbox(v___x_4056_);
v___x_16518__boxed_4082_ = lean_unbox(v___x_4057_);
v_res_4083_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4049_, v_tail_4050_, v_params_4051_, v_numIndices_4052_, v___x_4053_, v___x_4054_, v___x_16516__boxed_4080_, v___x_16517__boxed_4081_, v___x_16518__boxed_4082_, v_is_4058_, v___x_4059_, v___x_4060_, v___x_4061_, v___x_4062_, v___x_4063_, v___x_4064_, v_heq_4065_, v_val_4066_, v___x_4067_, v_declName_4068_, v_levelParams_4069_, v___x_4070_, v___x_4071_, v_numParams_4072_, v___x_4073_, v_motive_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4084_, lean_object* v___x_4085_, lean_object* v_is_4086_, lean_object* v_head_4087_, lean_object* v_ctors_4088_, lean_object* v_tail_4089_, lean_object* v_params_4090_, lean_object* v_numIndices_4091_, lean_object* v___x_4092_, lean_object* v___x_4093_, lean_object* v___x_4094_, lean_object* v___x_4095_, lean_object* v___x_4096_, lean_object* v_val_4097_, lean_object* v___x_4098_, lean_object* v_declName_4099_, lean_object* v_levelParams_4100_, lean_object* v___x_4101_, lean_object* v_numParams_4102_, lean_object* v___x_4103_, lean_object* v_heq_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; uint8_t v___x_4117_; uint8_t v___x_4118_; uint8_t v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___f_4123_; lean_object* v___x_4124_; 
v___x_4110_ = lean_unsigned_to_nat(3u);
v___x_4111_ = lean_mk_empty_array_with_capacity(v___x_4110_);
lean_inc_ref(v___x_4084_);
v___x_4112_ = lean_array_push(v___x_4111_, v___x_4084_);
lean_inc_ref(v___x_4085_);
v___x_4113_ = lean_array_push(v___x_4112_, v___x_4085_);
lean_inc_ref(v_heq_4104_);
v___x_4114_ = lean_array_push(v___x_4113_, v_heq_4104_);
lean_inc_ref(v_is_4086_);
v___x_4115_ = l_Array_append___redArg(v_is_4086_, v___x_4114_);
lean_dec_ref(v___x_4114_);
v___x_4116_ = l_Lean_mkSort(v_head_4087_);
v___x_4117_ = 0;
v___x_4118_ = 1;
v___x_4119_ = 1;
v___x_4120_ = lean_box(v___x_4117_);
v___x_4121_ = lean_box(v___x_4118_);
v___x_4122_ = lean_box(v___x_4119_);
lean_inc_ref(v___x_4115_);
v___f_4123_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4123_, 0, v_ctors_4088_);
lean_closure_set(v___f_4123_, 1, v_tail_4089_);
lean_closure_set(v___f_4123_, 2, v_params_4090_);
lean_closure_set(v___f_4123_, 3, v_numIndices_4091_);
lean_closure_set(v___f_4123_, 4, v___x_4092_);
lean_closure_set(v___f_4123_, 5, v___x_4115_);
lean_closure_set(v___f_4123_, 6, v___x_4120_);
lean_closure_set(v___f_4123_, 7, v___x_4121_);
lean_closure_set(v___f_4123_, 8, v___x_4122_);
lean_closure_set(v___f_4123_, 9, v_is_4086_);
lean_closure_set(v___f_4123_, 10, v___x_4085_);
lean_closure_set(v___f_4123_, 11, v___x_4084_);
lean_closure_set(v___f_4123_, 12, v___x_4093_);
lean_closure_set(v___f_4123_, 13, v___x_4094_);
lean_closure_set(v___f_4123_, 14, v___x_4095_);
lean_closure_set(v___f_4123_, 15, v___x_4096_);
lean_closure_set(v___f_4123_, 16, v_heq_4104_);
lean_closure_set(v___f_4123_, 17, v_val_4097_);
lean_closure_set(v___f_4123_, 18, v___x_4098_);
lean_closure_set(v___f_4123_, 19, v_declName_4099_);
lean_closure_set(v___f_4123_, 20, v_levelParams_4100_);
lean_closure_set(v___f_4123_, 21, v___x_4110_);
lean_closure_set(v___f_4123_, 22, v___x_4101_);
lean_closure_set(v___f_4123_, 23, v_numParams_4102_);
lean_closure_set(v___f_4123_, 24, v___x_4103_);
v___x_4124_ = l_Lean_Meta_mkForallFVars(v___x_4115_, v___x_4116_, v___x_4117_, v___x_4118_, v___x_4118_, v___x_4119_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec_ref(v___x_4115_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v_a_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; lean_object* v___x_4128_; 
v_a_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_a_4125_);
lean_dec_ref_known(v___x_4124_, 1);
v___x_4126_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4127_ = 0;
v___x_4128_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4126_, v___x_4119_, v_a_4125_, v___f_4123_, v___x_4127_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
return v___x_4128_;
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec_ref(v___f_4123_);
v_a_4129_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4124_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4124_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4137_ = _args[0];
lean_object* v___x_4138_ = _args[1];
lean_object* v_is_4139_ = _args[2];
lean_object* v_head_4140_ = _args[3];
lean_object* v_ctors_4141_ = _args[4];
lean_object* v_tail_4142_ = _args[5];
lean_object* v_params_4143_ = _args[6];
lean_object* v_numIndices_4144_ = _args[7];
lean_object* v___x_4145_ = _args[8];
lean_object* v___x_4146_ = _args[9];
lean_object* v___x_4147_ = _args[10];
lean_object* v___x_4148_ = _args[11];
lean_object* v___x_4149_ = _args[12];
lean_object* v_val_4150_ = _args[13];
lean_object* v___x_4151_ = _args[14];
lean_object* v_declName_4152_ = _args[15];
lean_object* v_levelParams_4153_ = _args[16];
lean_object* v___x_4154_ = _args[17];
lean_object* v_numParams_4155_ = _args[18];
lean_object* v___x_4156_ = _args[19];
lean_object* v_heq_4157_ = _args[20];
lean_object* v___y_4158_ = _args[21];
lean_object* v___y_4159_ = _args[22];
lean_object* v___y_4160_ = _args[23];
lean_object* v___y_4161_ = _args[24];
lean_object* v___y_4162_ = _args[25];
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4137_, v___x_4138_, v_is_4139_, v_head_4140_, v_ctors_4141_, v_tail_4142_, v_params_4143_, v_numIndices_4144_, v___x_4145_, v___x_4146_, v___x_4147_, v___x_4148_, v___x_4149_, v_val_4150_, v___x_4151_, v_declName_4152_, v_levelParams_4153_, v___x_4154_, v_numParams_4155_, v___x_4156_, v_heq_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4164_, lean_object* v_x1_4165_, lean_object* v_indName_4166_, lean_object* v_tail_4167_, lean_object* v_params_4168_, lean_object* v_is_4169_, lean_object* v___x_4170_, lean_object* v_head_4171_, lean_object* v_ctors_4172_, lean_object* v_numIndices_4173_, lean_object* v___x_4174_, lean_object* v___x_4175_, lean_object* v_val_4176_, lean_object* v_declName_4177_, lean_object* v_levelParams_4178_, lean_object* v_numParams_4179_, lean_object* v___x_4180_, lean_object* v_x2_4181_, lean_object* v_x_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___f_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4188_ = lean_unsigned_to_nat(0u);
v___x_4189_ = lean_array_get_borrowed(v___x_4164_, v_x1_4165_, v___x_4188_);
v___x_4190_ = lean_array_get_borrowed(v___x_4164_, v_x2_4181_, v___x_4188_);
v___x_4191_ = l_Lean_mkCtorIdxName(v_indName_4166_);
lean_inc(v_tail_4167_);
v___x_4192_ = l_Lean_mkConst(v___x_4191_, v_tail_4167_);
lean_inc_ref(v_params_4168_);
v___x_4193_ = l_Array_append___redArg(v_params_4168_, v_is_4169_);
v___x_4194_ = lean_mk_empty_array_with_capacity(v___x_4170_);
lean_inc_n(v___x_4189_, 2);
lean_inc_ref_n(v___x_4194_, 2);
v___x_4195_ = lean_array_push(v___x_4194_, v___x_4189_);
lean_inc_ref(v___x_4193_);
v___x_4196_ = l_Array_append___redArg(v___x_4193_, v___x_4195_);
lean_inc_ref(v___x_4192_);
v___x_4197_ = l_Lean_mkAppN(v___x_4192_, v___x_4196_);
lean_dec_ref(v___x_4196_);
lean_inc_n(v___x_4190_, 2);
v___x_4198_ = lean_array_push(v___x_4194_, v___x_4190_);
lean_inc_ref(v___x_4198_);
v___f_4199_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4199_, 0, v___x_4189_);
lean_closure_set(v___f_4199_, 1, v___x_4190_);
lean_closure_set(v___f_4199_, 2, v_is_4169_);
lean_closure_set(v___f_4199_, 3, v_head_4171_);
lean_closure_set(v___f_4199_, 4, v_ctors_4172_);
lean_closure_set(v___f_4199_, 5, v_tail_4167_);
lean_closure_set(v___f_4199_, 6, v_params_4168_);
lean_closure_set(v___f_4199_, 7, v_numIndices_4173_);
lean_closure_set(v___f_4199_, 8, v___x_4170_);
lean_closure_set(v___f_4199_, 9, v___x_4174_);
lean_closure_set(v___f_4199_, 10, v___x_4175_);
lean_closure_set(v___f_4199_, 11, v___x_4195_);
lean_closure_set(v___f_4199_, 12, v___x_4198_);
lean_closure_set(v___f_4199_, 13, v_val_4176_);
lean_closure_set(v___f_4199_, 14, v___x_4194_);
lean_closure_set(v___f_4199_, 15, v_declName_4177_);
lean_closure_set(v___f_4199_, 16, v_levelParams_4178_);
lean_closure_set(v___f_4199_, 17, v___x_4188_);
lean_closure_set(v___f_4199_, 18, v_numParams_4179_);
lean_closure_set(v___f_4199_, 19, v___x_4180_);
v___x_4200_ = l_Array_append___redArg(v___x_4193_, v___x_4198_);
lean_dec_ref(v___x_4198_);
v___x_4201_ = l_Lean_mkAppN(v___x_4192_, v___x_4200_);
lean_dec_ref(v___x_4200_);
v___x_4202_ = l_Lean_Meta_mkEq(v___x_4197_, v___x_4201_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v___x_4204_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4205_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4204_, v_a_4203_, v___f_4199_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4205_;
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec_ref(v___f_4199_);
v_a_4206_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4202_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4202_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4214_ = _args[0];
lean_object* v_x1_4215_ = _args[1];
lean_object* v_indName_4216_ = _args[2];
lean_object* v_tail_4217_ = _args[3];
lean_object* v_params_4218_ = _args[4];
lean_object* v_is_4219_ = _args[5];
lean_object* v___x_4220_ = _args[6];
lean_object* v_head_4221_ = _args[7];
lean_object* v_ctors_4222_ = _args[8];
lean_object* v_numIndices_4223_ = _args[9];
lean_object* v___x_4224_ = _args[10];
lean_object* v___x_4225_ = _args[11];
lean_object* v_val_4226_ = _args[12];
lean_object* v_declName_4227_ = _args[13];
lean_object* v_levelParams_4228_ = _args[14];
lean_object* v_numParams_4229_ = _args[15];
lean_object* v___x_4230_ = _args[16];
lean_object* v_x2_4231_ = _args[17];
lean_object* v_x_4232_ = _args[18];
lean_object* v___y_4233_ = _args[19];
lean_object* v___y_4234_ = _args[20];
lean_object* v___y_4235_ = _args[21];
lean_object* v___y_4236_ = _args[22];
lean_object* v___y_4237_ = _args[23];
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4214_, v_x1_4215_, v_indName_4216_, v_tail_4217_, v_params_4218_, v_is_4219_, v___x_4220_, v_head_4221_, v_ctors_4222_, v_numIndices_4223_, v___x_4224_, v___x_4225_, v_val_4226_, v_declName_4227_, v_levelParams_4228_, v_numParams_4229_, v___x_4230_, v_x2_4231_, v_x_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
lean_dec_ref(v_x_4232_);
lean_dec_ref(v_x2_4231_);
lean_dec_ref(v_x1_4215_);
lean_dec_ref(v___x_4214_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4239_, lean_object* v_indName_4240_, lean_object* v_tail_4241_, lean_object* v_params_4242_, lean_object* v_is_4243_, lean_object* v___x_4244_, lean_object* v_head_4245_, lean_object* v_ctors_4246_, lean_object* v_numIndices_4247_, lean_object* v___x_4248_, lean_object* v___x_4249_, lean_object* v_val_4250_, lean_object* v_declName_4251_, lean_object* v_levelParams_4252_, lean_object* v_numParams_4253_, lean_object* v___x_4254_, lean_object* v_t_4255_, lean_object* v___x_4256_, lean_object* v_x1_4257_, lean_object* v_x_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v___f_4264_; uint8_t v___x_4265_; lean_object* v___x_4266_; 
v___f_4264_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4264_, 0, v___x_4239_);
lean_closure_set(v___f_4264_, 1, v_x1_4257_);
lean_closure_set(v___f_4264_, 2, v_indName_4240_);
lean_closure_set(v___f_4264_, 3, v_tail_4241_);
lean_closure_set(v___f_4264_, 4, v_params_4242_);
lean_closure_set(v___f_4264_, 5, v_is_4243_);
lean_closure_set(v___f_4264_, 6, v___x_4244_);
lean_closure_set(v___f_4264_, 7, v_head_4245_);
lean_closure_set(v___f_4264_, 8, v_ctors_4246_);
lean_closure_set(v___f_4264_, 9, v_numIndices_4247_);
lean_closure_set(v___f_4264_, 10, v___x_4248_);
lean_closure_set(v___f_4264_, 11, v___x_4249_);
lean_closure_set(v___f_4264_, 12, v_val_4250_);
lean_closure_set(v___f_4264_, 13, v_declName_4251_);
lean_closure_set(v___f_4264_, 14, v_levelParams_4252_);
lean_closure_set(v___f_4264_, 15, v_numParams_4253_);
lean_closure_set(v___f_4264_, 16, v___x_4254_);
v___x_4265_ = 0;
v___x_4266_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4255_, v___x_4256_, v___f_4264_, v___x_4265_, v___x_4265_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
return v___x_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4267_ = _args[0];
lean_object* v_indName_4268_ = _args[1];
lean_object* v_tail_4269_ = _args[2];
lean_object* v_params_4270_ = _args[3];
lean_object* v_is_4271_ = _args[4];
lean_object* v___x_4272_ = _args[5];
lean_object* v_head_4273_ = _args[6];
lean_object* v_ctors_4274_ = _args[7];
lean_object* v_numIndices_4275_ = _args[8];
lean_object* v___x_4276_ = _args[9];
lean_object* v___x_4277_ = _args[10];
lean_object* v_val_4278_ = _args[11];
lean_object* v_declName_4279_ = _args[12];
lean_object* v_levelParams_4280_ = _args[13];
lean_object* v_numParams_4281_ = _args[14];
lean_object* v___x_4282_ = _args[15];
lean_object* v_t_4283_ = _args[16];
lean_object* v___x_4284_ = _args[17];
lean_object* v_x1_4285_ = _args[18];
lean_object* v_x_4286_ = _args[19];
lean_object* v___y_4287_ = _args[20];
lean_object* v___y_4288_ = _args[21];
lean_object* v___y_4289_ = _args[22];
lean_object* v___y_4290_ = _args[23];
lean_object* v___y_4291_ = _args[24];
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4267_, v_indName_4268_, v_tail_4269_, v_params_4270_, v_is_4271_, v___x_4272_, v_head_4273_, v_ctors_4274_, v_numIndices_4275_, v___x_4276_, v___x_4277_, v_val_4278_, v_declName_4279_, v_levelParams_4280_, v_numParams_4281_, v___x_4282_, v_t_4283_, v___x_4284_, v_x1_4285_, v_x_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec_ref(v_x_4286_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4293_, lean_object* v_indName_4294_, lean_object* v_tail_4295_, lean_object* v_params_4296_, lean_object* v_head_4297_, lean_object* v_ctors_4298_, lean_object* v_numIndices_4299_, lean_object* v___x_4300_, lean_object* v___x_4301_, lean_object* v_val_4302_, lean_object* v_declName_4303_, lean_object* v_levelParams_4304_, lean_object* v_numParams_4305_, lean_object* v___x_4306_, lean_object* v_is_4307_, lean_object* v_t_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; uint8_t v___x_4317_; lean_object* v___x_4318_; 
v___x_4314_ = lean_unsigned_to_nat(1u);
v___x_4315_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4308_);
v___f_4316_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4316_, 0, v___x_4293_);
lean_closure_set(v___f_4316_, 1, v_indName_4294_);
lean_closure_set(v___f_4316_, 2, v_tail_4295_);
lean_closure_set(v___f_4316_, 3, v_params_4296_);
lean_closure_set(v___f_4316_, 4, v_is_4307_);
lean_closure_set(v___f_4316_, 5, v___x_4314_);
lean_closure_set(v___f_4316_, 6, v_head_4297_);
lean_closure_set(v___f_4316_, 7, v_ctors_4298_);
lean_closure_set(v___f_4316_, 8, v_numIndices_4299_);
lean_closure_set(v___f_4316_, 9, v___x_4300_);
lean_closure_set(v___f_4316_, 10, v___x_4301_);
lean_closure_set(v___f_4316_, 11, v_val_4302_);
lean_closure_set(v___f_4316_, 12, v_declName_4303_);
lean_closure_set(v___f_4316_, 13, v_levelParams_4304_);
lean_closure_set(v___f_4316_, 14, v_numParams_4305_);
lean_closure_set(v___f_4316_, 15, v___x_4306_);
lean_closure_set(v___f_4316_, 16, v_t_4308_);
lean_closure_set(v___f_4316_, 17, v___x_4315_);
v___x_4317_ = 0;
v___x_4318_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4308_, v___x_4315_, v___f_4316_, v___x_4317_, v___x_4317_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4319_ = _args[0];
lean_object* v_indName_4320_ = _args[1];
lean_object* v_tail_4321_ = _args[2];
lean_object* v_params_4322_ = _args[3];
lean_object* v_head_4323_ = _args[4];
lean_object* v_ctors_4324_ = _args[5];
lean_object* v_numIndices_4325_ = _args[6];
lean_object* v___x_4326_ = _args[7];
lean_object* v___x_4327_ = _args[8];
lean_object* v_val_4328_ = _args[9];
lean_object* v_declName_4329_ = _args[10];
lean_object* v_levelParams_4330_ = _args[11];
lean_object* v_numParams_4331_ = _args[12];
lean_object* v___x_4332_ = _args[13];
lean_object* v_is_4333_ = _args[14];
lean_object* v_t_4334_ = _args[15];
lean_object* v___y_4335_ = _args[16];
lean_object* v___y_4336_ = _args[17];
lean_object* v___y_4337_ = _args[18];
lean_object* v___y_4338_ = _args[19];
lean_object* v___y_4339_ = _args[20];
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4319_, v_indName_4320_, v_tail_4321_, v_params_4322_, v_head_4323_, v_ctors_4324_, v_numIndices_4325_, v___x_4326_, v___x_4327_, v_val_4328_, v_declName_4329_, v_levelParams_4330_, v_numParams_4331_, v___x_4332_, v_is_4333_, v_t_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
return v_res_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4341_, lean_object* v_indName_4342_, lean_object* v_tail_4343_, lean_object* v_head_4344_, lean_object* v_ctors_4345_, lean_object* v_numIndices_4346_, lean_object* v___x_4347_, lean_object* v___x_4348_, lean_object* v_val_4349_, lean_object* v_declName_4350_, lean_object* v_levelParams_4351_, lean_object* v_numParams_4352_, lean_object* v_params_4353_, lean_object* v_t_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; lean_object* v___f_4361_; lean_object* v___x_4362_; uint8_t v___x_4363_; lean_object* v___x_4364_; 
v___x_4360_ = l_Lean_Expr_bindingBody_x21(v_t_4354_);
lean_inc_ref(v___x_4360_);
lean_inc(v_numIndices_4346_);
v___f_4361_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4361_, 0, v___x_4341_);
lean_closure_set(v___f_4361_, 1, v_indName_4342_);
lean_closure_set(v___f_4361_, 2, v_tail_4343_);
lean_closure_set(v___f_4361_, 3, v_params_4353_);
lean_closure_set(v___f_4361_, 4, v_head_4344_);
lean_closure_set(v___f_4361_, 5, v_ctors_4345_);
lean_closure_set(v___f_4361_, 6, v_numIndices_4346_);
lean_closure_set(v___f_4361_, 7, v___x_4347_);
lean_closure_set(v___f_4361_, 8, v___x_4348_);
lean_closure_set(v___f_4361_, 9, v_val_4349_);
lean_closure_set(v___f_4361_, 10, v_declName_4350_);
lean_closure_set(v___f_4361_, 11, v_levelParams_4351_);
lean_closure_set(v___f_4361_, 12, v_numParams_4352_);
lean_closure_set(v___f_4361_, 13, v___x_4360_);
v___x_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4362_, 0, v_numIndices_4346_);
v___x_4363_ = 0;
v___x_4364_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4360_, v___x_4362_, v___f_4361_, v___x_4363_, v___x_4363_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
return v___x_4364_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4365_ = _args[0];
lean_object* v_indName_4366_ = _args[1];
lean_object* v_tail_4367_ = _args[2];
lean_object* v_head_4368_ = _args[3];
lean_object* v_ctors_4369_ = _args[4];
lean_object* v_numIndices_4370_ = _args[5];
lean_object* v___x_4371_ = _args[6];
lean_object* v___x_4372_ = _args[7];
lean_object* v_val_4373_ = _args[8];
lean_object* v_declName_4374_ = _args[9];
lean_object* v_levelParams_4375_ = _args[10];
lean_object* v_numParams_4376_ = _args[11];
lean_object* v_params_4377_ = _args[12];
lean_object* v_t_4378_ = _args[13];
lean_object* v___y_4379_ = _args[14];
lean_object* v___y_4380_ = _args[15];
lean_object* v___y_4381_ = _args[16];
lean_object* v___y_4382_ = _args[17];
lean_object* v___y_4383_ = _args[18];
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4365_, v_indName_4366_, v_tail_4367_, v_head_4368_, v_ctors_4369_, v_numIndices_4370_, v___x_4371_, v___x_4372_, v_val_4373_, v_declName_4374_, v_levelParams_4375_, v_numParams_4376_, v_params_4377_, v_t_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec_ref(v_t_4378_);
return v_res_4384_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4389_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4390_ = lean_unsigned_to_nat(58u);
v___x_4391_ = lean_unsigned_to_nat(142u);
v___x_4392_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4393_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4394_ = l_mkPanicMessageWithDecl(v___x_4393_, v___x_4392_, v___x_4391_, v___x_4390_, v___x_4389_);
return v___x_4394_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4395_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4396_ = lean_unsigned_to_nat(60u);
v___x_4397_ = lean_unsigned_to_nat(136u);
v___x_4398_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4399_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4400_ = l_mkPanicMessageWithDecl(v___x_4399_, v___x_4398_, v___x_4397_, v___x_4396_, v___x_4395_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4401_, lean_object* v_indName_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_){
_start:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_4402_);
v___x_4409_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
if (lean_obj_tag(v_a_4410_) == 5)
{
lean_object* v_val_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v_val_4411_ = lean_ctor_get(v_a_4410_, 0);
lean_inc_ref(v_val_4411_);
lean_dec_ref_known(v_a_4410_, 1);
v___x_4412_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4401_);
v___x_4413_ = l_Lean_Name_append(v_declName_4401_, v___x_4412_);
lean_inc(v_indName_4402_);
lean_inc(v___x_4413_);
v___x_4414_ = l_Lean_mkCasesOnSameCtorHet(v___x_4413_, v_indName_4402_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4446_; 
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4446_ == 0)
{
lean_object* v_unused_4447_; 
v_unused_4447_ = lean_ctor_get(v___x_4414_, 0);
lean_dec(v_unused_4447_);
v___x_4416_ = v___x_4414_;
v_isShared_4417_ = v_isSharedCheck_4446_;
goto v_resetjp_4415_;
}
else
{
lean_dec(v___x_4414_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4446_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4418_; lean_object* v___x_4419_; 
lean_inc(v_indName_4402_);
v___x_4418_ = l_Lean_mkCasesOnName(v_indName_4402_);
v___x_4419_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4418_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; lean_object* v_levelParams_4421_; lean_object* v_type_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4419_, 1);
v_levelParams_4421_ = lean_ctor_get(v_a_4420_, 1);
lean_inc_n(v_levelParams_4421_, 2);
v_type_4422_ = lean_ctor_get(v_a_4420_, 2);
lean_inc_ref(v_type_4422_);
lean_dec(v_a_4420_);
v___x_4423_ = lean_box(0);
v___x_4424_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4421_, v___x_4423_);
if (lean_obj_tag(v___x_4424_) == 1)
{
lean_object* v_head_4425_; lean_object* v_tail_4426_; lean_object* v_numParams_4427_; lean_object* v_numIndices_4428_; lean_object* v_ctors_4429_; lean_object* v___f_4430_; lean_object* v___x_4432_; 
v_head_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_head_4425_);
v_tail_4426_ = lean_ctor_get(v___x_4424_, 1);
lean_inc(v_tail_4426_);
v_numParams_4427_ = lean_ctor_get(v_val_4411_, 1);
lean_inc_n(v_numParams_4427_, 2);
v_numIndices_4428_ = lean_ctor_get(v_val_4411_, 2);
lean_inc(v_numIndices_4428_);
v_ctors_4429_ = lean_ctor_get(v_val_4411_, 4);
lean_inc(v_ctors_4429_);
v___f_4430_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4430_, 0, v___x_4408_);
lean_closure_set(v___f_4430_, 1, v_indName_4402_);
lean_closure_set(v___f_4430_, 2, v_tail_4426_);
lean_closure_set(v___f_4430_, 3, v_head_4425_);
lean_closure_set(v___f_4430_, 4, v_ctors_4429_);
lean_closure_set(v___f_4430_, 5, v_numIndices_4428_);
lean_closure_set(v___f_4430_, 6, v___x_4413_);
lean_closure_set(v___f_4430_, 7, v___x_4424_);
lean_closure_set(v___f_4430_, 8, v_val_4411_);
lean_closure_set(v___f_4430_, 9, v_declName_4401_);
lean_closure_set(v___f_4430_, 10, v_levelParams_4421_);
lean_closure_set(v___f_4430_, 11, v_numParams_4427_);
if (v_isShared_4417_ == 0)
{
lean_ctor_set_tag(v___x_4416_, 1);
lean_ctor_set(v___x_4416_, 0, v_numParams_4427_);
v___x_4432_ = v___x_4416_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_numParams_4427_);
v___x_4432_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
uint8_t v___x_4433_; lean_object* v___x_4434_; 
v___x_4433_ = 0;
v___x_4434_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4422_, v___x_4432_, v___f_4430_, v___x_4433_, v___x_4433_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
return v___x_4434_;
}
}
else
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
lean_dec(v___x_4424_);
lean_dec_ref(v_type_4422_);
lean_dec(v_levelParams_4421_);
lean_del_object(v___x_4416_);
lean_dec(v___x_4413_);
lean_dec_ref(v_val_4411_);
lean_dec(v_indName_4402_);
lean_dec(v_declName_4401_);
v___x_4436_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4437_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4436_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
return v___x_4437_;
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_del_object(v___x_4416_);
lean_dec(v___x_4413_);
lean_dec_ref(v_val_4411_);
lean_dec(v_indName_4402_);
lean_dec(v_declName_4401_);
v_a_4438_ = lean_ctor_get(v___x_4419_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4419_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4419_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4419_);
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
else
{
lean_dec(v___x_4413_);
lean_dec_ref(v_val_4411_);
lean_dec(v_indName_4402_);
lean_dec(v_declName_4401_);
return v___x_4414_;
}
}
else
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
lean_dec(v_a_4410_);
lean_dec(v_indName_4402_);
lean_dec(v_declName_4401_);
v___x_4448_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4449_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4448_, v_a_4403_, v_a_4404_, v_a_4405_, v_a_4406_);
return v___x_4449_;
}
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_dec(v_indName_4402_);
lean_dec(v_declName_4401_);
v_a_4450_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4409_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4409_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4458_, lean_object* v_indName_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l_Lean_mkCasesOnSameCtor(v_declName_4458_, v_indName_4459_, v_a_4460_, v_a_4461_, v_a_4462_, v_a_4463_);
lean_dec(v_a_4463_);
lean_dec_ref(v_a_4462_);
lean_dec(v_a_4461_);
lean_dec_ref(v_a_4460_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4466_, lean_object* v_params_4467_, lean_object* v_motive_4468_, lean_object* v_as_4469_, size_t v_sz_4470_, size_t v_i_4471_, lean_object* v_bs_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4466_, v_params_4467_, v_motive_4468_, v_sz_4470_, v_i_4471_, v_bs_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4479_, lean_object* v_params_4480_, lean_object* v_motive_4481_, lean_object* v_as_4482_, lean_object* v_sz_4483_, lean_object* v_i_4484_, lean_object* v_bs_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
size_t v_sz_boxed_4491_; size_t v_i_boxed_4492_; lean_object* v_res_4493_; 
v_sz_boxed_4491_ = lean_unbox_usize(v_sz_4483_);
lean_dec(v_sz_4483_);
v_i_boxed_4492_ = lean_unbox_usize(v_i_4484_);
lean_dec(v_i_4484_);
v_res_4493_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4479_, v_params_4480_, v_motive_4481_, v_as_4482_, v_sz_boxed_4491_, v_i_boxed_4492_, v_bs_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec_ref(v_as_4482_);
lean_dec_ref(v_params_4480_);
return v_res_4493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4494_, lean_object* v_params_4495_, lean_object* v_a_4496_, lean_object* v_snd_4497_, lean_object* v_alts_4498_, lean_object* v_as_4499_, size_t v_sz_4500_, size_t v_i_4501_, lean_object* v_bs_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4494_, v_params_4495_, v_a_4496_, v_snd_4497_, v_alts_4498_, v_sz_4500_, v_i_4501_, v_bs_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4509_, lean_object* v_params_4510_, lean_object* v_a_4511_, lean_object* v_snd_4512_, lean_object* v_alts_4513_, lean_object* v_as_4514_, lean_object* v_sz_4515_, lean_object* v_i_4516_, lean_object* v_bs_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
size_t v_sz_boxed_4523_; size_t v_i_boxed_4524_; lean_object* v_res_4525_; 
v_sz_boxed_4523_ = lean_unbox_usize(v_sz_4515_);
lean_dec(v_sz_4515_);
v_i_boxed_4524_ = lean_unbox_usize(v_i_4516_);
lean_dec(v_i_4516_);
v_res_4525_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4509_, v_params_4510_, v_a_4511_, v_snd_4512_, v_alts_4513_, v_as_4514_, v_sz_boxed_4523_, v_i_boxed_4524_, v_bs_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec_ref(v_as_4514_);
lean_dec_ref(v_params_4510_);
return v_res_4525_;
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
