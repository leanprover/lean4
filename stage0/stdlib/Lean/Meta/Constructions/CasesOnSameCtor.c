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
v___x_337_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
lean_ctor_set(v___x_337_, 2, v___x_336_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
lean_ctor_set(v___x_337_, 4, v___x_336_);
lean_ctor_set(v___x_337_, 5, v___x_336_);
lean_ctor_set(v___x_337_, 6, v___x_336_);
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
lean_object* v___f_454_; lean_object* v___x_16060__overap_455_; lean_object* v___x_456_; 
v___f_454_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_16060__overap_455_ = lean_panic_fn_borrowed(v___f_454_, v_msg_448_);
lean_inc(v___y_452_);
lean_inc_ref(v___y_451_);
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
v___x_456_ = lean_apply_5(v___x_16060__overap_455_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, lean_box(0));
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
lean_dec(v_indName_495_);
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
lean_dec(v_indName_495_);
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
lean_dec(v_indName_495_);
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
uint8_t v___x_21160__boxed_560_; uint8_t v___x_21161__boxed_561_; uint8_t v___x_21162__boxed_562_; lean_object* v_res_563_; 
v___x_21160__boxed_560_ = lean_unbox(v___x_541_);
v___x_21161__boxed_561_ = lean_unbox(v___x_542_);
v___x_21162__boxed_562_ = lean_unbox(v___x_543_);
v_res_563_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_538_, v_ism2_539_, v_motive_540_, v___x_21160__boxed_560_, v___x_21161__boxed_561_, v___x_21162__boxed_562_, v_a_544_, v___f_545_, v_zs1_546_, v_val_547_, v___x_548_, v_indName_549_, v_v_550_, v___x_551_, v_params_552_, v___x_553_, v_h_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
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
uint8_t v___x_21272__boxed_596_; uint8_t v___x_21273__boxed_597_; uint8_t v___x_21274__boxed_598_; lean_object* v_res_599_; 
v___x_21272__boxed_596_ = lean_unbox(v___x_586_);
v___x_21273__boxed_597_ = lean_unbox(v___x_587_);
v___x_21274__boxed_598_ = lean_unbox(v___x_588_);
v_res_599_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_582_, v_alts_583_, v___x_584_, v_zs1_585_, v___x_21272__boxed_596_, v___x_21273__boxed_597_, v___x_21274__boxed_598_, v_zs2_589_, v_x_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_);
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
uint8_t v___x_21333__boxed_694_; uint8_t v___x_21334__boxed_695_; uint8_t v___x_21335__boxed_696_; lean_object* v_res_697_; 
v___x_21333__boxed_694_ = lean_unbox(v___x_670_);
v___x_21334__boxed_695_ = lean_unbox(v___x_671_);
v___x_21335__boxed_696_ = lean_unbox(v___x_672_);
v_res_697_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_667_, v_alts_668_, v___x_669_, v___x_21333__boxed_694_, v___x_21334__boxed_695_, v___x_21335__boxed_696_, v___x_673_, v___x_674_, v___x_675_, v_ism2_676_, v_motive_677_, v_a_678_, v_val_679_, v_indName_680_, v_v_681_, v___x_682_, v_params_683_, v___x_684_, v___x_685_, v___x_686_, v_zs1_687_, v_ctorRet1_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
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
uint8_t v___x_21575__boxed_869_; uint8_t v___x_21576__boxed_870_; uint8_t v___x_21577__boxed_871_; lean_object* v_res_872_; 
v___x_21575__boxed_869_ = lean_unbox(v___x_847_);
v___x_21576__boxed_870_ = lean_unbox(v___x_848_);
v___x_21577__boxed_871_ = lean_unbox(v___x_849_);
v_res_872_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_843_, v___x_844_, v_a_845_, v_ism1_846_, v___x_21575__boxed_869_, v___x_21576__boxed_870_, v___x_21577__boxed_871_, v_name_850_, v___x_851_, v_params_852_, v___x_853_, v_tail_854_, v_alts_855_, v_numParams_856_, v_ism2_857_, v_val_858_, v_indName_859_, v___x_860_, v___x_861_, v___x_862_, v_heq_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_);
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
uint8_t v___x_21698__boxed_935_; uint8_t v___x_21699__boxed_936_; uint8_t v___x_21700__boxed_937_; lean_object* v_res_938_; 
v___x_21698__boxed_935_ = lean_unbox(v___x_919_);
v___x_21699__boxed_936_ = lean_unbox(v___x_920_);
v___x_21700__boxed_937_ = lean_unbox(v___x_921_);
v_res_938_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_912_, v_tail_913_, v_params_914_, v_ism1_915_, v_ism2_916_, v_motive_917_, v___x_918_, v___x_21698__boxed_935_, v___x_21699__boxed_936_, v___x_21700__boxed_937_, v_name_922_, v___x_923_, v___x_924_, v_numParams_925_, v_val_926_, v___x_927_, v___x_928_, v_alts_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
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
lean_object* v___x_20571__overap_990_; lean_object* v___x_991_; 
v___x_20571__overap_990_ = l_instInhabitedOfMonad___redArg(v___x_982_, v___x_983_);
lean_inc(v___y_988_);
lean_inc_ref(v___y_987_);
lean_inc(v___y_986_);
lean_inc_ref(v___y_985_);
v___x_991_ = lean_apply_5(v___x_20571__overap_990_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, lean_box(0));
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
uint8_t v___x_22137__boxed_1306_; uint8_t v___x_22138__boxed_1307_; uint8_t v___x_22139__boxed_1308_; lean_object* v_res_1309_; 
v___x_22137__boxed_1306_ = lean_unbox(v___x_1294_);
v___x_22138__boxed_1307_ = lean_unbox(v___x_1295_);
v___x_22139__boxed_1308_ = lean_unbox(v___x_1296_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1287_, v_dummy_1288_, v___x_1289_, v___x_1290_, v___x_1291_, v_motive_1292_, v_zs1_1293_, v___x_22137__boxed_1306_, v___x_22138__boxed_1307_, v___x_22139__boxed_1308_, v_v_1297_, v___x_1298_, v_zs2_1299_, v_ctorRet2_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
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
uint8_t v___x_22278__boxed_1369_; uint8_t v___x_22279__boxed_1370_; uint8_t v___x_22280__boxed_1371_; lean_object* v_res_1372_; 
v___x_22278__boxed_1369_ = lean_unbox(v___x_1356_);
v___x_22279__boxed_1370_ = lean_unbox(v___x_1357_);
v___x_22280__boxed_1371_ = lean_unbox(v___x_1358_);
v_res_1372_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1352_, v___x_1353_, v___x_1354_, v_motive_1355_, v___x_22278__boxed_1369_, v___x_22279__boxed_1370_, v___x_22280__boxed_1371_, v_v_1359_, v___x_1360_, v_a_1361_, v_zs1_1362_, v_ctorRet1_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
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
uint8_t v___x_22458__boxed_1502_; uint8_t v___x_22459__boxed_1503_; uint8_t v___x_22460__boxed_1504_; lean_object* v_res_1505_; 
v___x_22458__boxed_1502_ = lean_unbox(v___x_1487_);
v___x_22459__boxed_1503_ = lean_unbox(v___x_1488_);
v___x_22460__boxed_1504_ = lean_unbox(v___x_1489_);
v_res_1505_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1480_, v_indName_1481_, v_tail_1482_, v_params_1483_, v_ism1_1484_, v_ism2_1485_, v___x_1486_, v___x_22458__boxed_1502_, v___x_22459__boxed_1503_, v___x_22460__boxed_1504_, v_name_1490_, v___x_1491_, v_numParams_1492_, v_val_1493_, v___x_1494_, v___x_1495_, v_motive_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
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
uint8_t v___x_22746__boxed_1731_; lean_object* v_res_1732_; 
v___x_22746__boxed_1731_ = lean_unbox(v___x_1725_);
v_res_1732_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1722_, v_declName_1723_, v_levelParams_1724_, v___x_22746__boxed_1731_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
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
lean_object* v_toCold_1803_; lean_object* v_currRecDepth_1804_; lean_object* v_ref_1805_; uint16_t v_optionFlags_1806_; uint8_t v_suppressElabErrors_1807_; uint8_t v_checkDeprecated_1808_; uint8_t v_isRecordingDeps_1809_; lean_object* v_ref_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_toCold_1803_ = lean_ctor_get(v___y_1800_, 0);
v_currRecDepth_1804_ = lean_ctor_get(v___y_1800_, 1);
v_ref_1805_ = lean_ctor_get(v___y_1800_, 2);
v_optionFlags_1806_ = lean_ctor_get_uint16(v___y_1800_, sizeof(void*)*3);
v_suppressElabErrors_1807_ = lean_ctor_get_uint8(v___y_1800_, sizeof(void*)*3 + 2);
v_checkDeprecated_1808_ = lean_ctor_get_uint8(v___y_1800_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1809_ = lean_ctor_get_uint8(v___y_1800_, sizeof(void*)*3 + 4);
v_ref_1810_ = l_Lean_replaceRef(v_ref_1796_, v_ref_1805_);
lean_inc(v_currRecDepth_1804_);
lean_inc_ref(v_toCold_1803_);
v___x_1811_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1811_, 0, v_toCold_1803_);
lean_ctor_set(v___x_1811_, 1, v_currRecDepth_1804_);
lean_ctor_set(v___x_1811_, 2, v_ref_1810_);
lean_ctor_set_uint16(v___x_1811_, sizeof(void*)*3, v_optionFlags_1806_);
lean_ctor_set_uint8(v___x_1811_, sizeof(void*)*3 + 2, v_suppressElabErrors_1807_);
lean_ctor_set_uint8(v___x_1811_, sizeof(void*)*3 + 3, v_checkDeprecated_1808_);
lean_ctor_set_uint8(v___x_1811_, sizeof(void*)*3 + 4, v_isRecordingDeps_1809_);
v___x_1812_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1797_, v___y_1798_, v___y_1799_, v___x_1811_, v___y_1801_);
lean_dec_ref_known(v___x_1811_, 3);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1813_, lean_object* v_msg_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_){
_start:
{
lean_object* v_res_1820_; 
v_res_1820_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1813_, v_msg_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
lean_dec(v___y_1818_);
lean_dec_ref(v___y_1817_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v_ref_1813_);
return v_res_1820_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1823_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1824_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
lean_ctor_set(v___x_1826_, 2, v___x_1825_);
lean_ctor_set(v___x_1826_, 3, v___x_1825_);
lean_ctor_set(v___x_1826_, 4, v___x_1824_);
lean_ctor_set(v___x_1826_, 5, v___x_1824_);
lean_ctor_set(v___x_1826_, 6, v___x_1824_);
lean_ctor_set(v___x_1826_, 7, v___x_1824_);
lean_ctor_set(v___x_1826_, 8, v___x_1824_);
lean_ctor_set(v___x_1826_, 9, v___x_1824_);
lean_ctor_set(v___x_1826_, 10, v___x_1824_);
lean_ctor_set(v___x_1826_, 11, v___x_1823_);
return v___x_1826_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = lean_unsigned_to_nat(32u);
v___x_1828_ = lean_mk_empty_array_with_capacity(v___x_1827_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1828_);
return v___x_1829_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
size_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1830_ = ((size_t)5ULL);
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = lean_unsigned_to_nat(32u);
v___x_1833_ = lean_mk_empty_array_with_capacity(v___x_1832_);
v___x_1834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1835_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1835_, 0, v___x_1834_);
lean_ctor_set(v___x_1835_, 1, v___x_1833_);
lean_ctor_set(v___x_1835_, 2, v___x_1831_);
lean_ctor_set(v___x_1835_, 3, v___x_1831_);
lean_ctor_set_usize(v___x_1835_, 4, v___x_1830_);
return v___x_1835_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1836_ = lean_box(1);
v___x_1837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1838_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v___x_1837_);
lean_ctor_set(v___x_1839_, 2, v___x_1836_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5));
v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9));
v___x_1848_ = l_Lean_stringToMessageData(v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11));
v___x_1851_ = l_Lean_stringToMessageData(v___x_1850_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13));
v___x_1854_ = l_Lean_stringToMessageData(v___x_1853_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15));
v___x_1857_ = l_Lean_stringToMessageData(v___x_1856_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17));
v___x_1860_ = l_Lean_stringToMessageData(v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1861_, lean_object* v_declHint_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v_env_1867_; uint8_t v___x_1868_; 
v___x_1865_ = lean_box(0);
v___x_1866_ = lean_st_ref_get(v___y_1863_);
v_env_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc_ref(v_env_1867_);
lean_dec(v___x_1866_);
v___x_1868_ = l_Lean_Name_isAnonymous(v_declHint_1862_);
if (v___x_1868_ == 0)
{
uint8_t v_isExporting_1869_; 
v_isExporting_1869_ = lean_ctor_get_uint8(v_env_1867_, sizeof(void*)*13);
if (v_isExporting_1869_ == 0)
{
lean_object* v___x_1870_; 
lean_dec_ref(v_env_1867_);
lean_dec(v_declHint_1862_);
v___x_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1870_, 0, v_msg_1861_);
return v___x_1870_;
}
else
{
lean_object* v___x_1871_; uint8_t v___x_1872_; 
lean_inc_ref(v_env_1867_);
v___x_1871_ = l_Lean_Environment_setExporting(v_env_1867_, v___x_1868_);
lean_inc(v_declHint_1862_);
lean_inc_ref(v___x_1871_);
v___x_1872_ = l_Lean_Environment_contains(v___x_1871_, v_declHint_1862_, v_isExporting_1869_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_dec_ref(v___x_1871_);
lean_dec_ref(v_env_1867_);
lean_dec(v_declHint_1862_);
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v_msg_1861_);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_c_1879_; lean_object* v___x_1880_; 
v___x_1874_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1876_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1871_);
v___x_1877_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1871_);
lean_ctor_set(v___x_1877_, 1, v___x_1874_);
lean_ctor_set(v___x_1877_, 2, v___x_1875_);
lean_ctor_set(v___x_1877_, 3, v___x_1876_);
lean_inc(v_declHint_1862_);
v___x_1878_ = l_Lean_MessageData_ofConstName(v_declHint_1862_, v___x_1868_);
v_c_1879_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1879_, 0, v___x_1877_);
lean_ctor_set(v_c_1879_, 1, v___x_1878_);
v___x_1880_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1871_, v_declHint_1862_);
lean_dec_ref(v___x_1871_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_dec_ref(v_env_1867_);
lean_dec(v_declHint_1862_);
v___x_1881_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v_c_1879_);
v___x_1883_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = l_Lean_MessageData_note(v___x_1884_);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v_msg_1861_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
return v___x_1887_;
}
else
{
lean_object* v_val_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1922_; 
v_val_1888_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1890_ = v___x_1880_;
v_isShared_1891_ = v_isSharedCheck_1922_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_val_1888_);
lean_dec(v___x_1880_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1922_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1892_; lean_object* v_moduleNames_1893_; lean_object* v_mod_1894_; uint8_t v___x_1895_; 
v___x_1892_ = l_Lean_Environment_header(v_env_1867_);
lean_dec_ref(v_env_1867_);
v_moduleNames_1893_ = lean_ctor_get(v___x_1892_, 4);
lean_inc_ref(v_moduleNames_1893_);
lean_dec_ref(v___x_1892_);
v_mod_1894_ = lean_array_get(v___x_1865_, v_moduleNames_1893_, v_val_1888_);
lean_dec(v_val_1888_);
lean_dec_ref(v_moduleNames_1893_);
v___x_1895_ = l_Lean_isPrivateName(v_declHint_1862_);
lean_dec(v_declHint_1862_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1896_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10);
v___x_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v_c_1879_);
v___x_1898_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = l_Lean_MessageData_ofName(v_mod_1894_);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_MessageData_note(v___x_1903_);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_msg_1861_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1905_);
v___x_1907_ = v___x_1890_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1909_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v_c_1879_);
v___x_1911_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = l_Lean_MessageData_ofName(v_mod_1894_);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_MessageData_note(v___x_1916_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_msg_1861_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set_tag(v___x_1890_, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1918_);
v___x_1920_ = v___x_1890_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1923_; 
lean_dec_ref(v_env_1867_);
lean_dec(v_declHint_1862_);
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_msg_1861_);
return v___x_1923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1924_, lean_object* v_declHint_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1924_, v_declHint_1925_, v___y_1926_);
lean_dec(v___y_1926_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1929_, lean_object* v_declHint_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v___x_1936_; lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1946_; 
v___x_1936_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1929_, v_declHint_1930_, v___y_1934_);
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1939_ = v___x_1936_;
v_isShared_1940_ = v_isSharedCheck_1946_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1936_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1946_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1941_ = l_Lean_unknownIdentifierMessageTag;
v___x_1942_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
lean_ctor_set(v___x_1942_, 1, v_a_1937_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 0, v___x_1942_);
v___x_1944_ = v___x_1939_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1947_, lean_object* v_declHint_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v_res_1954_; 
v_res_1954_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1947_, v_declHint_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1955_, lean_object* v_msg_1956_, lean_object* v_declHint_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; lean_object* v_a_1964_; lean_object* v___x_1965_; 
v___x_1963_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1956_, v_declHint_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref(v___x_1963_);
v___x_1965_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1955_, v_a_1964_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1966_, lean_object* v_msg_1967_, lean_object* v_declHint_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v_res_1974_; 
v_res_1974_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1966_, v_msg_1967_, v_declHint_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_ref_1966_);
return v_res_1974_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_1977_ = l_Lean_stringToMessageData(v___x_1976_);
return v___x_1977_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_1980_ = l_Lean_stringToMessageData(v___x_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_1981_, lean_object* v_constName_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v___x_1988_; uint8_t v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1988_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_1989_ = 0;
lean_inc(v_constName_1982_);
v___x_1990_ = l_Lean_MessageData_ofConstName(v_constName_1982_, v___x_1989_);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1988_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1981_, v___x_1993_, v_constName_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_1995_, lean_object* v_constName_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1995_, v_constName_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
lean_dec(v_ref_1995_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_ref_2009_; lean_object* v___x_2010_; 
v_ref_2009_ = lean_ctor_get(v___y_2006_, 2);
v___x_2010_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2009_, v_constName_2003_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
return v___x_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
lean_dec(v___y_2013_);
lean_dec_ref(v___y_2012_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_){
_start:
{
lean_object* v___x_2024_; lean_object* v_env_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; 
v___x_2024_ = lean_st_ref_get(v___y_2022_);
v_env_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc_ref(v_env_2025_);
lean_dec(v___x_2024_);
v___x_2026_ = 0;
lean_inc(v_constName_2018_);
v___x_2027_ = l_Lean_Environment_findConstVal_x3f(v_env_2025_, v_constName_2018_, v___x_2026_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2018_, v___y_2019_, v___y_2020_, v___y_2021_, v___y_2022_);
return v___x_2028_;
}
else
{
lean_object* v_val_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2036_; 
lean_dec(v_constName_2018_);
v_val_2029_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2031_ = v___x_2027_;
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_val_2029_);
lean_dec(v___x_2027_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2036_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2034_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set_tag(v___x_2031_, 0);
v___x_2034_ = v___x_2031_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_val_2029_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2044_, uint8_t v_s_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v___x_2049_; lean_object* v_env_2050_; lean_object* v_nextMacroScope_2051_; lean_object* v_ngen_2052_; lean_object* v_auxDeclNGen_2053_; lean_object* v_traceState_2054_; lean_object* v_recordedDeps_2055_; lean_object* v_messages_2056_; lean_object* v_infoState_2057_; lean_object* v_snapshotTasks_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2087_; 
v___x_2049_ = lean_st_ref_take(v___y_2047_);
v_env_2050_ = lean_ctor_get(v___x_2049_, 0);
v_nextMacroScope_2051_ = lean_ctor_get(v___x_2049_, 1);
v_ngen_2052_ = lean_ctor_get(v___x_2049_, 2);
v_auxDeclNGen_2053_ = lean_ctor_get(v___x_2049_, 3);
v_traceState_2054_ = lean_ctor_get(v___x_2049_, 4);
v_recordedDeps_2055_ = lean_ctor_get(v___x_2049_, 6);
v_messages_2056_ = lean_ctor_get(v___x_2049_, 7);
v_infoState_2057_ = lean_ctor_get(v___x_2049_, 8);
v_snapshotTasks_2058_ = lean_ctor_get(v___x_2049_, 9);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v___x_2049_, 5);
lean_dec(v_unused_2088_);
v___x_2060_ = v___x_2049_;
v_isShared_2061_ = v_isSharedCheck_2087_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_snapshotTasks_2058_);
lean_inc(v_infoState_2057_);
lean_inc(v_messages_2056_);
lean_inc(v_recordedDeps_2055_);
lean_inc(v_traceState_2054_);
lean_inc(v_auxDeclNGen_2053_);
lean_inc(v_ngen_2052_);
lean_inc(v_nextMacroScope_2051_);
lean_inc(v_env_2050_);
lean_dec(v___x_2049_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2087_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
uint8_t v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2062_ = 0;
v___x_2063_ = lean_box(0);
v___x_2064_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2050_, v_declName_2044_, v_s_2045_, v___x_2062_, v___x_2063_);
v___x_2065_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 5, v___x_2065_);
lean_ctor_set(v___x_2060_, 0, v___x_2064_);
v___x_2067_ = v___x_2060_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2064_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_nextMacroScope_2051_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_ngen_2052_);
lean_ctor_set(v_reuseFailAlloc_2086_, 3, v_auxDeclNGen_2053_);
lean_ctor_set(v_reuseFailAlloc_2086_, 4, v_traceState_2054_);
lean_ctor_set(v_reuseFailAlloc_2086_, 5, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2086_, 6, v_recordedDeps_2055_);
lean_ctor_set(v_reuseFailAlloc_2086_, 7, v_messages_2056_);
lean_ctor_set(v_reuseFailAlloc_2086_, 8, v_infoState_2057_);
lean_ctor_set(v_reuseFailAlloc_2086_, 9, v_snapshotTasks_2058_);
v___x_2067_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v_mctx_2070_; lean_object* v_zetaDeltaFVarIds_2071_; lean_object* v_postponed_2072_; lean_object* v_diag_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2084_; 
v___x_2068_ = lean_st_ref_put(v___y_2047_, v___x_2067_);
v___x_2069_ = lean_st_ref_take(v___y_2046_);
v_mctx_2070_ = lean_ctor_get(v___x_2069_, 0);
v_zetaDeltaFVarIds_2071_ = lean_ctor_get(v___x_2069_, 2);
v_postponed_2072_ = lean_ctor_get(v___x_2069_, 3);
v_diag_2073_ = lean_ctor_get(v___x_2069_, 4);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2084_ == 0)
{
lean_object* v_unused_2085_; 
v_unused_2085_ = lean_ctor_get(v___x_2069_, 1);
lean_dec(v_unused_2085_);
v___x_2075_ = v___x_2069_;
v_isShared_2076_ = v_isSharedCheck_2084_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_diag_2073_);
lean_inc(v_postponed_2072_);
lean_inc(v_zetaDeltaFVarIds_2071_);
lean_inc(v_mctx_2070_);
lean_dec(v___x_2069_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2084_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 1, v___x_2078_);
v___x_2080_ = v___x_2075_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_mctx_2070_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v_zetaDeltaFVarIds_2071_);
lean_ctor_set(v_reuseFailAlloc_2083_, 3, v_postponed_2072_);
lean_ctor_set(v_reuseFailAlloc_2083_, 4, v_diag_2073_);
v___x_2080_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_st_ref_put(v___y_2046_, v___x_2080_);
v___x_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2082_, 0, v___x_2077_);
return v___x_2082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2089_, lean_object* v_s_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
uint8_t v_s_boxed_2094_; lean_object* v_res_2095_; 
v_s_boxed_2094_ = lean_unbox(v_s_2090_);
v_res_2095_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2089_, v_s_boxed_2094_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec(v___y_2091_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
uint8_t v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = 0;
v___x_2103_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2096_, v___x_2102_, v___y_2098_, v___y_2100_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2110_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2120_, lean_object* v_declName_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2127_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2128_ = l_Lean_MessageData_ofName(v_attrName_2120_);
v___x_2129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2129_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = 0;
v___x_2133_ = l_Lean_MessageData_ofConstName(v_declName_2121_, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2131_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2136_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2138_, lean_object* v_declName_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2138_, v_declName_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0(lean_object* v_addEntryFn_2146_, lean_object* v_decl_2147_, lean_object* v_s_2148_){
_start:
{
lean_object* v_importedEntries_2149_; lean_object* v_state_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2158_; 
v_importedEntries_2149_ = lean_ctor_get(v_s_2148_, 0);
v_state_2150_ = lean_ctor_get(v_s_2148_, 1);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_s_2148_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2152_ = v_s_2148_;
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_state_2150_);
lean_inc(v_importedEntries_2149_);
lean_dec(v_s_2148_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2158_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_state_2154_; lean_object* v___x_2156_; 
v_state_2154_ = lean_apply_2(v_addEntryFn_2146_, v_state_2150_, v_decl_2147_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 1, v_state_2154_);
v___x_2156_ = v___x_2152_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_importedEntries_2149_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v_state_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2160_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2161_ = l_Lean_stringToMessageData(v___x_2160_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2164_ = l_Lean_stringToMessageData(v___x_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2165_, lean_object* v_declName_2166_, lean_object* v_asyncPrefix_x3f_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___y_2174_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2167_) == 0)
{
lean_object* v___x_2187_; 
v___x_2187_ = l_Lean_MessageData_nil;
v___y_2174_ = v___x_2187_;
goto v___jp_2173_;
}
else
{
lean_object* v_val_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v_val_2188_ = lean_ctor_get(v_asyncPrefix_x3f_2167_, 0);
lean_inc(v_val_2188_);
lean_dec_ref_known(v_asyncPrefix_x3f_2167_, 1);
v___x_2189_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2190_ = l_Lean_MessageData_ofName(v_val_2188_);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___y_2174_ = v___x_2193_;
goto v___jp_2173_;
}
v___jp_2173_:
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2175_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2176_ = l_Lean_MessageData_ofName(v_attrName_2165_);
v___x_2177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = 0;
v___x_2181_ = l_Lean_MessageData_ofConstName(v_declName_2166_, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2179_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v___y_2174_);
v___x_2186_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2185_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
return v___x_2186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2194_, lean_object* v_declName_2195_, lean_object* v_asyncPrefix_x3f_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2194_, v_declName_2195_, v_asyncPrefix_x3f_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2203_, lean_object* v_decl_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v___y_2217_; lean_object* v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2220_; lean_object* v___y_2221_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___x_2265_; lean_object* v_env_2266_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___x_2281_; 
v___x_2265_ = lean_st_ref_get(v___y_2208_);
v_env_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc_ref(v_env_2266_);
lean_dec(v___x_2265_);
v___x_2281_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2266_, v_decl_2204_);
if (lean_obj_tag(v___x_2281_) == 0)
{
v___y_2268_ = v___y_2205_;
v___y_2269_ = v___y_2206_;
v___y_2270_ = v___y_2207_;
v___y_2271_ = v___y_2208_;
goto v___jp_2267_;
}
else
{
lean_object* v_attr_2282_; lean_object* v_toAttributeImplCore_2283_; lean_object* v_name_2284_; lean_object* v___x_2285_; 
lean_dec_ref_known(v___x_2281_, 1);
lean_dec_ref(v_env_2266_);
v_attr_2282_ = lean_ctor_get(v_attr_2203_, 0);
lean_inc_ref(v_attr_2282_);
lean_dec_ref(v_attr_2203_);
v_toAttributeImplCore_2283_ = lean_ctor_get(v_attr_2282_, 0);
lean_inc_ref(v_toAttributeImplCore_2283_);
lean_dec_ref(v_attr_2282_);
v_name_2284_ = lean_ctor_get(v_toAttributeImplCore_2283_, 1);
lean_inc(v_name_2284_);
lean_dec_ref(v_toAttributeImplCore_2283_);
v___x_2285_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2284_, v_decl_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
return v___x_2285_;
}
v___jp_2210_:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v_mctx_2226_; lean_object* v_zetaDeltaFVarIds_2227_; lean_object* v_postponed_2228_; lean_object* v_diag_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2240_; 
v___x_2222_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
v___x_2223_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2223_, 0, v___y_2221_);
lean_ctor_set(v___x_2223_, 1, v___y_2214_);
lean_ctor_set(v___x_2223_, 2, v___y_2213_);
lean_ctor_set(v___x_2223_, 3, v___y_2220_);
lean_ctor_set(v___x_2223_, 4, v___y_2211_);
lean_ctor_set(v___x_2223_, 5, v___x_2222_);
lean_ctor_set(v___x_2223_, 6, v___y_2219_);
lean_ctor_set(v___x_2223_, 7, v___y_2212_);
lean_ctor_set(v___x_2223_, 8, v___y_2216_);
lean_ctor_set(v___x_2223_, 9, v___y_2215_);
v___x_2224_ = lean_st_ref_put(v___y_2218_, v___x_2223_);
v___x_2225_ = lean_st_ref_take(v___y_2217_);
v_mctx_2226_ = lean_ctor_get(v___x_2225_, 0);
v_zetaDeltaFVarIds_2227_ = lean_ctor_get(v___x_2225_, 2);
v_postponed_2228_ = lean_ctor_get(v___x_2225_, 3);
v_diag_2229_ = lean_ctor_get(v___x_2225_, 4);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v___x_2225_, 1);
lean_dec(v_unused_2241_);
v___x_2231_ = v___x_2225_;
v_isShared_2232_ = v_isSharedCheck_2240_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_diag_2229_);
lean_inc(v_postponed_2228_);
lean_inc(v_zetaDeltaFVarIds_2227_);
lean_inc(v_mctx_2226_);
lean_dec(v___x_2225_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2240_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2233_ = lean_box(0);
v___x_2234_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v___x_2234_);
v___x_2236_ = v___x_2231_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_mctx_2226_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2239_, 2, v_zetaDeltaFVarIds_2227_);
lean_ctor_set(v_reuseFailAlloc_2239_, 3, v_postponed_2228_);
lean_ctor_set(v_reuseFailAlloc_2239_, 4, v_diag_2229_);
v___x_2236_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = lean_st_ref_put(v___y_2217_, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2233_);
return v___x_2238_;
}
}
}
v___jp_2242_:
{
lean_object* v___x_2245_; lean_object* v_ext_2246_; lean_object* v_toEnvExtension_2247_; lean_object* v_env_2248_; lean_object* v_nextMacroScope_2249_; lean_object* v_ngen_2250_; lean_object* v_auxDeclNGen_2251_; lean_object* v_traceState_2252_; lean_object* v_recordedDeps_2253_; lean_object* v_messages_2254_; lean_object* v_infoState_2255_; lean_object* v_snapshotTasks_2256_; lean_object* v_addEntryFn_2257_; lean_object* v_asyncMode_2258_; uint8_t v_logWrites_2259_; lean_object* v___f_2260_; uint8_t v___x_2261_; 
v___x_2245_ = lean_st_ref_take(v___y_2244_);
v_ext_2246_ = lean_ctor_get(v_attr_2203_, 1);
lean_inc_ref(v_ext_2246_);
lean_dec_ref(v_attr_2203_);
v_toEnvExtension_2247_ = lean_ctor_get(v_ext_2246_, 0);
lean_inc_ref(v_toEnvExtension_2247_);
v_env_2248_ = lean_ctor_get(v___x_2245_, 0);
lean_inc_ref(v_env_2248_);
v_nextMacroScope_2249_ = lean_ctor_get(v___x_2245_, 1);
lean_inc(v_nextMacroScope_2249_);
v_ngen_2250_ = lean_ctor_get(v___x_2245_, 2);
lean_inc_ref(v_ngen_2250_);
v_auxDeclNGen_2251_ = lean_ctor_get(v___x_2245_, 3);
lean_inc_ref(v_auxDeclNGen_2251_);
v_traceState_2252_ = lean_ctor_get(v___x_2245_, 4);
lean_inc_ref(v_traceState_2252_);
v_recordedDeps_2253_ = lean_ctor_get(v___x_2245_, 6);
lean_inc_ref(v_recordedDeps_2253_);
v_messages_2254_ = lean_ctor_get(v___x_2245_, 7);
lean_inc_ref(v_messages_2254_);
v_infoState_2255_ = lean_ctor_get(v___x_2245_, 8);
lean_inc_ref(v_infoState_2255_);
v_snapshotTasks_2256_ = lean_ctor_get(v___x_2245_, 9);
lean_inc_ref(v_snapshotTasks_2256_);
lean_dec(v___x_2245_);
v_addEntryFn_2257_ = lean_ctor_get(v_ext_2246_, 3);
lean_inc(v_addEntryFn_2257_);
lean_dec_ref(v_ext_2246_);
v_asyncMode_2258_ = lean_ctor_get(v_toEnvExtension_2247_, 2);
lean_inc(v_asyncMode_2258_);
v_logWrites_2259_ = lean_ctor_get_uint8(v_toEnvExtension_2247_, sizeof(void*)*6);
lean_inc(v_decl_2204_);
v___f_2260_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___lam__0), 3, 2);
lean_closure_set(v___f_2260_, 0, v_addEntryFn_2257_);
lean_closure_set(v___f_2260_, 1, v_decl_2204_);
v___x_2261_ = 1;
if (v_logWrites_2259_ == 0)
{
lean_object* v___x_2262_; 
v___x_2262_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2247_, v_env_2248_, v___f_2260_, v_asyncMode_2258_, v_decl_2204_, v___x_2261_);
lean_dec(v_asyncMode_2258_);
v___y_2211_ = v_traceState_2252_;
v___y_2212_ = v_messages_2254_;
v___y_2213_ = v_ngen_2250_;
v___y_2214_ = v_nextMacroScope_2249_;
v___y_2215_ = v_snapshotTasks_2256_;
v___y_2216_ = v_infoState_2255_;
v___y_2217_ = v___y_2243_;
v___y_2218_ = v___y_2244_;
v___y_2219_ = v_recordedDeps_2253_;
v___y_2220_ = v_auxDeclNGen_2251_;
v___y_2221_ = v___x_2262_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
lean_inc_ref(v_toEnvExtension_2247_);
v___x_2263_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2247_, v_env_2248_);
lean_dec_ref(v_env_2248_);
v___x_2264_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2247_, v___x_2263_, v___f_2260_, v_asyncMode_2258_, v_decl_2204_, v___x_2261_);
lean_dec(v_asyncMode_2258_);
v___y_2211_ = v_traceState_2252_;
v___y_2212_ = v_messages_2254_;
v___y_2213_ = v_ngen_2250_;
v___y_2214_ = v_nextMacroScope_2249_;
v___y_2215_ = v_snapshotTasks_2256_;
v___y_2216_ = v_infoState_2255_;
v___y_2217_ = v___y_2243_;
v___y_2218_ = v___y_2244_;
v___y_2219_ = v_recordedDeps_2253_;
v___y_2220_ = v_auxDeclNGen_2251_;
v___y_2221_ = v___x_2264_;
goto v___jp_2210_;
}
}
v___jp_2267_:
{
lean_object* v_ext_2272_; lean_object* v_toEnvExtension_2273_; lean_object* v_attr_2274_; lean_object* v_asyncMode_2275_; uint8_t v___x_2276_; 
v_ext_2272_ = lean_ctor_get(v_attr_2203_, 1);
v_toEnvExtension_2273_ = lean_ctor_get(v_ext_2272_, 0);
v_attr_2274_ = lean_ctor_get(v_attr_2203_, 0);
v_asyncMode_2275_ = lean_ctor_get(v_toEnvExtension_2273_, 2);
lean_inc(v_decl_2204_);
lean_inc_ref(v_env_2266_);
v___x_2276_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2266_, v_decl_2204_, v_asyncMode_2275_);
if (v___x_2276_ == 0)
{
lean_object* v_toAttributeImplCore_2277_; lean_object* v_name_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_inc_ref(v_attr_2274_);
lean_dec_ref(v_attr_2203_);
v_toAttributeImplCore_2277_ = lean_ctor_get(v_attr_2274_, 0);
lean_inc_ref(v_toAttributeImplCore_2277_);
lean_dec_ref(v_attr_2274_);
v_name_2278_ = lean_ctor_get(v_toAttributeImplCore_2277_, 1);
lean_inc(v_name_2278_);
lean_dec_ref(v_toAttributeImplCore_2277_);
v___x_2279_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2266_);
v___x_2280_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2278_, v_decl_2204_, v___x_2279_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2280_;
}
else
{
lean_dec_ref(v_env_2266_);
v___y_2243_ = v___y_2269_;
v___y_2244_ = v___y_2271_;
goto v___jp_2242_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2286_, lean_object* v_decl_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2286_, v_decl_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; lean_object* v_env_2301_; uint8_t v___x_2302_; lean_object* v___x_2303_; 
v___x_2300_ = lean_st_ref_get(v___y_2298_);
v_env_2301_ = lean_ctor_get(v___x_2300_, 0);
lean_inc_ref(v_env_2301_);
lean_dec(v___x_2300_);
v___x_2302_ = 0;
lean_inc(v_constName_2294_);
v___x_2303_ = l_Lean_Environment_find_x3f(v_env_2301_, v_constName_2294_, v___x_2302_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2304_;
}
else
{
lean_object* v_val_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec(v_constName_2294_);
v_val_2305_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2303_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_val_2305_);
lean_dec(v___x_2303_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
lean_ctor_set_tag(v___x_2307_, 0);
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_val_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
lean_object* v_res_2319_; 
v_res_2319_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
return v_res_2319_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2323_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2324_ = lean_unsigned_to_nat(58u);
v___x_2325_ = lean_unsigned_to_nat(33u);
v___x_2326_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2327_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2328_ = l_mkPanicMessageWithDecl(v___x_2327_, v___x_2326_, v___x_2325_, v___x_2324_, v___x_2323_);
return v___x_2328_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2330_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2331_ = lean_unsigned_to_nat(60u);
v___x_2332_ = lean_unsigned_to_nat(30u);
v___x_2333_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2334_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2335_ = l_mkPanicMessageWithDecl(v___x_2334_, v___x_2333_, v___x_2332_, v___x_2331_, v___x_2330_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2336_, lean_object* v_indName_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___x_2343_; 
lean_inc(v_indName_2337_);
v___x_2343_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
if (lean_obj_tag(v_a_2344_) == 5)
{
lean_object* v_val_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2535_; 
v_val_2345_ = lean_ctor_get(v_a_2344_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_a_2344_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2347_ = v_a_2344_;
v_isShared_2348_ = v_isSharedCheck_2535_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_val_2345_);
lean_dec(v_a_2344_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2535_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; 
lean_inc(v_indName_2337_);
v___x_2349_ = l_Lean_mkCasesOnName(v_indName_2337_);
lean_inc(v___x_2349_);
v___x_2350_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2349_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v_name_2352_; lean_object* v_levelParams_2353_; lean_object* v_type_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref_known(v___x_2350_, 1);
v_name_2352_ = lean_ctor_get(v_a_2351_, 0);
lean_inc(v_name_2352_);
v_levelParams_2353_ = lean_ctor_get(v_a_2351_, 1);
lean_inc_n(v_levelParams_2353_, 2);
v_type_2354_ = lean_ctor_get(v_a_2351_, 2);
lean_inc_ref(v_type_2354_);
lean_dec(v_a_2351_);
v___x_2355_ = lean_box(0);
v___x_2356_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2353_, v___x_2355_);
if (lean_obj_tag(v___x_2356_) == 1)
{
lean_object* v_head_2357_; lean_object* v_tail_2358_; lean_object* v_numParams_2359_; lean_object* v_numIndices_2360_; lean_object* v_ctors_2361_; lean_object* v___f_2362_; lean_object* v___x_2364_; 
v_head_2357_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_head_2357_);
v_tail_2358_ = lean_ctor_get(v___x_2356_, 1);
lean_inc(v_tail_2358_);
v_numParams_2359_ = lean_ctor_get(v_val_2345_, 1);
lean_inc_n(v_numParams_2359_, 2);
v_numIndices_2360_ = lean_ctor_get(v_val_2345_, 2);
lean_inc(v_numIndices_2360_);
v_ctors_2361_ = lean_ctor_get(v_val_2345_, 4);
lean_inc(v_ctors_2361_);
v___f_2362_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2362_, 0, v_numIndices_2360_);
lean_closure_set(v___f_2362_, 1, v_head_2357_);
lean_closure_set(v___f_2362_, 2, v_ctors_2361_);
lean_closure_set(v___f_2362_, 3, v_indName_2337_);
lean_closure_set(v___f_2362_, 4, v_tail_2358_);
lean_closure_set(v___f_2362_, 5, v_name_2352_);
lean_closure_set(v___f_2362_, 6, v___x_2356_);
lean_closure_set(v___f_2362_, 7, v_numParams_2359_);
lean_closure_set(v___f_2362_, 8, v_val_2345_);
lean_closure_set(v___f_2362_, 9, v___x_2349_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 1);
lean_ctor_set(v___x_2347_, 0, v_numParams_2359_);
v___x_2364_ = v___x_2347_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_numParams_2359_);
v___x_2364_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
uint8_t v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = 0;
v___x_2366_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2354_, v___x_2364_, v___f_2362_, v___x_2365_, v___x_2365_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; lean_object* v___f_2369_; uint8_t v___y_2371_; uint8_t v___x_2514_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = lean_box(v___x_2365_);
lean_inc(v_declName_2336_);
v___f_2369_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2369_, 0, v_a_2367_);
lean_closure_set(v___f_2369_, 1, v_declName_2336_);
lean_closure_set(v___f_2369_, 2, v_levelParams_2353_);
lean_closure_set(v___f_2369_, 3, v___x_2368_);
v___x_2514_ = l_Lean_isPrivateName(v_declName_2336_);
if (v___x_2514_ == 0)
{
uint8_t v___x_2515_; 
v___x_2515_ = 1;
v___y_2371_ = v___x_2515_;
goto v___jp_2370_;
}
else
{
v___y_2371_ = v___x_2365_;
goto v___jp_2370_;
}
v___jp_2370_:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2369_, v___y_2371_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2373_; lean_object* v_env_2374_; lean_object* v_nextMacroScope_2375_; lean_object* v_ngen_2376_; lean_object* v_auxDeclNGen_2377_; lean_object* v_traceState_2378_; lean_object* v_recordedDeps_2379_; lean_object* v_messages_2380_; lean_object* v_infoState_2381_; lean_object* v_snapshotTasks_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2512_; 
lean_dec_ref_known(v___x_2372_, 1);
v___x_2373_ = lean_st_ref_take(v_a_2341_);
v_env_2374_ = lean_ctor_get(v___x_2373_, 0);
v_nextMacroScope_2375_ = lean_ctor_get(v___x_2373_, 1);
v_ngen_2376_ = lean_ctor_get(v___x_2373_, 2);
v_auxDeclNGen_2377_ = lean_ctor_get(v___x_2373_, 3);
v_traceState_2378_ = lean_ctor_get(v___x_2373_, 4);
v_recordedDeps_2379_ = lean_ctor_get(v___x_2373_, 6);
v_messages_2380_ = lean_ctor_get(v___x_2373_, 7);
v_infoState_2381_ = lean_ctor_get(v___x_2373_, 8);
v_snapshotTasks_2382_ = lean_ctor_get(v___x_2373_, 9);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2373_, 5);
lean_dec(v_unused_2513_);
v___x_2384_ = v___x_2373_;
v_isShared_2385_ = v_isSharedCheck_2512_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_snapshotTasks_2382_);
lean_inc(v_infoState_2381_);
lean_inc(v_messages_2380_);
lean_inc(v_recordedDeps_2379_);
lean_inc(v_traceState_2378_);
lean_inc(v_auxDeclNGen_2377_);
lean_inc(v_ngen_2376_);
lean_inc(v_nextMacroScope_2375_);
lean_inc(v_env_2374_);
lean_dec(v___x_2373_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2512_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
lean_inc(v_declName_2336_);
v___x_2386_ = l_Lean_Meta_markMatcherLike(v_env_2374_, v_declName_2336_);
v___x_2387_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 5, v___x_2387_);
lean_ctor_set(v___x_2384_, 0, v___x_2386_);
v___x_2389_ = v___x_2384_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2386_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_nextMacroScope_2375_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v_ngen_2376_);
lean_ctor_set(v_reuseFailAlloc_2511_, 3, v_auxDeclNGen_2377_);
lean_ctor_set(v_reuseFailAlloc_2511_, 4, v_traceState_2378_);
lean_ctor_set(v_reuseFailAlloc_2511_, 5, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2511_, 6, v_recordedDeps_2379_);
lean_ctor_set(v_reuseFailAlloc_2511_, 7, v_messages_2380_);
lean_ctor_set(v_reuseFailAlloc_2511_, 8, v_infoState_2381_);
lean_ctor_set(v_reuseFailAlloc_2511_, 9, v_snapshotTasks_2382_);
v___x_2389_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v_mctx_2392_; lean_object* v_zetaDeltaFVarIds_2393_; lean_object* v_postponed_2394_; lean_object* v_diag_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2509_; 
v___x_2390_ = lean_st_ref_put(v_a_2341_, v___x_2389_);
v___x_2391_ = lean_st_ref_take(v_a_2339_);
v_mctx_2392_ = lean_ctor_get(v___x_2391_, 0);
v_zetaDeltaFVarIds_2393_ = lean_ctor_get(v___x_2391_, 2);
v_postponed_2394_ = lean_ctor_get(v___x_2391_, 3);
v_diag_2395_ = lean_ctor_get(v___x_2391_, 4);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2509_ == 0)
{
lean_object* v_unused_2510_; 
v_unused_2510_ = lean_ctor_get(v___x_2391_, 1);
lean_dec(v_unused_2510_);
v___x_2397_ = v___x_2391_;
v_isShared_2398_ = v_isSharedCheck_2509_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_diag_2395_);
lean_inc(v_postponed_2394_);
lean_inc(v_zetaDeltaFVarIds_2393_);
lean_inc(v_mctx_2392_);
lean_dec(v___x_2391_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2509_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; lean_object* v___x_2401_; 
v___x_2399_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 1, v___x_2399_);
v___x_2401_ = v___x_2397_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_mctx_2392_);
lean_ctor_set(v_reuseFailAlloc_2508_, 1, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2508_, 2, v_zetaDeltaFVarIds_2393_);
lean_ctor_set(v_reuseFailAlloc_2508_, 3, v_postponed_2394_);
lean_ctor_set(v_reuseFailAlloc_2508_, 4, v_diag_2395_);
v___x_2401_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v_env_2404_; lean_object* v_nextMacroScope_2405_; lean_object* v_ngen_2406_; lean_object* v_auxDeclNGen_2407_; lean_object* v_traceState_2408_; lean_object* v_recordedDeps_2409_; lean_object* v_messages_2410_; lean_object* v_infoState_2411_; lean_object* v_snapshotTasks_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2506_; 
v___x_2402_ = lean_st_ref_put(v_a_2339_, v___x_2401_);
v___x_2403_ = lean_st_ref_take(v_a_2341_);
v_env_2404_ = lean_ctor_get(v___x_2403_, 0);
v_nextMacroScope_2405_ = lean_ctor_get(v___x_2403_, 1);
v_ngen_2406_ = lean_ctor_get(v___x_2403_, 2);
v_auxDeclNGen_2407_ = lean_ctor_get(v___x_2403_, 3);
v_traceState_2408_ = lean_ctor_get(v___x_2403_, 4);
v_recordedDeps_2409_ = lean_ctor_get(v___x_2403_, 6);
v_messages_2410_ = lean_ctor_get(v___x_2403_, 7);
v_infoState_2411_ = lean_ctor_get(v___x_2403_, 8);
v_snapshotTasks_2412_ = lean_ctor_get(v___x_2403_, 9);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2506_ == 0)
{
lean_object* v_unused_2507_; 
v_unused_2507_ = lean_ctor_get(v___x_2403_, 5);
lean_dec(v_unused_2507_);
v___x_2414_ = v___x_2403_;
v_isShared_2415_ = v_isSharedCheck_2506_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_snapshotTasks_2412_);
lean_inc(v_infoState_2411_);
lean_inc(v_messages_2410_);
lean_inc(v_recordedDeps_2409_);
lean_inc(v_traceState_2408_);
lean_inc(v_auxDeclNGen_2407_);
lean_inc(v_ngen_2406_);
lean_inc(v_nextMacroScope_2405_);
lean_inc(v_env_2404_);
lean_dec(v___x_2403_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2506_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2418_; 
lean_inc(v_declName_2336_);
v___x_2416_ = l_Lean_markAuxRecursor(v_env_2404_, v_declName_2336_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 5, v___x_2387_);
lean_ctor_set(v___x_2414_, 0, v___x_2416_);
v___x_2418_ = v___x_2414_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_nextMacroScope_2405_);
lean_ctor_set(v_reuseFailAlloc_2505_, 2, v_ngen_2406_);
lean_ctor_set(v_reuseFailAlloc_2505_, 3, v_auxDeclNGen_2407_);
lean_ctor_set(v_reuseFailAlloc_2505_, 4, v_traceState_2408_);
lean_ctor_set(v_reuseFailAlloc_2505_, 5, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2505_, 6, v_recordedDeps_2409_);
lean_ctor_set(v_reuseFailAlloc_2505_, 7, v_messages_2410_);
lean_ctor_set(v_reuseFailAlloc_2505_, 8, v_infoState_2411_);
lean_ctor_set(v_reuseFailAlloc_2505_, 9, v_snapshotTasks_2412_);
v___x_2418_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v_mctx_2421_; lean_object* v_zetaDeltaFVarIds_2422_; lean_object* v_postponed_2423_; lean_object* v_diag_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2503_; 
v___x_2419_ = lean_st_ref_put(v_a_2341_, v___x_2418_);
v___x_2420_ = lean_st_ref_take(v_a_2339_);
v_mctx_2421_ = lean_ctor_get(v___x_2420_, 0);
v_zetaDeltaFVarIds_2422_ = lean_ctor_get(v___x_2420_, 2);
v_postponed_2423_ = lean_ctor_get(v___x_2420_, 3);
v_diag_2424_ = lean_ctor_get(v___x_2420_, 4);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; 
v_unused_2504_ = lean_ctor_get(v___x_2420_, 1);
lean_dec(v_unused_2504_);
v___x_2426_ = v___x_2420_;
v_isShared_2427_ = v_isSharedCheck_2503_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_diag_2424_);
lean_inc(v_postponed_2423_);
lean_inc(v_zetaDeltaFVarIds_2422_);
lean_inc(v_mctx_2421_);
lean_dec(v___x_2420_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2503_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v___x_2399_);
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_mctx_2421_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v_zetaDeltaFVarIds_2422_);
lean_ctor_set(v_reuseFailAlloc_2502_, 3, v_postponed_2423_);
lean_ctor_set(v_reuseFailAlloc_2502_, 4, v_diag_2424_);
v___x_2429_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v_env_2432_; lean_object* v_nextMacroScope_2433_; lean_object* v_ngen_2434_; lean_object* v_auxDeclNGen_2435_; lean_object* v_traceState_2436_; lean_object* v_recordedDeps_2437_; lean_object* v_messages_2438_; lean_object* v_infoState_2439_; lean_object* v_snapshotTasks_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2500_; 
v___x_2430_ = lean_st_ref_put(v_a_2339_, v___x_2429_);
v___x_2431_ = lean_st_ref_take(v_a_2341_);
v_env_2432_ = lean_ctor_get(v___x_2431_, 0);
v_nextMacroScope_2433_ = lean_ctor_get(v___x_2431_, 1);
v_ngen_2434_ = lean_ctor_get(v___x_2431_, 2);
v_auxDeclNGen_2435_ = lean_ctor_get(v___x_2431_, 3);
v_traceState_2436_ = lean_ctor_get(v___x_2431_, 4);
v_recordedDeps_2437_ = lean_ctor_get(v___x_2431_, 6);
v_messages_2438_ = lean_ctor_get(v___x_2431_, 7);
v_infoState_2439_ = lean_ctor_get(v___x_2431_, 8);
v_snapshotTasks_2440_ = lean_ctor_get(v___x_2431_, 9);
v_isSharedCheck_2500_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v___x_2431_, 5);
lean_dec(v_unused_2501_);
v___x_2442_ = v___x_2431_;
v_isShared_2443_ = v_isSharedCheck_2500_;
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
v_isShared_2443_ = v_isSharedCheck_2500_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_inc(v_declName_2336_);
v___x_2444_ = l_Lean_Meta_addToCompletionBlackList(v_env_2432_, v_declName_2336_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 5, v___x_2387_);
lean_ctor_set(v___x_2442_, 0, v___x_2444_);
v___x_2446_ = v___x_2442_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_nextMacroScope_2433_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_ngen_2434_);
lean_ctor_set(v_reuseFailAlloc_2499_, 3, v_auxDeclNGen_2435_);
lean_ctor_set(v_reuseFailAlloc_2499_, 4, v_traceState_2436_);
lean_ctor_set(v_reuseFailAlloc_2499_, 5, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2499_, 6, v_recordedDeps_2437_);
lean_ctor_set(v_reuseFailAlloc_2499_, 7, v_messages_2438_);
lean_ctor_set(v_reuseFailAlloc_2499_, 8, v_infoState_2439_);
lean_ctor_set(v_reuseFailAlloc_2499_, 9, v_snapshotTasks_2440_);
v___x_2446_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v_mctx_2449_; lean_object* v_zetaDeltaFVarIds_2450_; lean_object* v_postponed_2451_; lean_object* v_diag_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2497_; 
v___x_2447_ = lean_st_ref_put(v_a_2341_, v___x_2446_);
v___x_2448_ = lean_st_ref_take(v_a_2339_);
v_mctx_2449_ = lean_ctor_get(v___x_2448_, 0);
v_zetaDeltaFVarIds_2450_ = lean_ctor_get(v___x_2448_, 2);
v_postponed_2451_ = lean_ctor_get(v___x_2448_, 3);
v_diag_2452_ = lean_ctor_get(v___x_2448_, 4);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2497_ == 0)
{
lean_object* v_unused_2498_; 
v_unused_2498_ = lean_ctor_get(v___x_2448_, 1);
lean_dec(v_unused_2498_);
v___x_2454_ = v___x_2448_;
v_isShared_2455_ = v_isSharedCheck_2497_;
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
v_isShared_2455_ = v_isSharedCheck_2497_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 1, v___x_2399_);
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_mctx_2449_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2496_, 2, v_zetaDeltaFVarIds_2450_);
lean_ctor_set(v_reuseFailAlloc_2496_, 3, v_postponed_2451_);
lean_ctor_set(v_reuseFailAlloc_2496_, 4, v_diag_2452_);
v___x_2457_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_env_2460_; lean_object* v_nextMacroScope_2461_; lean_object* v_ngen_2462_; lean_object* v_auxDeclNGen_2463_; lean_object* v_traceState_2464_; lean_object* v_recordedDeps_2465_; lean_object* v_messages_2466_; lean_object* v_infoState_2467_; lean_object* v_snapshotTasks_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2494_; 
v___x_2458_ = lean_st_ref_put(v_a_2339_, v___x_2457_);
v___x_2459_ = lean_st_ref_take(v_a_2341_);
v_env_2460_ = lean_ctor_get(v___x_2459_, 0);
v_nextMacroScope_2461_ = lean_ctor_get(v___x_2459_, 1);
v_ngen_2462_ = lean_ctor_get(v___x_2459_, 2);
v_auxDeclNGen_2463_ = lean_ctor_get(v___x_2459_, 3);
v_traceState_2464_ = lean_ctor_get(v___x_2459_, 4);
v_recordedDeps_2465_ = lean_ctor_get(v___x_2459_, 6);
v_messages_2466_ = lean_ctor_get(v___x_2459_, 7);
v_infoState_2467_ = lean_ctor_get(v___x_2459_, 8);
v_snapshotTasks_2468_ = lean_ctor_get(v___x_2459_, 9);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2494_ == 0)
{
lean_object* v_unused_2495_; 
v_unused_2495_ = lean_ctor_get(v___x_2459_, 5);
lean_dec(v_unused_2495_);
v___x_2470_ = v___x_2459_;
v_isShared_2471_ = v_isSharedCheck_2494_;
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
v_isShared_2471_ = v_isSharedCheck_2494_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_inc(v_declName_2336_);
v___x_2472_ = l_Lean_addProtected(v_env_2460_, v_declName_2336_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 5, v___x_2387_);
lean_ctor_set(v___x_2470_, 0, v___x_2472_);
v___x_2474_ = v___x_2470_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_nextMacroScope_2461_);
lean_ctor_set(v_reuseFailAlloc_2493_, 2, v_ngen_2462_);
lean_ctor_set(v_reuseFailAlloc_2493_, 3, v_auxDeclNGen_2463_);
lean_ctor_set(v_reuseFailAlloc_2493_, 4, v_traceState_2464_);
lean_ctor_set(v_reuseFailAlloc_2493_, 5, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2493_, 6, v_recordedDeps_2465_);
lean_ctor_set(v_reuseFailAlloc_2493_, 7, v_messages_2466_);
lean_ctor_set(v_reuseFailAlloc_2493_, 8, v_infoState_2467_);
lean_ctor_set(v_reuseFailAlloc_2493_, 9, v_snapshotTasks_2468_);
v___x_2474_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v_mctx_2477_; lean_object* v_zetaDeltaFVarIds_2478_; lean_object* v_postponed_2479_; lean_object* v_diag_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2491_; 
v___x_2475_ = lean_st_ref_put(v_a_2341_, v___x_2474_);
v___x_2476_ = lean_st_ref_take(v_a_2339_);
v_mctx_2477_ = lean_ctor_get(v___x_2476_, 0);
v_zetaDeltaFVarIds_2478_ = lean_ctor_get(v___x_2476_, 2);
v_postponed_2479_ = lean_ctor_get(v___x_2476_, 3);
v_diag_2480_ = lean_ctor_get(v___x_2476_, 4);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v___x_2476_, 1);
lean_dec(v_unused_2492_);
v___x_2482_ = v___x_2476_;
v_isShared_2483_ = v_isSharedCheck_2491_;
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
v_isShared_2483_ = v_isSharedCheck_2491_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
lean_ctor_set(v___x_2482_, 1, v___x_2399_);
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_mctx_2477_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_zetaDeltaFVarIds_2478_);
lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_postponed_2479_);
lean_ctor_set(v_reuseFailAlloc_2490_, 4, v_diag_2480_);
v___x_2485_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2486_ = lean_st_ref_put(v_a_2339_, v___x_2485_);
v___x_2487_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2336_);
v___x_2488_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2487_, v_declName_2336_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v___x_2489_; 
lean_dec_ref_known(v___x_2488_, 1);
v___x_2489_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2336_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2489_;
}
else
{
lean_dec(v_declName_2336_);
return v___x_2488_;
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
lean_dec(v_declName_2336_);
return v___x_2372_;
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_levelParams_2353_);
lean_dec(v_declName_2336_);
v_a_2516_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2366_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2366_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
lean_dec(v___x_2356_);
lean_dec_ref(v_type_2354_);
lean_dec(v_levelParams_2353_);
lean_dec(v_name_2352_);
lean_dec(v___x_2349_);
lean_del_object(v___x_2347_);
lean_dec_ref(v_val_2345_);
lean_dec(v_indName_2337_);
lean_dec(v_declName_2336_);
v___x_2525_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2526_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2525_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2526_;
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v___x_2349_);
lean_del_object(v___x_2347_);
lean_dec_ref(v_val_2345_);
lean_dec(v_indName_2337_);
lean_dec(v_declName_2336_);
v_a_2527_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2350_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2350_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
else
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
lean_dec(v_a_2344_);
lean_dec(v_indName_2337_);
lean_dec(v_declName_2336_);
v___x_2536_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2537_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2536_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2537_;
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_dec(v_indName_2337_);
lean_dec(v_declName_2336_);
v_a_2538_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2343_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2343_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2546_, lean_object* v_indName_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2546_, v_indName_2547_, v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2554_, lean_object* v_name_2555_, lean_object* v_type_2556_, lean_object* v_k_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2555_, v_type_2556_, v_k_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2564_, lean_object* v_name_2565_, lean_object* v_type_2566_, lean_object* v_k_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_){
_start:
{
lean_object* v_res_2573_; 
v_res_2573_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2564_, v_name_2565_, v_type_2566_, v_k_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
return v_res_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2574_, lean_object* v_params_2575_, lean_object* v_alts_2576_, lean_object* v___x_2577_, lean_object* v_ism2_2578_, lean_object* v_motive_2579_, lean_object* v_val_2580_, lean_object* v_indName_2581_, lean_object* v___x_2582_, lean_object* v___x_2583_, lean_object* v___x_2584_, lean_object* v_as_2585_, size_t v_sz_2586_, size_t v_i_2587_, lean_object* v_bs_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2574_, v_params_2575_, v_alts_2576_, v___x_2577_, v_ism2_2578_, v_motive_2579_, v_val_2580_, v_indName_2581_, v___x_2582_, v___x_2583_, v___x_2584_, v_sz_2586_, v_i_2587_, v_bs_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2595_ = _args[0];
lean_object* v_params_2596_ = _args[1];
lean_object* v_alts_2597_ = _args[2];
lean_object* v___x_2598_ = _args[3];
lean_object* v_ism2_2599_ = _args[4];
lean_object* v_motive_2600_ = _args[5];
lean_object* v_val_2601_ = _args[6];
lean_object* v_indName_2602_ = _args[7];
lean_object* v___x_2603_ = _args[8];
lean_object* v___x_2604_ = _args[9];
lean_object* v___x_2605_ = _args[10];
lean_object* v_as_2606_ = _args[11];
lean_object* v_sz_2607_ = _args[12];
lean_object* v_i_2608_ = _args[13];
lean_object* v_bs_2609_ = _args[14];
lean_object* v___y_2610_ = _args[15];
lean_object* v___y_2611_ = _args[16];
lean_object* v___y_2612_ = _args[17];
lean_object* v___y_2613_ = _args[18];
lean_object* v___y_2614_ = _args[19];
_start:
{
size_t v_sz_boxed_2615_; size_t v_i_boxed_2616_; lean_object* v_res_2617_; 
v_sz_boxed_2615_ = lean_unbox_usize(v_sz_2607_);
lean_dec(v_sz_2607_);
v_i_boxed_2616_ = lean_unbox_usize(v_i_2608_);
lean_dec(v_i_2608_);
v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2595_, v_params_2596_, v_alts_2597_, v___x_2598_, v_ism2_2599_, v_motive_2600_, v_val_2601_, v_indName_2602_, v___x_2603_, v___x_2604_, v___x_2605_, v_as_2606_, v_sz_boxed_2615_, v_i_boxed_2616_, v_bs_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v_as_2606_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2618_, lean_object* v_params_2619_, lean_object* v___x_2620_, lean_object* v_motive_2621_, lean_object* v_as_2622_, size_t v_sz_2623_, size_t v_i_2624_, lean_object* v_bs_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2618_, v_params_2619_, v___x_2620_, v_motive_2621_, v_sz_2623_, v_i_2624_, v_bs_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2632_, lean_object* v_params_2633_, lean_object* v___x_2634_, lean_object* v_motive_2635_, lean_object* v_as_2636_, lean_object* v_sz_2637_, lean_object* v_i_2638_, lean_object* v_bs_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
size_t v_sz_boxed_2645_; size_t v_i_boxed_2646_; lean_object* v_res_2647_; 
v_sz_boxed_2645_ = lean_unbox_usize(v_sz_2637_);
lean_dec(v_sz_2637_);
v_i_boxed_2646_ = lean_unbox_usize(v_i_2638_);
lean_dec(v_i_2638_);
v_res_2647_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2632_, v_params_2633_, v___x_2634_, v_motive_2635_, v_as_2636_, v_sz_boxed_2645_, v_i_boxed_2646_, v_bs_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
lean_dec(v___y_2641_);
lean_dec_ref(v___y_2640_);
lean_dec_ref(v_as_2636_);
lean_dec_ref(v_params_2633_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2648_, uint8_t v_s_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2648_, v_s_2649_, v___y_2651_, v___y_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2656_, lean_object* v_s_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
uint8_t v_s_boxed_2663_; lean_object* v_res_2664_; 
v_s_boxed_2663_ = lean_unbox(v_s_2657_);
v_res_2664_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2656_, v_s_boxed_2663_, v___y_2658_, v___y_2659_, v___y_2660_, v___y_2661_);
lean_dec(v___y_2661_);
lean_dec_ref(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2665_, lean_object* v_constName_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2673_, lean_object* v_constName_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2673_, v_constName_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2681_, lean_object* v_attrName_2682_, lean_object* v_declName_2683_, lean_object* v_asyncPrefix_x3f_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2682_, v_declName_2683_, v_asyncPrefix_x3f_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2691_, lean_object* v_attrName_2692_, lean_object* v_declName_2693_, lean_object* v_asyncPrefix_x3f_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2691_, v_attrName_2692_, v_declName_2693_, v_asyncPrefix_x3f_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2701_, lean_object* v_attrName_2702_, lean_object* v_declName_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2702_, v_declName_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2710_, lean_object* v_attrName_2711_, lean_object* v_declName_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2710_, v_attrName_2711_, v_declName_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
lean_dec(v___y_2716_);
lean_dec_ref(v___y_2715_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2719_, lean_object* v_ref_2720_, lean_object* v_constName_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2720_, v_constName_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2728_, lean_object* v_ref_2729_, lean_object* v_constName_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2728_, v_ref_2729_, v_constName_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v_ref_2729_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2737_, lean_object* v_msg_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v___x_2744_; 
v___x_2744_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2745_, lean_object* v_msg_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2745_, v_msg_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
lean_dec(v___y_2748_);
lean_dec_ref(v___y_2747_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2753_, lean_object* v_ref_2754_, lean_object* v_msg_2755_, lean_object* v_declHint_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2754_, v_msg_2755_, v_declHint_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2763_, lean_object* v_ref_2764_, lean_object* v_msg_2765_, lean_object* v_declHint_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2763_, v_ref_2764_, v_msg_2765_, v_declHint_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v_ref_2764_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2773_, lean_object* v_declHint_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2773_, v_declHint_2774_, v___y_2778_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2781_, lean_object* v_declHint_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2781_, v_declHint_2782_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
lean_dec(v___y_2786_);
lean_dec_ref(v___y_2785_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2789_, lean_object* v_ref_2790_, lean_object* v_msg_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2790_, v_msg_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2798_, lean_object* v_ref_2799_, lean_object* v_msg_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2798_, v_ref_2799_, v_msg_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v_ref_2799_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2807_, lean_object* v___y_2808_){
_start:
{
uint8_t v___x_2810_; 
v___x_2810_ = l_Lean_Expr_hasMVar(v_e_2807_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
v___x_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2811_, 0, v_e_2807_);
return v___x_2811_;
}
else
{
lean_object* v___x_2812_; lean_object* v_mctx_2813_; lean_object* v___x_2814_; lean_object* v_fst_2815_; lean_object* v_snd_2816_; lean_object* v___x_2817_; lean_object* v_cache_2818_; lean_object* v_zetaDeltaFVarIds_2819_; lean_object* v_postponed_2820_; lean_object* v_diag_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2830_; 
v___x_2812_ = lean_st_ref_get(v___y_2808_);
v_mctx_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc_ref(v_mctx_2813_);
lean_dec(v___x_2812_);
v___x_2814_ = l_Lean_instantiateMVarsCore(v_mctx_2813_, v_e_2807_);
v_fst_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_fst_2815_);
v_snd_2816_ = lean_ctor_get(v___x_2814_, 1);
lean_inc(v_snd_2816_);
lean_dec_ref(v___x_2814_);
v___x_2817_ = lean_st_ref_take(v___y_2808_);
v_cache_2818_ = lean_ctor_get(v___x_2817_, 1);
v_zetaDeltaFVarIds_2819_ = lean_ctor_get(v___x_2817_, 2);
v_postponed_2820_ = lean_ctor_get(v___x_2817_, 3);
v_diag_2821_ = lean_ctor_get(v___x_2817_, 4);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; 
v_unused_2831_ = lean_ctor_get(v___x_2817_, 0);
lean_dec(v_unused_2831_);
v___x_2823_ = v___x_2817_;
v_isShared_2824_ = v_isSharedCheck_2830_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_diag_2821_);
lean_inc(v_postponed_2820_);
lean_inc(v_zetaDeltaFVarIds_2819_);
lean_inc(v_cache_2818_);
lean_dec(v___x_2817_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2830_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v_snd_2816_);
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_snd_2816_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_cache_2818_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_zetaDeltaFVarIds_2819_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_postponed_2820_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v_diag_2821_);
v___x_2826_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_st_ref_put(v___y_2808_, v___x_2826_);
v___x_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2828_, 0, v_fst_2815_);
return v___x_2828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2832_, v___y_2833_);
lean_dec(v___y_2833_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2836_, v___y_2838_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
lean_dec(v___y_2847_);
lean_dec_ref(v___y_2846_);
lean_dec(v___y_2845_);
lean_dec_ref(v___y_2844_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2850_, lean_object* v_info_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_){
_start:
{
lean_object* v___x_2855_; lean_object* v_env_2856_; lean_object* v_nextMacroScope_2857_; lean_object* v_ngen_2858_; lean_object* v_auxDeclNGen_2859_; lean_object* v_traceState_2860_; lean_object* v_recordedDeps_2861_; lean_object* v_messages_2862_; lean_object* v_infoState_2863_; lean_object* v_snapshotTasks_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2891_; 
v___x_2855_ = lean_st_ref_take(v___y_2853_);
v_env_2856_ = lean_ctor_get(v___x_2855_, 0);
v_nextMacroScope_2857_ = lean_ctor_get(v___x_2855_, 1);
v_ngen_2858_ = lean_ctor_get(v___x_2855_, 2);
v_auxDeclNGen_2859_ = lean_ctor_get(v___x_2855_, 3);
v_traceState_2860_ = lean_ctor_get(v___x_2855_, 4);
v_recordedDeps_2861_ = lean_ctor_get(v___x_2855_, 6);
v_messages_2862_ = lean_ctor_get(v___x_2855_, 7);
v_infoState_2863_ = lean_ctor_get(v___x_2855_, 8);
v_snapshotTasks_2864_ = lean_ctor_get(v___x_2855_, 9);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; 
v_unused_2892_ = lean_ctor_get(v___x_2855_, 5);
lean_dec(v_unused_2892_);
v___x_2866_ = v___x_2855_;
v_isShared_2867_ = v_isSharedCheck_2891_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_snapshotTasks_2864_);
lean_inc(v_infoState_2863_);
lean_inc(v_messages_2862_);
lean_inc(v_recordedDeps_2861_);
lean_inc(v_traceState_2860_);
lean_inc(v_auxDeclNGen_2859_);
lean_inc(v_ngen_2858_);
lean_inc(v_nextMacroScope_2857_);
lean_inc(v_env_2856_);
lean_dec(v___x_2855_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2891_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
v___x_2868_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2856_, v_matcherName_2850_, v_info_2851_);
v___x_2869_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 5, v___x_2869_);
lean_ctor_set(v___x_2866_, 0, v___x_2868_);
v___x_2871_ = v___x_2866_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2868_);
lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_nextMacroScope_2857_);
lean_ctor_set(v_reuseFailAlloc_2890_, 2, v_ngen_2858_);
lean_ctor_set(v_reuseFailAlloc_2890_, 3, v_auxDeclNGen_2859_);
lean_ctor_set(v_reuseFailAlloc_2890_, 4, v_traceState_2860_);
lean_ctor_set(v_reuseFailAlloc_2890_, 5, v___x_2869_);
lean_ctor_set(v_reuseFailAlloc_2890_, 6, v_recordedDeps_2861_);
lean_ctor_set(v_reuseFailAlloc_2890_, 7, v_messages_2862_);
lean_ctor_set(v_reuseFailAlloc_2890_, 8, v_infoState_2863_);
lean_ctor_set(v_reuseFailAlloc_2890_, 9, v_snapshotTasks_2864_);
v___x_2871_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v_mctx_2874_; lean_object* v_zetaDeltaFVarIds_2875_; lean_object* v_postponed_2876_; lean_object* v_diag_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2888_; 
v___x_2872_ = lean_st_ref_put(v___y_2853_, v___x_2871_);
v___x_2873_ = lean_st_ref_take(v___y_2852_);
v_mctx_2874_ = lean_ctor_get(v___x_2873_, 0);
v_zetaDeltaFVarIds_2875_ = lean_ctor_get(v___x_2873_, 2);
v_postponed_2876_ = lean_ctor_get(v___x_2873_, 3);
v_diag_2877_ = lean_ctor_get(v___x_2873_, 4);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2888_ == 0)
{
lean_object* v_unused_2889_; 
v_unused_2889_ = lean_ctor_get(v___x_2873_, 1);
lean_dec(v_unused_2889_);
v___x_2879_ = v___x_2873_;
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_diag_2877_);
lean_inc(v_postponed_2876_);
lean_inc(v_zetaDeltaFVarIds_2875_);
lean_inc(v_mctx_2874_);
lean_dec(v___x_2873_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2888_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2881_ = lean_box(0);
v___x_2882_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 1, v___x_2882_);
v___x_2884_ = v___x_2879_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_mctx_2874_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2887_, 2, v_zetaDeltaFVarIds_2875_);
lean_ctor_set(v_reuseFailAlloc_2887_, 3, v_postponed_2876_);
lean_ctor_set(v_reuseFailAlloc_2887_, 4, v_diag_2877_);
v___x_2884_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_st_ref_put(v___y_2852_, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2881_);
return v___x_2886_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2893_, lean_object* v_info_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2893_, v_info_2894_, v___y_2895_, v___y_2896_);
lean_dec(v___y_2896_);
lean_dec(v___y_2895_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2899_, lean_object* v_info_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2899_, v_info_2900_, v___y_2902_, v___y_2904_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2907_, lean_object* v_info_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2907_, v_info_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2915_, lean_object* v___x_2916_, lean_object* v_newEqs1_2917_, uint8_t v___x_2918_, uint8_t v___x_2919_, uint8_t v___x_2920_, lean_object* v_ism1_x27_2921_, lean_object* v_ism2_x27_2922_, lean_object* v_newRefls1_2923_, lean_object* v_newEqs2_2924_, lean_object* v_newRefls2_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; 
v___x_2931_ = l_Lean_mkAppN(v_motive_2915_, v___x_2916_);
v___x_2932_ = l_Array_append___redArg(v_newEqs1_2917_, v_newEqs2_2924_);
v___x_2933_ = l_Lean_Meta_mkForallFVars(v___x_2932_, v___x_2931_, v___x_2918_, v___x_2919_, v___x_2919_, v___x_2920_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec_ref(v___x_2932_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
v___x_2935_ = l_Array_append___redArg(v_ism1_x27_2921_, v_ism2_x27_2922_);
v___x_2936_ = l_Lean_Meta_mkLambdaFVars(v___x_2935_, v_a_2934_, v___x_2918_, v___x_2919_, v___x_2918_, v___x_2919_, v___x_2920_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec_ref(v___x_2935_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2946_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2946_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2946_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2944_; 
v___x_2941_ = l_Array_append___redArg(v_newRefls1_2923_, v_newRefls2_2925_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v_a_2937_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
if (v_isShared_2940_ == 0)
{
lean_ctor_set(v___x_2939_, 0, v___x_2942_);
v___x_2944_ = v___x_2939_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec_ref(v_newRefls1_2923_);
v_a_2947_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2936_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2936_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec_ref(v_newRefls1_2923_);
lean_dec_ref(v_ism1_x27_2921_);
v_a_2955_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2933_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2933_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2963_, lean_object* v___x_2964_, lean_object* v_newEqs1_2965_, lean_object* v___x_2966_, lean_object* v___x_2967_, lean_object* v___x_2968_, lean_object* v_ism1_x27_2969_, lean_object* v_ism2_x27_2970_, lean_object* v_newRefls1_2971_, lean_object* v_newEqs2_2972_, lean_object* v_newRefls2_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
uint8_t v___x_14986__boxed_2979_; uint8_t v___x_14987__boxed_2980_; uint8_t v___x_14988__boxed_2981_; lean_object* v_res_2982_; 
v___x_14986__boxed_2979_ = lean_unbox(v___x_2966_);
v___x_14987__boxed_2980_ = lean_unbox(v___x_2967_);
v___x_14988__boxed_2981_ = lean_unbox(v___x_2968_);
v_res_2982_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2963_, v___x_2964_, v_newEqs1_2965_, v___x_14986__boxed_2979_, v___x_14987__boxed_2980_, v___x_14988__boxed_2981_, v_ism1_x27_2969_, v_ism2_x27_2970_, v_newRefls1_2971_, v_newEqs2_2972_, v_newRefls2_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec_ref(v_newRefls2_2973_);
lean_dec_ref(v_newEqs2_2972_);
lean_dec_ref(v_ism2_x27_2970_);
lean_dec_ref(v___x_2964_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2983_, lean_object* v___x_2984_, uint8_t v___x_2985_, uint8_t v___x_2986_, uint8_t v___x_2987_, lean_object* v_ism1_x27_2988_, lean_object* v_ism2_x27_2989_, lean_object* v_is_2990_, lean_object* v___x_2991_, lean_object* v_newEqs1_2992_, lean_object* v_newRefls1_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___f_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_2999_ = lean_box(v___x_2985_);
v___x_3000_ = lean_box(v___x_2986_);
v___x_3001_ = lean_box(v___x_2987_);
lean_inc_ref(v_ism2_x27_2989_);
v___f_3002_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3002_, 0, v_motive_2983_);
lean_closure_set(v___f_3002_, 1, v___x_2984_);
lean_closure_set(v___f_3002_, 2, v_newEqs1_2992_);
lean_closure_set(v___f_3002_, 3, v___x_2999_);
lean_closure_set(v___f_3002_, 4, v___x_3000_);
lean_closure_set(v___f_3002_, 5, v___x_3001_);
lean_closure_set(v___f_3002_, 6, v_ism1_x27_2988_);
lean_closure_set(v___f_3002_, 7, v_ism2_x27_2989_);
lean_closure_set(v___f_3002_, 8, v_newRefls1_2993_);
v___x_3003_ = lean_array_push(v_is_2990_, v___x_2991_);
v___x_3004_ = l_Lean_Meta_withNewEqs___redArg(v___x_3003_, v_ism2_x27_2989_, v___f_3002_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_3005_, lean_object* v___x_3006_, lean_object* v___x_3007_, lean_object* v___x_3008_, lean_object* v___x_3009_, lean_object* v_ism1_x27_3010_, lean_object* v_ism2_x27_3011_, lean_object* v_is_3012_, lean_object* v___x_3013_, lean_object* v_newEqs1_3014_, lean_object* v_newRefls1_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
uint8_t v___x_15077__boxed_3021_; uint8_t v___x_15078__boxed_3022_; uint8_t v___x_15079__boxed_3023_; lean_object* v_res_3024_; 
v___x_15077__boxed_3021_ = lean_unbox(v___x_3007_);
v___x_15078__boxed_3022_ = lean_unbox(v___x_3008_);
v___x_15079__boxed_3023_ = lean_unbox(v___x_3009_);
v_res_3024_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_3005_, v___x_3006_, v___x_15077__boxed_3021_, v___x_15078__boxed_3022_, v___x_15079__boxed_3023_, v_ism1_x27_3010_, v_ism2_x27_3011_, v_is_3012_, v___x_3013_, v_newEqs1_3014_, v_newRefls1_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_3025_, uint8_t v___x_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Lean_addDecl(v___x_3025_, v___x_3026_, v___y_3029_, v___y_3030_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3033_, lean_object* v___x_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
uint8_t v___x_15119__boxed_3040_; lean_object* v_res_3041_; 
v___x_15119__boxed_3040_ = lean_unbox(v___x_3034_);
v_res_3041_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3033_, v___x_15119__boxed_3040_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v_res_3041_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3044_ = l_Lean_stringToMessageData(v___x_3043_);
return v___x_3044_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3047_ = l_Lean_stringToMessageData(v___x_3046_);
return v___x_3047_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = lean_box(0);
v___x_3054_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3055_ = l_Lean_mkConst(v___x_3054_, v___x_3053_);
return v___x_3055_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3058_ = l_Lean_stringToMessageData(v___x_3057_);
return v___x_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3059_, lean_object* v_a_3060_, lean_object* v___x_3061_, lean_object* v_zs1_3062_, lean_object* v_snd_3063_, uint8_t v___x_3064_, uint8_t v___x_3065_, uint8_t v___x_3066_, lean_object* v_alts_3067_, lean_object* v_zs2_3068_, lean_object* v___ctorRet2_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3075_ = lean_array_get_borrowed(v___x_3059_, v_a_3060_, v___x_3061_);
lean_inc_ref(v_zs1_3062_);
v___x_3076_ = l_Array_append___redArg(v_zs1_3062_, v_zs2_3068_);
lean_inc(v___x_3075_);
v___x_3077_ = l_Lean_Meta_instantiateForall(v___x_3075_, v___x_3076_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___x_3079_ = lean_box(0);
v___x_3080_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3078_, v___x_3079_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_a_3081_);
lean_dec_ref_known(v___x_3080_, 1);
v___x_3082_ = l_Lean_Expr_mvarId_x21(v_a_3081_);
v___x_3083_ = lean_array_get_size(v_snd_3063_);
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_box(0);
lean_inc_ref(v___y_3072_);
v___x_3086_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3083_, v___x_3082_, v___x_3084_, v___x_3085_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
if (lean_obj_tag(v_a_3087_) == 1)
{
lean_object* v_val_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3135_; 
v_val_3088_ = lean_ctor_get(v_a_3087_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_a_3087_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3090_ = v_a_3087_;
v_isShared_3091_ = v_isSharedCheck_3135_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_val_3088_);
lean_dec(v_a_3087_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3135_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v_fst_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3133_; 
v_fst_3092_ = lean_ctor_get(v_val_3088_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v_val_3088_);
if (v_isSharedCheck_3133_ == 0)
{
lean_object* v_unused_3134_; 
v_unused_3134_ = lean_ctor_get(v_val_3088_, 1);
lean_dec(v_unused_3134_);
v___x_3094_ = v_val_3088_;
v_isShared_3095_ = v_isSharedCheck_3133_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_fst_3092_);
lean_dec(v_val_3088_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3133_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___y_3097_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v___x_3125_ = lean_array_get_borrowed(v___x_3059_, v_alts_3067_, v___x_3061_);
v___x_3126_ = lean_array_get_size(v_zs1_3062_);
lean_dec_ref(v_zs1_3062_);
v___x_3127_ = lean_unsigned_to_nat(0u);
v___x_3128_ = lean_nat_dec_eq(v___x_3126_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_inc(v___x_3125_);
v___y_3097_ = v___x_3125_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3129_; uint8_t v___x_3130_; 
v___x_3129_ = lean_array_get_size(v_zs2_3068_);
v___x_3130_ = lean_nat_dec_eq(v___x_3129_, v___x_3127_);
if (v___x_3130_ == 0)
{
lean_inc(v___x_3125_);
v___y_3097_ = v___x_3125_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3125_);
v___x_3132_ = l_Lean_Expr_app___override(v___x_3125_, v___x_3131_);
v___y_3097_ = v___x_3132_;
goto v___jp_3096_;
}
}
v___jp_3096_:
{
uint8_t v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = 0;
v___x_3099_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3099_, 0, v___x_3098_);
lean_ctor_set_uint8(v___x_3099_, 1, v___x_3064_);
lean_ctor_set_uint8(v___x_3099_, 2, v___x_3065_);
lean_ctor_set_uint8(v___x_3099_, 3, v___x_3064_);
lean_inc_ref(v___y_3097_);
lean_inc(v_fst_3092_);
v___x_3100_ = l_Lean_MVarId_apply(v_fst_3092_, v___y_3097_, v___x_3099_, v___x_3085_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_a_3101_; 
v_a_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_a_3101_);
lean_dec_ref_known(v___x_3100_, 1);
if (lean_obj_tag(v_a_3101_) == 0)
{
lean_object* v___x_3102_; 
lean_dec_ref(v___y_3097_);
lean_del_object(v___x_3094_);
lean_dec(v_fst_3092_);
lean_del_object(v___x_3090_);
v___x_3102_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3081_, v___y_3071_);
if (lean_obj_tag(v___x_3102_) == 0)
{
lean_object* v_a_3103_; lean_object* v___x_3104_; 
v_a_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_a_3103_);
lean_dec_ref_known(v___x_3102_, 1);
v___x_3104_ = l_Lean_Meta_mkLambdaFVars(v___x_3076_, v_a_3103_, v___x_3065_, v___x_3064_, v___x_3065_, v___x_3064_, v___x_3066_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec_ref(v___x_3076_);
return v___x_3104_;
}
else
{
lean_dec_ref(v___x_3076_);
return v___x_3102_;
}
}
else
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3108_; 
lean_dec(v_a_3101_);
lean_dec(v_a_3081_);
lean_dec_ref(v___x_3076_);
v___x_3105_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3106_ = l_Lean_MessageData_ofExpr(v___y_3097_);
if (v_isShared_3095_ == 0)
{
lean_ctor_set_tag(v___x_3094_, 7);
lean_ctor_set(v___x_3094_, 1, v___x_3106_);
lean_ctor_set(v___x_3094_, 0, v___x_3105_);
v___x_3108_ = v___x_3094_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3105_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3108_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v_fst_3092_);
v___x_3112_ = v___x_3090_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_fst_3092_);
v___x_3112_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3110_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3113_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
return v___x_3114_;
}
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
lean_dec_ref(v___y_3097_);
lean_del_object(v___x_3094_);
lean_dec(v_fst_3092_);
lean_del_object(v___x_3090_);
lean_dec(v_a_3081_);
lean_dec_ref(v___x_3076_);
v_a_3117_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v___x_3100_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3100_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; 
lean_dec(v_a_3087_);
lean_dec(v_a_3081_);
lean_dec_ref(v___x_3076_);
lean_dec_ref(v_zs1_3062_);
v___x_3136_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3137_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3136_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_);
return v___x_3137_;
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v_a_3081_);
lean_dec_ref(v___x_3076_);
lean_dec_ref(v_zs1_3062_);
v_a_3138_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3086_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3086_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_dec_ref(v___x_3076_);
lean_dec_ref(v_zs1_3062_);
return v___x_3080_;
}
}
else
{
lean_dec_ref(v___x_3076_);
lean_dec_ref(v_zs1_3062_);
return v___x_3077_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3146_, lean_object* v_a_3147_, lean_object* v___x_3148_, lean_object* v_zs1_3149_, lean_object* v_snd_3150_, lean_object* v___x_3151_, lean_object* v___x_3152_, lean_object* v___x_3153_, lean_object* v_alts_3154_, lean_object* v_zs2_3155_, lean_object* v___ctorRet2_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_){
_start:
{
uint8_t v___x_15179__boxed_3162_; uint8_t v___x_15180__boxed_3163_; uint8_t v___x_15181__boxed_3164_; lean_object* v_res_3165_; 
v___x_15179__boxed_3162_ = lean_unbox(v___x_3151_);
v___x_15180__boxed_3163_ = lean_unbox(v___x_3152_);
v___x_15181__boxed_3164_ = lean_unbox(v___x_3153_);
v_res_3165_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3146_, v_a_3147_, v___x_3148_, v_zs1_3149_, v_snd_3150_, v___x_15179__boxed_3162_, v___x_15180__boxed_3163_, v___x_15181__boxed_3164_, v_alts_3154_, v_zs2_3155_, v___ctorRet2_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec_ref(v___ctorRet2_3156_);
lean_dec_ref(v_zs2_3155_);
lean_dec_ref(v_alts_3154_);
lean_dec_ref(v_snd_3150_);
lean_dec(v___x_3148_);
lean_dec_ref(v_a_3147_);
lean_dec_ref(v___x_3146_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3166_, lean_object* v_a_3167_, lean_object* v___x_3168_, lean_object* v_snd_3169_, uint8_t v___x_3170_, uint8_t v___x_3171_, uint8_t v___x_3172_, lean_object* v_alts_3173_, lean_object* v_a_3174_, lean_object* v_zs1_3175_, lean_object* v___ctorRet1_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___f_3185_; lean_object* v___x_3186_; 
v___x_3182_ = lean_box(v___x_3170_);
v___x_3183_ = lean_box(v___x_3171_);
v___x_3184_ = lean_box(v___x_3172_);
v___f_3185_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3185_, 0, v___x_3166_);
lean_closure_set(v___f_3185_, 1, v_a_3167_);
lean_closure_set(v___f_3185_, 2, v___x_3168_);
lean_closure_set(v___f_3185_, 3, v_zs1_3175_);
lean_closure_set(v___f_3185_, 4, v_snd_3169_);
lean_closure_set(v___f_3185_, 5, v___x_3182_);
lean_closure_set(v___f_3185_, 6, v___x_3183_);
lean_closure_set(v___f_3185_, 7, v___x_3184_);
lean_closure_set(v___f_3185_, 8, v_alts_3173_);
v___x_3186_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3174_, v___f_3185_, v___x_3171_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
return v___x_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3187_, lean_object* v_a_3188_, lean_object* v___x_3189_, lean_object* v_snd_3190_, lean_object* v___x_3191_, lean_object* v___x_3192_, lean_object* v___x_3193_, lean_object* v_alts_3194_, lean_object* v_a_3195_, lean_object* v_zs1_3196_, lean_object* v___ctorRet1_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
uint8_t v___x_15378__boxed_3203_; uint8_t v___x_15379__boxed_3204_; uint8_t v___x_15380__boxed_3205_; lean_object* v_res_3206_; 
v___x_15378__boxed_3203_ = lean_unbox(v___x_3191_);
v___x_15379__boxed_3204_ = lean_unbox(v___x_3192_);
v___x_15380__boxed_3205_ = lean_unbox(v___x_3193_);
v_res_3206_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3187_, v_a_3188_, v___x_3189_, v_snd_3190_, v___x_15378__boxed_3203_, v___x_15379__boxed_3204_, v___x_15380__boxed_3205_, v_alts_3194_, v_a_3195_, v_zs1_3196_, v___ctorRet1_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
lean_dec_ref(v___ctorRet1_3197_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3207_, lean_object* v_params_3208_, lean_object* v_a_3209_, lean_object* v_snd_3210_, lean_object* v_alts_3211_, size_t v_sz_3212_, size_t v_i_3213_, lean_object* v_bs_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
uint8_t v___x_3220_; 
v___x_3220_ = lean_usize_dec_lt(v_i_3213_, v_sz_3212_);
if (v___x_3220_ == 0)
{
lean_object* v___x_3221_; 
lean_dec_ref(v_alts_3211_);
lean_dec_ref(v_snd_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_tail_3207_);
v___x_3221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3221_, 0, v_bs_3214_);
return v___x_3221_;
}
else
{
lean_object* v___x_3222_; uint8_t v___x_3223_; uint8_t v___x_3224_; lean_object* v_v_3225_; lean_object* v___x_3226_; lean_object* v_bs_x27_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3222_ = l_Lean_instInhabitedExpr;
v___x_3223_ = 0;
v___x_3224_ = 1;
v_v_3225_ = lean_array_uget(v_bs_3214_, v_i_3213_);
v___x_3226_ = lean_unsigned_to_nat(0u);
v_bs_x27_3227_ = lean_array_uset(v_bs_3214_, v_i_3213_, v___x_3226_);
v___x_3228_ = lean_usize_to_nat(v_i_3213_);
lean_inc(v_tail_3207_);
v___x_3229_ = l_Lean_mkConst(v_v_3225_, v_tail_3207_);
v___x_3230_ = l_Lean_mkAppN(v___x_3229_, v_params_3208_);
lean_inc(v___y_3218_);
lean_inc_ref(v___y_3217_);
lean_inc(v___y_3216_);
lean_inc_ref(v___y_3215_);
v___x_3231_ = lean_infer_type(v___x_3230_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___f_3236_; lean_object* v___x_3237_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc_n(v_a_3232_, 2);
lean_dec_ref_known(v___x_3231_, 1);
v___x_3233_ = lean_box(v___x_3220_);
v___x_3234_ = lean_box(v___x_3223_);
v___x_3235_ = lean_box(v___x_3224_);
lean_inc_ref(v_alts_3211_);
lean_inc_ref(v_snd_3210_);
lean_inc_ref(v_a_3209_);
v___f_3236_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3236_, 0, v___x_3222_);
lean_closure_set(v___f_3236_, 1, v_a_3209_);
lean_closure_set(v___f_3236_, 2, v___x_3228_);
lean_closure_set(v___f_3236_, 3, v_snd_3210_);
lean_closure_set(v___f_3236_, 4, v___x_3233_);
lean_closure_set(v___f_3236_, 5, v___x_3234_);
lean_closure_set(v___f_3236_, 6, v___x_3235_);
lean_closure_set(v___f_3236_, 7, v_alts_3211_);
lean_closure_set(v___f_3236_, 8, v_a_3232_);
v___x_3237_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3232_, v___f_3236_, v___x_3223_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; size_t v___x_3239_; size_t v___x_3240_; lean_object* v___x_3241_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref_known(v___x_3237_, 1);
v___x_3239_ = ((size_t)1ULL);
v___x_3240_ = lean_usize_add(v_i_3213_, v___x_3239_);
v___x_3241_ = lean_array_uset(v_bs_x27_3227_, v_i_3213_, v_a_3238_);
v_i_3213_ = v___x_3240_;
v_bs_3214_ = v___x_3241_;
goto _start;
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec_ref(v_bs_x27_3227_);
lean_dec_ref(v_alts_3211_);
lean_dec_ref(v_snd_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_tail_3207_);
v_a_3243_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3237_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3237_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v___x_3228_);
lean_dec_ref(v_bs_x27_3227_);
lean_dec_ref(v_alts_3211_);
lean_dec_ref(v_snd_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_tail_3207_);
v_a_3251_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3231_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3231_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3259_, lean_object* v_params_3260_, lean_object* v_a_3261_, lean_object* v_snd_3262_, lean_object* v_alts_3263_, lean_object* v_sz_3264_, lean_object* v_i_3265_, lean_object* v_bs_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
size_t v_sz_boxed_3272_; size_t v_i_boxed_3273_; lean_object* v_res_3274_; 
v_sz_boxed_3272_ = lean_unbox_usize(v_sz_3264_);
lean_dec(v_sz_3264_);
v_i_boxed_3273_ = lean_unbox_usize(v_i_3265_);
lean_dec(v_i_3265_);
v_res_3274_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3259_, v_params_3260_, v_a_3261_, v_snd_3262_, v_alts_3263_, v_sz_boxed_3272_, v_i_boxed_3273_, v_bs_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec_ref(v_params_3260_);
return v_res_3274_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = lean_box(0);
v___x_3276_ = lean_unsigned_to_nat(16u);
v___x_3277_ = lean_mk_array(v___x_3276_, v___x_3275_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3278_, lean_object* v___x_3279_, uint8_t v___x_3280_, uint8_t v___x_3281_, uint8_t v___x_3282_, lean_object* v_ism1_x27_3283_, lean_object* v_is_3284_, lean_object* v___x_3285_, lean_object* v___x_3286_, lean_object* v___x_3287_, lean_object* v___x_3288_, lean_object* v_params_3289_, lean_object* v___x_3290_, lean_object* v___x_3291_, lean_object* v_heq_3292_, lean_object* v_val_3293_, lean_object* v_tail_3294_, lean_object* v_alts_3295_, size_t v_sz_3296_, size_t v___x_3297_, lean_object* v___x_3298_, lean_object* v___x_3299_, lean_object* v_declName_3300_, lean_object* v_levelParams_3301_, lean_object* v_numIndices_3302_, lean_object* v___x_3303_, lean_object* v___x_3304_, lean_object* v_numParams_3305_, lean_object* v_snd_3306_, lean_object* v_ism2_x27_3307_, lean_object* v_x_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___f_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3314_ = lean_box(v___x_3280_);
v___x_3315_ = lean_box(v___x_3281_);
v___x_3316_ = lean_box(v___x_3282_);
lean_inc_ref(v___x_3285_);
lean_inc_ref_n(v_is_3284_, 2);
lean_inc_ref(v_ism1_x27_3283_);
lean_inc_ref(v_motive_3278_);
v___f_3317_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3317_, 0, v_motive_3278_);
lean_closure_set(v___f_3317_, 1, v___x_3279_);
lean_closure_set(v___f_3317_, 2, v___x_3314_);
lean_closure_set(v___f_3317_, 3, v___x_3315_);
lean_closure_set(v___f_3317_, 4, v___x_3316_);
lean_closure_set(v___f_3317_, 5, v_ism1_x27_3283_);
lean_closure_set(v___f_3317_, 6, v_ism2_x27_3307_);
lean_closure_set(v___f_3317_, 7, v_is_3284_);
lean_closure_set(v___f_3317_, 8, v___x_3285_);
lean_inc_ref(v___x_3286_);
v___x_3318_ = lean_array_push(v_is_3284_, v___x_3286_);
v___x_3319_ = l_Lean_Meta_withNewEqs___redArg(v___x_3318_, v_ism1_x27_3283_, v___f_3317_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v_a_3320_; lean_object* v_fst_3321_; lean_object* v_snd_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3423_; 
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_a_3320_);
lean_dec_ref_known(v___x_3319_, 1);
v_fst_3321_ = lean_ctor_get(v_a_3320_, 0);
v_snd_3322_ = lean_ctor_get(v_a_3320_, 1);
v_isSharedCheck_3423_ = !lean_is_exclusive(v_a_3320_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3324_ = v_a_3320_;
v_isShared_3325_ = v_isSharedCheck_3423_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_snd_3322_);
lean_inc(v_fst_3321_);
lean_dec(v_a_3320_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3423_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3326_ = l_Lean_mkConst(v___x_3287_, v___x_3288_);
v___x_3327_ = l_Lean_mkAppN(v___x_3326_, v_params_3289_);
v___x_3328_ = l_Lean_Expr_app___override(v___x_3327_, v_fst_3321_);
lean_inc_ref(v_is_3284_);
v___x_3329_ = l_Array_append___redArg(v_is_3284_, v___x_3290_);
v___x_3330_ = l_Array_append___redArg(v___x_3329_, v_is_3284_);
v___x_3331_ = l_Array_append___redArg(v___x_3330_, v___x_3291_);
v___x_3332_ = l_Lean_mkAppN(v___x_3328_, v___x_3331_);
lean_dec_ref(v___x_3331_);
lean_inc_ref(v_heq_3292_);
v___x_3333_ = l_Lean_Expr_app___override(v___x_3332_, v_heq_3292_);
v___x_3334_ = l_Lean_InductiveVal_numCtors(v_val_3293_);
lean_inc_ref(v___x_3333_);
v___x_3335_ = l_Lean_Meta_inferArgumentTypesN(v___x_3334_, v___x_3333_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref_known(v___x_3335_, 1);
lean_inc_ref(v_alts_3295_);
lean_inc(v_snd_3322_);
v___x_3337_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3294_, v_params_3289_, v_a_3336_, v_snd_3322_, v_alts_3295_, v_sz_3296_, v___x_3297_, v___x_3298_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
v___x_3339_ = l_Lean_mkAppN(v___x_3333_, v_a_3338_);
lean_dec(v_a_3338_);
v___x_3340_ = l_Lean_mkAppN(v___x_3339_, v_snd_3322_);
lean_dec(v_snd_3322_);
lean_inc_ref(v___x_3299_);
v___x_3341_ = lean_array_push(v___x_3299_, v_motive_3278_);
v___x_3342_ = l_Array_append___redArg(v_params_3289_, v___x_3341_);
lean_dec_ref(v___x_3341_);
v___x_3343_ = l_Array_append___redArg(v___x_3342_, v_is_3284_);
lean_dec_ref(v_is_3284_);
v___x_3344_ = lean_unsigned_to_nat(2u);
v___x_3345_ = lean_mk_empty_array_with_capacity(v___x_3344_);
v___x_3346_ = lean_array_push(v___x_3345_, v___x_3286_);
v___x_3347_ = lean_array_push(v___x_3346_, v___x_3285_);
v___x_3348_ = l_Array_append___redArg(v___x_3343_, v___x_3347_);
lean_dec_ref(v___x_3347_);
v___x_3349_ = lean_array_push(v___x_3299_, v_heq_3292_);
v___x_3350_ = l_Array_append___redArg(v___x_3348_, v___x_3349_);
lean_dec_ref(v___x_3349_);
v___x_3351_ = l_Array_append___redArg(v___x_3350_, v_alts_3295_);
lean_dec_ref(v_alts_3295_);
v___x_3352_ = l_Lean_Meta_mkLambdaFVars(v___x_3351_, v___x_3340_, v___x_3280_, v___x_3281_, v___x_3280_, v___x_3281_, v___x_3282_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
lean_dec_ref(v___x_3351_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3354_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc_n(v_a_3353_, 2);
lean_dec_ref_known(v___x_3352_, 1);
lean_inc(v___y_3312_);
lean_inc_ref(v___y_3311_);
lean_inc(v___y_3310_);
lean_inc_ref(v___y_3309_);
v___x_3354_ = lean_infer_type(v_a_3353_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3390_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v___x_3356_ = lean_box(1);
lean_inc(v_declName_3300_);
v___x_3357_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3300_, v_levelParams_3301_, v_a_3355_, v_a_3353_, v___x_3356_, v___y_3312_);
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3360_ = v___x_3357_;
v_isShared_3361_ = v_isSharedCheck_3390_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3357_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3390_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set_tag(v___x_3360_, 1);
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3364_; lean_object* v___f_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3364_ = lean_box(v___x_3280_);
lean_inc_ref(v___x_3363_);
v___f_3365_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3365_, 0, v___x_3363_);
lean_closure_set(v___f_3365_, 1, v___x_3364_);
v___x_3366_ = lean_nat_add(v_numIndices_3302_, v___x_3303_);
lean_inc(v___x_3304_);
v___x_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3304_);
v___x_3368_ = lean_box(0);
v___x_3369_ = lean_mk_empty_array_with_capacity(v___x_3303_);
v___x_3370_ = lean_array_push(v___x_3369_, v___x_3368_);
v___x_3371_ = lean_array_push(v___x_3370_, v___x_3368_);
v___x_3372_ = lean_array_push(v___x_3371_, v___x_3368_);
v___x_3373_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3325_ == 0)
{
lean_ctor_set(v___x_3324_, 1, v___x_3373_);
lean_ctor_set(v___x_3324_, 0, v___x_3304_);
v___x_3375_ = v___x_3324_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3304_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3376_; uint8_t v___y_3378_; uint8_t v___x_3387_; 
v___x_3376_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3376_, 0, v_numParams_3305_);
lean_ctor_set(v___x_3376_, 1, v___x_3366_);
lean_ctor_set(v___x_3376_, 2, v_snd_3306_);
lean_ctor_set(v___x_3376_, 3, v___x_3367_);
lean_ctor_set(v___x_3376_, 4, v___x_3372_);
lean_ctor_set(v___x_3376_, 5, v___x_3375_);
v___x_3387_ = l_Lean_isPrivateName(v_declName_3300_);
if (v___x_3387_ == 0)
{
v___y_3378_ = v___x_3281_;
goto v___jp_3377_;
}
else
{
v___y_3378_ = v___x_3280_;
goto v___jp_3377_;
}
v___jp_3377_:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3365_, v___y_3378_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec_ref_known(v___x_3379_, 1);
v___x_3380_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3300_);
v___x_3381_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3380_, v_declName_3300_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v___x_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; 
lean_dec_ref_known(v___x_3381_, 1);
lean_inc_n(v_declName_3300_, 2);
v___x_3382_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3300_, v___x_3376_, v___y_3310_, v___y_3312_);
lean_dec_ref(v___x_3382_);
v___x_3383_ = 0;
v___x_3384_ = l_Lean_Meta_setInlineAttribute(v_declName_3300_, v___x_3383_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v___x_3385_; 
lean_dec_ref_known(v___x_3384_, 1);
v___x_3385_ = l_Lean_enableRealizationsForConst(v_declName_3300_, v___y_3311_, v___y_3312_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v___x_3386_; 
lean_dec_ref_known(v___x_3385_, 1);
v___x_3386_ = l_Lean_compileDecl(v___x_3363_, v___x_3281_, v___y_3311_, v___y_3312_);
return v___x_3386_;
}
else
{
lean_dec_ref(v___x_3363_);
return v___x_3385_;
}
}
else
{
lean_dec_ref(v___x_3363_);
lean_dec(v_declName_3300_);
return v___x_3384_;
}
}
else
{
lean_dec_ref_known(v___x_3376_, 6);
lean_dec_ref(v___x_3363_);
lean_dec(v_declName_3300_);
return v___x_3381_;
}
}
else
{
lean_dec_ref_known(v___x_3376_, 6);
lean_dec_ref(v___x_3363_);
lean_dec(v_declName_3300_);
return v___x_3379_;
}
}
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec(v_a_3353_);
lean_del_object(v___x_3324_);
lean_dec_ref(v_snd_3306_);
lean_dec(v_numParams_3305_);
lean_dec(v___x_3304_);
lean_dec(v_levelParams_3301_);
lean_dec(v_declName_3300_);
v_a_3391_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3354_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3354_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
else
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3406_; 
lean_del_object(v___x_3324_);
lean_dec_ref(v_snd_3306_);
lean_dec(v_numParams_3305_);
lean_dec(v___x_3304_);
lean_dec(v_levelParams_3301_);
lean_dec(v_declName_3300_);
v_a_3399_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3401_ = v___x_3352_;
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3352_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3406_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3404_; 
if (v_isShared_3402_ == 0)
{
v___x_3404_ = v___x_3401_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3399_);
v___x_3404_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
return v___x_3404_;
}
}
}
}
else
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
lean_dec_ref(v___x_3333_);
lean_del_object(v___x_3324_);
lean_dec(v_snd_3322_);
lean_dec_ref(v_snd_3306_);
lean_dec(v_numParams_3305_);
lean_dec(v___x_3304_);
lean_dec(v_levelParams_3301_);
lean_dec(v_declName_3300_);
lean_dec_ref(v___x_3299_);
lean_dec_ref(v_alts_3295_);
lean_dec_ref(v_heq_3292_);
lean_dec_ref(v_params_3289_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_is_3284_);
lean_dec_ref(v_motive_3278_);
v_a_3407_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3414_ == 0)
{
v___x_3409_ = v___x_3337_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3337_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v___x_3333_);
lean_del_object(v___x_3324_);
lean_dec(v_snd_3322_);
lean_dec_ref(v_snd_3306_);
lean_dec(v_numParams_3305_);
lean_dec(v___x_3304_);
lean_dec(v_levelParams_3301_);
lean_dec(v_declName_3300_);
lean_dec_ref(v___x_3299_);
lean_dec_ref(v___x_3298_);
lean_dec_ref(v_alts_3295_);
lean_dec(v_tail_3294_);
lean_dec_ref(v_heq_3292_);
lean_dec_ref(v_params_3289_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_is_3284_);
lean_dec_ref(v_motive_3278_);
v_a_3415_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3335_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3335_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
lean_dec_ref(v_snd_3306_);
lean_dec(v_numParams_3305_);
lean_dec(v___x_3304_);
lean_dec(v_levelParams_3301_);
lean_dec(v_declName_3300_);
lean_dec_ref(v___x_3299_);
lean_dec_ref(v___x_3298_);
lean_dec_ref(v_alts_3295_);
lean_dec(v_tail_3294_);
lean_dec_ref(v_heq_3292_);
lean_dec_ref(v_params_3289_);
lean_dec(v___x_3288_);
lean_dec(v___x_3287_);
lean_dec_ref(v___x_3286_);
lean_dec_ref(v___x_3285_);
lean_dec_ref(v_is_3284_);
lean_dec_ref(v_motive_3278_);
v_a_3424_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3319_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3319_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3432_ = _args[0];
lean_object* v___x_3433_ = _args[1];
lean_object* v___x_3434_ = _args[2];
lean_object* v___x_3435_ = _args[3];
lean_object* v___x_3436_ = _args[4];
lean_object* v_ism1_x27_3437_ = _args[5];
lean_object* v_is_3438_ = _args[6];
lean_object* v___x_3439_ = _args[7];
lean_object* v___x_3440_ = _args[8];
lean_object* v___x_3441_ = _args[9];
lean_object* v___x_3442_ = _args[10];
lean_object* v_params_3443_ = _args[11];
lean_object* v___x_3444_ = _args[12];
lean_object* v___x_3445_ = _args[13];
lean_object* v_heq_3446_ = _args[14];
lean_object* v_val_3447_ = _args[15];
lean_object* v_tail_3448_ = _args[16];
lean_object* v_alts_3449_ = _args[17];
lean_object* v_sz_3450_ = _args[18];
lean_object* v___x_3451_ = _args[19];
lean_object* v___x_3452_ = _args[20];
lean_object* v___x_3453_ = _args[21];
lean_object* v_declName_3454_ = _args[22];
lean_object* v_levelParams_3455_ = _args[23];
lean_object* v_numIndices_3456_ = _args[24];
lean_object* v___x_3457_ = _args[25];
lean_object* v___x_3458_ = _args[26];
lean_object* v_numParams_3459_ = _args[27];
lean_object* v_snd_3460_ = _args[28];
lean_object* v_ism2_x27_3461_ = _args[29];
lean_object* v_x_3462_ = _args[30];
lean_object* v___y_3463_ = _args[31];
lean_object* v___y_3464_ = _args[32];
lean_object* v___y_3465_ = _args[33];
lean_object* v___y_3466_ = _args[34];
lean_object* v___y_3467_ = _args[35];
_start:
{
uint8_t v___x_15528__boxed_3468_; uint8_t v___x_15529__boxed_3469_; uint8_t v___x_15530__boxed_3470_; size_t v_sz_boxed_3471_; size_t v___x_15539__boxed_3472_; lean_object* v_res_3473_; 
v___x_15528__boxed_3468_ = lean_unbox(v___x_3434_);
v___x_15529__boxed_3469_ = lean_unbox(v___x_3435_);
v___x_15530__boxed_3470_ = lean_unbox(v___x_3436_);
v_sz_boxed_3471_ = lean_unbox_usize(v_sz_3450_);
lean_dec(v_sz_3450_);
v___x_15539__boxed_3472_ = lean_unbox_usize(v___x_3451_);
lean_dec(v___x_3451_);
v_res_3473_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3432_, v___x_3433_, v___x_15528__boxed_3468_, v___x_15529__boxed_3469_, v___x_15530__boxed_3470_, v_ism1_x27_3437_, v_is_3438_, v___x_3439_, v___x_3440_, v___x_3441_, v___x_3442_, v_params_3443_, v___x_3444_, v___x_3445_, v_heq_3446_, v_val_3447_, v_tail_3448_, v_alts_3449_, v_sz_boxed_3471_, v___x_15539__boxed_3472_, v___x_3452_, v___x_3453_, v_declName_3454_, v_levelParams_3455_, v_numIndices_3456_, v___x_3457_, v___x_3458_, v_numParams_3459_, v_snd_3460_, v_ism2_x27_3461_, v_x_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v___y_3464_);
lean_dec_ref(v___y_3463_);
lean_dec_ref(v_x_3462_);
lean_dec(v___x_3457_);
lean_dec(v_numIndices_3456_);
lean_dec_ref(v_val_3447_);
lean_dec_ref(v___x_3445_);
lean_dec_ref(v___x_3444_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3474_, lean_object* v___x_3475_, uint8_t v___x_3476_, uint8_t v___x_3477_, uint8_t v___x_3478_, lean_object* v_is_3479_, lean_object* v___x_3480_, lean_object* v___x_3481_, lean_object* v___x_3482_, lean_object* v___x_3483_, lean_object* v_params_3484_, lean_object* v___x_3485_, lean_object* v___x_3486_, lean_object* v_heq_3487_, lean_object* v_val_3488_, lean_object* v_tail_3489_, lean_object* v_alts_3490_, size_t v_sz_3491_, size_t v___x_3492_, lean_object* v___x_3493_, lean_object* v___x_3494_, lean_object* v_declName_3495_, lean_object* v_levelParams_3496_, lean_object* v_numIndices_3497_, lean_object* v___x_3498_, lean_object* v___x_3499_, lean_object* v_numParams_3500_, lean_object* v_snd_3501_, lean_object* v___x_3502_, lean_object* v___x_3503_, lean_object* v_ism1_x27_3504_, lean_object* v_x_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; 
v___x_3511_ = lean_box(v___x_3476_);
v___x_3512_ = lean_box(v___x_3477_);
v___x_3513_ = lean_box(v___x_3478_);
v___x_3514_ = lean_box_usize(v_sz_3491_);
v___x_3515_ = lean_box_usize(v___x_3492_);
v___f_3516_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3516_, 0, v_motive_3474_);
lean_closure_set(v___f_3516_, 1, v___x_3475_);
lean_closure_set(v___f_3516_, 2, v___x_3511_);
lean_closure_set(v___f_3516_, 3, v___x_3512_);
lean_closure_set(v___f_3516_, 4, v___x_3513_);
lean_closure_set(v___f_3516_, 5, v_ism1_x27_3504_);
lean_closure_set(v___f_3516_, 6, v_is_3479_);
lean_closure_set(v___f_3516_, 7, v___x_3480_);
lean_closure_set(v___f_3516_, 8, v___x_3481_);
lean_closure_set(v___f_3516_, 9, v___x_3482_);
lean_closure_set(v___f_3516_, 10, v___x_3483_);
lean_closure_set(v___f_3516_, 11, v_params_3484_);
lean_closure_set(v___f_3516_, 12, v___x_3485_);
lean_closure_set(v___f_3516_, 13, v___x_3486_);
lean_closure_set(v___f_3516_, 14, v_heq_3487_);
lean_closure_set(v___f_3516_, 15, v_val_3488_);
lean_closure_set(v___f_3516_, 16, v_tail_3489_);
lean_closure_set(v___f_3516_, 17, v_alts_3490_);
lean_closure_set(v___f_3516_, 18, v___x_3514_);
lean_closure_set(v___f_3516_, 19, v___x_3515_);
lean_closure_set(v___f_3516_, 20, v___x_3493_);
lean_closure_set(v___f_3516_, 21, v___x_3494_);
lean_closure_set(v___f_3516_, 22, v_declName_3495_);
lean_closure_set(v___f_3516_, 23, v_levelParams_3496_);
lean_closure_set(v___f_3516_, 24, v_numIndices_3497_);
lean_closure_set(v___f_3516_, 25, v___x_3498_);
lean_closure_set(v___f_3516_, 26, v___x_3499_);
lean_closure_set(v___f_3516_, 27, v_numParams_3500_);
lean_closure_set(v___f_3516_, 28, v_snd_3501_);
v___x_3517_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3502_, v___x_3503_, v___f_3516_, v___x_3476_, v___x_3476_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
return v___x_3517_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3518_ = _args[0];
lean_object* v___x_3519_ = _args[1];
lean_object* v___x_3520_ = _args[2];
lean_object* v___x_3521_ = _args[3];
lean_object* v___x_3522_ = _args[4];
lean_object* v_is_3523_ = _args[5];
lean_object* v___x_3524_ = _args[6];
lean_object* v___x_3525_ = _args[7];
lean_object* v___x_3526_ = _args[8];
lean_object* v___x_3527_ = _args[9];
lean_object* v_params_3528_ = _args[10];
lean_object* v___x_3529_ = _args[11];
lean_object* v___x_3530_ = _args[12];
lean_object* v_heq_3531_ = _args[13];
lean_object* v_val_3532_ = _args[14];
lean_object* v_tail_3533_ = _args[15];
lean_object* v_alts_3534_ = _args[16];
lean_object* v_sz_3535_ = _args[17];
lean_object* v___x_3536_ = _args[18];
lean_object* v___x_3537_ = _args[19];
lean_object* v___x_3538_ = _args[20];
lean_object* v_declName_3539_ = _args[21];
lean_object* v_levelParams_3540_ = _args[22];
lean_object* v_numIndices_3541_ = _args[23];
lean_object* v___x_3542_ = _args[24];
lean_object* v___x_3543_ = _args[25];
lean_object* v_numParams_3544_ = _args[26];
lean_object* v_snd_3545_ = _args[27];
lean_object* v___x_3546_ = _args[28];
lean_object* v___x_3547_ = _args[29];
lean_object* v_ism1_x27_3548_ = _args[30];
lean_object* v_x_3549_ = _args[31];
lean_object* v___y_3550_ = _args[32];
lean_object* v___y_3551_ = _args[33];
lean_object* v___y_3552_ = _args[34];
lean_object* v___y_3553_ = _args[35];
lean_object* v___y_3554_ = _args[36];
_start:
{
uint8_t v___x_15850__boxed_3555_; uint8_t v___x_15851__boxed_3556_; uint8_t v___x_15852__boxed_3557_; size_t v_sz_boxed_3558_; size_t v___x_15861__boxed_3559_; lean_object* v_res_3560_; 
v___x_15850__boxed_3555_ = lean_unbox(v___x_3520_);
v___x_15851__boxed_3556_ = lean_unbox(v___x_3521_);
v___x_15852__boxed_3557_ = lean_unbox(v___x_3522_);
v_sz_boxed_3558_ = lean_unbox_usize(v_sz_3535_);
lean_dec(v_sz_3535_);
v___x_15861__boxed_3559_ = lean_unbox_usize(v___x_3536_);
lean_dec(v___x_3536_);
v_res_3560_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3518_, v___x_3519_, v___x_15850__boxed_3555_, v___x_15851__boxed_3556_, v___x_15852__boxed_3557_, v_is_3523_, v___x_3524_, v___x_3525_, v___x_3526_, v___x_3527_, v_params_3528_, v___x_3529_, v___x_3530_, v_heq_3531_, v_val_3532_, v_tail_3533_, v_alts_3534_, v_sz_boxed_3558_, v___x_15861__boxed_3559_, v___x_3537_, v___x_3538_, v_declName_3539_, v_levelParams_3540_, v_numIndices_3541_, v___x_3542_, v___x_3543_, v_numParams_3544_, v_snd_3545_, v___x_3546_, v___x_3547_, v_ism1_x27_3548_, v_x_3549_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec_ref(v_x_3549_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3561_, lean_object* v___x_3562_, lean_object* v_motive_3563_, lean_object* v___x_3564_, uint8_t v___x_3565_, uint8_t v___x_3566_, uint8_t v___x_3567_, lean_object* v_is_3568_, lean_object* v___x_3569_, lean_object* v___x_3570_, lean_object* v___x_3571_, lean_object* v___x_3572_, lean_object* v_params_3573_, lean_object* v___x_3574_, lean_object* v___x_3575_, lean_object* v_heq_3576_, lean_object* v_val_3577_, lean_object* v_tail_3578_, size_t v_sz_3579_, size_t v___x_3580_, lean_object* v___x_3581_, lean_object* v___x_3582_, lean_object* v_declName_3583_, lean_object* v_levelParams_3584_, lean_object* v___x_3585_, lean_object* v___x_3586_, lean_object* v_numParams_3587_, lean_object* v_snd_3588_, lean_object* v___x_3589_, lean_object* v_alts_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___f_3603_; lean_object* v___x_3604_; 
v___x_3596_ = lean_nat_add(v_numIndices_3561_, v___x_3562_);
v___x_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
v___x_3598_ = lean_box(v___x_3565_);
v___x_3599_ = lean_box(v___x_3566_);
v___x_3600_ = lean_box(v___x_3567_);
v___x_3601_ = lean_box_usize(v_sz_3579_);
v___x_3602_ = lean_box_usize(v___x_3580_);
lean_inc_ref(v___x_3597_);
lean_inc_ref(v___x_3589_);
v___f_3603_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3603_, 0, v_motive_3563_);
lean_closure_set(v___f_3603_, 1, v___x_3564_);
lean_closure_set(v___f_3603_, 2, v___x_3598_);
lean_closure_set(v___f_3603_, 3, v___x_3599_);
lean_closure_set(v___f_3603_, 4, v___x_3600_);
lean_closure_set(v___f_3603_, 5, v_is_3568_);
lean_closure_set(v___f_3603_, 6, v___x_3569_);
lean_closure_set(v___f_3603_, 7, v___x_3570_);
lean_closure_set(v___f_3603_, 8, v___x_3571_);
lean_closure_set(v___f_3603_, 9, v___x_3572_);
lean_closure_set(v___f_3603_, 10, v_params_3573_);
lean_closure_set(v___f_3603_, 11, v___x_3574_);
lean_closure_set(v___f_3603_, 12, v___x_3575_);
lean_closure_set(v___f_3603_, 13, v_heq_3576_);
lean_closure_set(v___f_3603_, 14, v_val_3577_);
lean_closure_set(v___f_3603_, 15, v_tail_3578_);
lean_closure_set(v___f_3603_, 16, v_alts_3590_);
lean_closure_set(v___f_3603_, 17, v___x_3601_);
lean_closure_set(v___f_3603_, 18, v___x_3602_);
lean_closure_set(v___f_3603_, 19, v___x_3581_);
lean_closure_set(v___f_3603_, 20, v___x_3582_);
lean_closure_set(v___f_3603_, 21, v_declName_3583_);
lean_closure_set(v___f_3603_, 22, v_levelParams_3584_);
lean_closure_set(v___f_3603_, 23, v_numIndices_3561_);
lean_closure_set(v___f_3603_, 24, v___x_3585_);
lean_closure_set(v___f_3603_, 25, v___x_3586_);
lean_closure_set(v___f_3603_, 26, v_numParams_3587_);
lean_closure_set(v___f_3603_, 27, v_snd_3588_);
lean_closure_set(v___f_3603_, 28, v___x_3589_);
lean_closure_set(v___f_3603_, 29, v___x_3597_);
v___x_3604_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3589_, v___x_3597_, v___f_3603_, v___x_3565_, v___x_3565_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3605_ = _args[0];
lean_object* v___x_3606_ = _args[1];
lean_object* v_motive_3607_ = _args[2];
lean_object* v___x_3608_ = _args[3];
lean_object* v___x_3609_ = _args[4];
lean_object* v___x_3610_ = _args[5];
lean_object* v___x_3611_ = _args[6];
lean_object* v_is_3612_ = _args[7];
lean_object* v___x_3613_ = _args[8];
lean_object* v___x_3614_ = _args[9];
lean_object* v___x_3615_ = _args[10];
lean_object* v___x_3616_ = _args[11];
lean_object* v_params_3617_ = _args[12];
lean_object* v___x_3618_ = _args[13];
lean_object* v___x_3619_ = _args[14];
lean_object* v_heq_3620_ = _args[15];
lean_object* v_val_3621_ = _args[16];
lean_object* v_tail_3622_ = _args[17];
lean_object* v_sz_3623_ = _args[18];
lean_object* v___x_3624_ = _args[19];
lean_object* v___x_3625_ = _args[20];
lean_object* v___x_3626_ = _args[21];
lean_object* v_declName_3627_ = _args[22];
lean_object* v_levelParams_3628_ = _args[23];
lean_object* v___x_3629_ = _args[24];
lean_object* v___x_3630_ = _args[25];
lean_object* v_numParams_3631_ = _args[26];
lean_object* v_snd_3632_ = _args[27];
lean_object* v___x_3633_ = _args[28];
lean_object* v_alts_3634_ = _args[29];
lean_object* v___y_3635_ = _args[30];
lean_object* v___y_3636_ = _args[31];
lean_object* v___y_3637_ = _args[32];
lean_object* v___y_3638_ = _args[33];
lean_object* v___y_3639_ = _args[34];
_start:
{
uint8_t v___x_15943__boxed_3640_; uint8_t v___x_15944__boxed_3641_; uint8_t v___x_15945__boxed_3642_; size_t v_sz_boxed_3643_; size_t v___x_15954__boxed_3644_; lean_object* v_res_3645_; 
v___x_15943__boxed_3640_ = lean_unbox(v___x_3609_);
v___x_15944__boxed_3641_ = lean_unbox(v___x_3610_);
v___x_15945__boxed_3642_ = lean_unbox(v___x_3611_);
v_sz_boxed_3643_ = lean_unbox_usize(v_sz_3623_);
lean_dec(v_sz_3623_);
v___x_15954__boxed_3644_ = lean_unbox_usize(v___x_3624_);
lean_dec(v___x_3624_);
v_res_3645_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3605_, v___x_3606_, v_motive_3607_, v___x_3608_, v___x_15943__boxed_3640_, v___x_15944__boxed_3641_, v___x_15945__boxed_3642_, v_is_3612_, v___x_3613_, v___x_3614_, v___x_3615_, v___x_3616_, v_params_3617_, v___x_3618_, v___x_3619_, v_heq_3620_, v_val_3621_, v_tail_3622_, v_sz_boxed_3643_, v___x_15954__boxed_3644_, v___x_3625_, v___x_3626_, v_declName_3627_, v_levelParams_3628_, v___x_3629_, v___x_3630_, v_numParams_3631_, v_snd_3632_, v___x_3633_, v_alts_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v___x_3606_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3646_, lean_object* v_declInfos_3647_, lean_object* v_k_3648_, lean_object* v_kind_3649_, lean_object* v_x_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
uint8_t v_kind_boxed_3656_; lean_object* v_res_3657_; 
v_kind_boxed_3656_ = lean_unbox(v_kind_3649_);
v_res_3657_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3646_, v_declInfos_3647_, v_k_3648_, v_kind_boxed_3656_, v_x_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3658_, lean_object* v_k_3659_, uint8_t v_kind_3660_, lean_object* v_acc_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v___x_3667_; lean_object* v_toApplicative_3668_; lean_object* v_toFunctor_3669_; lean_object* v_toSeq_3670_; lean_object* v_toSeqLeft_3671_; lean_object* v_toSeqRight_3672_; lean_object* v___f_3673_; lean_object* v___f_3674_; lean_object* v___f_3675_; lean_object* v___f_3676_; lean_object* v___x_3677_; lean_object* v___f_3678_; lean_object* v___f_3679_; lean_object* v___f_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v_toApplicative_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3742_; 
v___x_3667_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3668_ = lean_ctor_get(v___x_3667_, 0);
v_toFunctor_3669_ = lean_ctor_get(v_toApplicative_3668_, 0);
v_toSeq_3670_ = lean_ctor_get(v_toApplicative_3668_, 2);
v_toSeqLeft_3671_ = lean_ctor_get(v_toApplicative_3668_, 3);
v_toSeqRight_3672_ = lean_ctor_get(v_toApplicative_3668_, 4);
v___f_3673_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3674_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3669_, 2);
v___f_3675_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3675_, 0, v_toFunctor_3669_);
v___f_3676_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3676_, 0, v_toFunctor_3669_);
v___x_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___f_3675_);
lean_ctor_set(v___x_3677_, 1, v___f_3676_);
lean_inc(v_toSeqRight_3672_);
v___f_3678_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3678_, 0, v_toSeqRight_3672_);
lean_inc(v_toSeqLeft_3671_);
v___f_3679_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3679_, 0, v_toSeqLeft_3671_);
lean_inc(v_toSeq_3670_);
v___f_3680_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3680_, 0, v_toSeq_3670_);
v___x_3681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3677_);
lean_ctor_set(v___x_3681_, 1, v___f_3673_);
lean_ctor_set(v___x_3681_, 2, v___f_3680_);
lean_ctor_set(v___x_3681_, 3, v___f_3679_);
lean_ctor_set(v___x_3681_, 4, v___f_3678_);
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
lean_ctor_set(v___x_3682_, 1, v___f_3674_);
v___x_3683_ = l_StateRefT_x27_instMonad___redArg(v___x_3682_);
v_toApplicative_3684_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; 
v_unused_3743_ = lean_ctor_get(v___x_3683_, 1);
lean_dec(v_unused_3743_);
v___x_3686_ = v___x_3683_;
v_isShared_3687_ = v_isSharedCheck_3742_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_toApplicative_3684_);
lean_dec(v___x_3683_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3742_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v_toFunctor_3688_; lean_object* v_toSeq_3689_; lean_object* v_toSeqLeft_3690_; lean_object* v_toSeqRight_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3740_; 
v_toFunctor_3688_ = lean_ctor_get(v_toApplicative_3684_, 0);
v_toSeq_3689_ = lean_ctor_get(v_toApplicative_3684_, 2);
v_toSeqLeft_3690_ = lean_ctor_get(v_toApplicative_3684_, 3);
v_toSeqRight_3691_ = lean_ctor_get(v_toApplicative_3684_, 4);
v_isSharedCheck_3740_ = !lean_is_exclusive(v_toApplicative_3684_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; 
v_unused_3741_ = lean_ctor_get(v_toApplicative_3684_, 1);
lean_dec(v_unused_3741_);
v___x_3693_ = v_toApplicative_3684_;
v_isShared_3694_ = v_isSharedCheck_3740_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_toSeqRight_3691_);
lean_inc(v_toSeqLeft_3690_);
lean_inc(v_toSeq_3689_);
lean_inc(v_toFunctor_3688_);
lean_dec(v_toApplicative_3684_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3740_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___f_3695_; lean_object* v___f_3696_; lean_object* v___f_3697_; lean_object* v___f_3698_; lean_object* v___x_3699_; lean_object* v___f_3700_; lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___x_3704_; 
v___f_3695_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3696_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3688_);
v___f_3697_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3697_, 0, v_toFunctor_3688_);
v___f_3698_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3698_, 0, v_toFunctor_3688_);
v___x_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___f_3697_);
lean_ctor_set(v___x_3699_, 1, v___f_3698_);
v___f_3700_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3700_, 0, v_toSeqRight_3691_);
v___f_3701_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3701_, 0, v_toSeqLeft_3690_);
v___f_3702_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3702_, 0, v_toSeq_3689_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 4, v___f_3700_);
lean_ctor_set(v___x_3693_, 3, v___f_3701_);
lean_ctor_set(v___x_3693_, 2, v___f_3702_);
lean_ctor_set(v___x_3693_, 1, v___f_3695_);
lean_ctor_set(v___x_3693_, 0, v___x_3699_);
v___x_3704_ = v___x_3693_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3739_, 1, v___f_3695_);
lean_ctor_set(v_reuseFailAlloc_3739_, 2, v___f_3702_);
lean_ctor_set(v_reuseFailAlloc_3739_, 3, v___f_3701_);
lean_ctor_set(v_reuseFailAlloc_3739_, 4, v___f_3700_);
v___x_3704_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3706_; 
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 1, v___f_3696_);
lean_ctor_set(v___x_3686_, 0, v___x_3704_);
v___x_3706_ = v___x_3686_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3704_);
lean_ctor_set(v_reuseFailAlloc_3738_, 1, v___f_3696_);
v___x_3706_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; uint8_t v___x_3709_; 
v___x_3707_ = lean_array_get_size(v_acc_3661_);
v___x_3708_ = lean_array_get_size(v_declInfos_3658_);
v___x_3709_ = lean_nat_dec_lt(v___x_3707_, v___x_3708_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; 
lean_dec_ref(v___x_3706_);
lean_dec_ref(v_declInfos_3658_);
lean_inc(v___y_3665_);
lean_inc_ref(v___y_3664_);
lean_inc(v___y_3663_);
lean_inc_ref(v___y_3662_);
v___x_3710_ = lean_apply_6(v_k_3659_, v_acc_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, lean_box(0));
return v___x_3710_;
}
else
{
lean_object* v___x_3711_; uint8_t v___x_3712_; lean_object* v___x_3713_; lean_object* v___f_3714_; lean_object* v___f_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v_snd_3720_; lean_object* v_fst_3721_; lean_object* v_fst_3722_; lean_object* v_snd_3723_; lean_object* v___x_3724_; lean_object* v___f_3725_; lean_object* v___x_3726_; 
v___x_3711_ = lean_box(0);
v___x_3712_ = 0;
v___x_3713_ = l_Lean_instInhabitedExpr;
v___f_3714_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3714_, 0, v___x_3706_);
lean_closure_set(v___f_3714_, 1, v___x_3713_);
v___f_3715_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3715_, 0, v___f_3714_);
v___x_3716_ = lean_box(v___x_3712_);
v___x_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
lean_ctor_set(v___x_3717_, 1, v___f_3715_);
v___x_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3711_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = lean_array_get(v___x_3718_, v_declInfos_3658_, v___x_3707_);
lean_dec_ref_known(v___x_3718_, 2);
v_snd_3720_ = lean_ctor_get(v___x_3719_, 1);
lean_inc(v_snd_3720_);
v_fst_3721_ = lean_ctor_get(v___x_3719_, 0);
lean_inc(v_fst_3721_);
lean_dec(v___x_3719_);
v_fst_3722_ = lean_ctor_get(v_snd_3720_, 0);
lean_inc(v_fst_3722_);
v_snd_3723_ = lean_ctor_get(v_snd_3720_, 1);
lean_inc(v_snd_3723_);
lean_dec(v_snd_3720_);
v___x_3724_ = lean_box(v_kind_3660_);
lean_inc_ref(v_acc_3661_);
v___f_3725_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3725_, 0, v_acc_3661_);
lean_closure_set(v___f_3725_, 1, v_declInfos_3658_);
lean_closure_set(v___f_3725_, 2, v_k_3659_);
lean_closure_set(v___f_3725_, 3, v___x_3724_);
lean_inc(v___y_3665_);
lean_inc_ref(v___y_3664_);
lean_inc(v___y_3663_);
lean_inc_ref(v___y_3662_);
v___x_3726_ = lean_apply_6(v_snd_3723_, v_acc_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, lean_box(0));
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; uint8_t v___x_3728_; lean_object* v___x_3729_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
v___x_3728_ = lean_unbox(v_fst_3722_);
lean_dec(v_fst_3722_);
v___x_3729_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3721_, v___x_3728_, v_a_3727_, v___f_3725_, v_kind_3660_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3729_;
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v___f_3725_);
lean_dec(v_fst_3722_);
lean_dec(v_fst_3721_);
v_a_3730_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3726_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3726_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3744_, lean_object* v_declInfos_3745_, lean_object* v_k_3746_, uint8_t v_kind_3747_, lean_object* v_x_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3754_ = lean_array_push(v_acc_3744_, v_x_3748_);
v___x_3755_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3745_, v_k_3746_, v_kind_3747_, v___x_3754_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3756_, lean_object* v_k_3757_, lean_object* v_kind_3758_, lean_object* v_acc_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_){
_start:
{
uint8_t v_kind_boxed_3765_; lean_object* v_res_3766_; 
v_kind_boxed_3765_ = lean_unbox(v_kind_3758_);
v_res_3766_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3756_, v_k_3757_, v_kind_boxed_3765_, v_acc_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3767_, lean_object* v_k_3768_, uint8_t v_kind_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
v___x_3775_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3776_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3767_, v_k_3768_, v_kind_3769_, v___x_3775_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
return v___x_3776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3777_, lean_object* v_k_3778_, lean_object* v_kind_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
uint8_t v_kind_boxed_3785_; lean_object* v_res_3786_; 
v_kind_boxed_3785_ = lean_unbox(v_kind_3779_);
v_res_3786_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3777_, v_k_3778_, v_kind_boxed_3785_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
lean_dec(v___y_3783_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3787_, lean_object* v_k_3788_, uint8_t v_kind_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_){
_start:
{
size_t v_sz_3795_; size_t v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_sz_3795_ = lean_array_size(v_declInfos_3787_);
v___x_3796_ = ((size_t)0ULL);
v___x_3797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3795_, v___x_3796_, v_declInfos_3787_);
v___x_3798_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3797_, v_k_3788_, v_kind_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3799_, lean_object* v_k_3800_, lean_object* v_kind_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_){
_start:
{
uint8_t v_kind_boxed_3807_; lean_object* v_res_3808_; 
v_kind_boxed_3807_ = lean_unbox(v_kind_3801_);
v_res_3808_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3799_, v_k_3800_, v_kind_boxed_3807_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3803_);
lean_dec_ref(v___y_3802_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3809_, lean_object* v_k_3810_, uint8_t v_kind_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
size_t v_sz_3817_; size_t v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
v_sz_3817_ = lean_array_size(v_declInfos_3809_);
v___x_3818_ = ((size_t)0ULL);
v___x_3819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3817_, v___x_3818_, v_declInfos_3809_);
v___x_3820_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3819_, v_k_3810_, v_kind_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3821_, lean_object* v_k_3822_, lean_object* v_kind_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_){
_start:
{
uint8_t v_kind_boxed_3829_; lean_object* v_res_3830_; 
v_kind_boxed_3829_ = lean_unbox(v_kind_3823_);
v_res_3830_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3821_, v_k_3822_, v_kind_boxed_3829_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
lean_dec(v___y_3827_);
lean_dec_ref(v___y_3826_);
lean_dec(v___y_3825_);
lean_dec_ref(v___y_3824_);
return v_res_3830_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3833_ = lean_box(0);
v___x_3834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3835_ = l_Lean_mkConst(v___x_3834_, v___x_3833_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3836_, lean_object* v_v_3837_, lean_object* v___x_3838_, lean_object* v___x_3839_, lean_object* v___x_3840_, lean_object* v_motive_3841_, uint8_t v___x_3842_, uint8_t v___x_3843_, uint8_t v___x_3844_, lean_object* v_zs12_3845_, lean_object* v_is_3846_, lean_object* v_fields1_3847_, lean_object* v_fields2_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v_e_3864_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
lean_inc_ref(v___x_3840_);
v___x_3874_ = l_Lean_mkAppN(v___x_3840_, v_fields1_3847_);
v___x_3875_ = l_Lean_mkAppN(v___x_3840_, v_fields2_3848_);
lean_inc(v___x_3838_);
v___x_3876_ = l_Lean_mkNatLit(v___x_3838_);
v___x_3877_ = l_Lean_Meta_mkEqRefl(v___x_3876_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
v___x_3879_ = lean_unsigned_to_nat(3u);
v___x_3880_ = lean_mk_empty_array_with_capacity(v___x_3879_);
v___x_3881_ = lean_array_push(v___x_3880_, v___x_3874_);
v___x_3882_ = lean_array_push(v___x_3881_, v___x_3875_);
v___x_3883_ = lean_array_push(v___x_3882_, v_a_3878_);
v___x_3884_ = l_Array_append___redArg(v_is_3846_, v___x_3883_);
lean_dec_ref(v___x_3883_);
v___x_3885_ = l_Lean_mkAppN(v_motive_3841_, v___x_3884_);
lean_dec_ref(v___x_3884_);
v___x_3886_ = l_Lean_Meta_mkForallFVars(v_zs12_3845_, v___x_3885_, v___x_3842_, v___x_3843_, v___x_3843_, v___x_3844_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = lean_array_get_size(v_zs12_3845_);
v___x_3889_ = lean_nat_dec_eq(v___x_3888_, v___x_3836_);
if (v___x_3889_ == 0)
{
v_e_3864_ = v_a_3887_;
goto v___jp_3863_;
}
else
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3891_ = l_Lean_mkArrow(v___x_3890_, v_a_3887_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
v_e_3864_ = v_a_3892_;
goto v___jp_3863_;
}
else
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3900_; 
lean_dec(v___x_3838_);
lean_dec(v_v_3837_);
lean_dec(v___x_3836_);
v_a_3893_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3895_ = v___x_3891_;
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3891_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3900_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3898_; 
if (v_isShared_3896_ == 0)
{
v___x_3898_ = v___x_3895_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_a_3893_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_dec(v___x_3838_);
lean_dec(v_v_3837_);
lean_dec(v___x_3836_);
v_a_3901_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3886_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3886_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
else
{
lean_object* v_a_3909_; lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3916_; 
lean_dec_ref(v___x_3875_);
lean_dec_ref(v___x_3874_);
lean_dec_ref(v_is_3846_);
lean_dec_ref(v_motive_3841_);
lean_dec(v___x_3838_);
lean_dec(v_v_3837_);
lean_dec(v___x_3836_);
v_a_3909_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3916_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3911_ = v___x_3877_;
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
else
{
lean_inc(v_a_3909_);
lean_dec(v___x_3877_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3916_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3914_; 
if (v_isShared_3912_ == 0)
{
v___x_3914_ = v___x_3911_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3909_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
v___jp_3854_:
{
lean_object* v___x_3857_; uint8_t v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3857_ = lean_array_get_size(v_zs12_3845_);
v___x_3858_ = lean_nat_dec_eq(v___x_3857_, v___x_3836_);
v___x_3859_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3859_, 0, v___x_3857_);
lean_ctor_set(v___x_3859_, 1, v___x_3836_);
lean_ctor_set_uint8(v___x_3859_, sizeof(void*)*2, v___x_3858_);
v___x_3860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___y_3856_);
lean_ctor_set(v___x_3860_, 1, v___y_3855_);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
lean_ctor_set(v___x_3861_, 1, v___x_3859_);
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
v___jp_3863_:
{
if (lean_obj_tag(v_v_3837_) == 1)
{
lean_object* v_str_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; 
lean_dec(v___x_3838_);
v_str_3865_ = lean_ctor_get(v_v_3837_, 1);
lean_inc_ref(v_str_3865_);
lean_dec_ref_known(v_v_3837_, 2);
v___x_3866_ = lean_box(0);
v___x_3867_ = l_Lean_Name_str___override(v___x_3866_, v_str_3865_);
v___y_3855_ = v_e_3864_;
v___y_3856_ = v___x_3867_;
goto v___jp_3854_;
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
lean_dec(v_v_3837_);
v___x_3868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3869_ = lean_nat_add(v___x_3838_, v___x_3839_);
lean_dec(v___x_3838_);
v___x_3870_ = l_Nat_reprFast(v___x_3869_);
v___x_3871_ = lean_string_append(v___x_3868_, v___x_3870_);
lean_dec_ref(v___x_3870_);
v___x_3872_ = lean_box(0);
v___x_3873_ = l_Lean_Name_str___override(v___x_3872_, v___x_3871_);
v___y_3855_ = v_e_3864_;
v___y_3856_ = v___x_3873_;
goto v___jp_3854_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3917_ = _args[0];
lean_object* v_v_3918_ = _args[1];
lean_object* v___x_3919_ = _args[2];
lean_object* v___x_3920_ = _args[3];
lean_object* v___x_3921_ = _args[4];
lean_object* v_motive_3922_ = _args[5];
lean_object* v___x_3923_ = _args[6];
lean_object* v___x_3924_ = _args[7];
lean_object* v___x_3925_ = _args[8];
lean_object* v_zs12_3926_ = _args[9];
lean_object* v_is_3927_ = _args[10];
lean_object* v_fields1_3928_ = _args[11];
lean_object* v_fields2_3929_ = _args[12];
lean_object* v___y_3930_ = _args[13];
lean_object* v___y_3931_ = _args[14];
lean_object* v___y_3932_ = _args[15];
lean_object* v___y_3933_ = _args[16];
lean_object* v___y_3934_ = _args[17];
_start:
{
uint8_t v___x_16290__boxed_3935_; uint8_t v___x_16291__boxed_3936_; uint8_t v___x_16292__boxed_3937_; lean_object* v_res_3938_; 
v___x_16290__boxed_3935_ = lean_unbox(v___x_3923_);
v___x_16291__boxed_3936_ = lean_unbox(v___x_3924_);
v___x_16292__boxed_3937_ = lean_unbox(v___x_3925_);
v_res_3938_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3917_, v_v_3918_, v___x_3919_, v___x_3920_, v___x_3921_, v_motive_3922_, v___x_16290__boxed_3935_, v___x_16291__boxed_3936_, v___x_16292__boxed_3937_, v_zs12_3926_, v_is_3927_, v_fields1_3928_, v_fields2_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec_ref(v_fields2_3929_);
lean_dec_ref(v_fields1_3928_);
lean_dec_ref(v_zs12_3926_);
lean_dec(v___x_3920_);
return v_res_3938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3939_, lean_object* v_params_3940_, lean_object* v_motive_3941_, size_t v_sz_3942_, size_t v_i_3943_, lean_object* v_bs_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
uint8_t v___x_3950_; 
v___x_3950_ = lean_usize_dec_lt(v_i_3943_, v_sz_3942_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; 
lean_dec_ref(v_motive_3941_);
lean_dec(v_tail_3939_);
v___x_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3951_, 0, v_bs_3944_);
return v___x_3951_;
}
else
{
lean_object* v___x_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; uint8_t v___x_3955_; lean_object* v_v_3956_; lean_object* v_bs_x27_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___f_3964_; lean_object* v___x_3965_; 
v___x_3952_ = lean_unsigned_to_nat(0u);
v___x_3953_ = lean_unsigned_to_nat(1u);
v___x_3954_ = 0;
v___x_3955_ = 1;
v_v_3956_ = lean_array_uget(v_bs_3944_, v_i_3943_);
v_bs_x27_3957_ = lean_array_uset(v_bs_3944_, v_i_3943_, v___x_3952_);
v___x_3958_ = lean_usize_to_nat(v_i_3943_);
lean_inc(v_tail_3939_);
lean_inc(v_v_3956_);
v___x_3959_ = l_Lean_mkConst(v_v_3956_, v_tail_3939_);
v___x_3960_ = l_Lean_mkAppN(v___x_3959_, v_params_3940_);
v___x_3961_ = lean_box(v___x_3954_);
v___x_3962_ = lean_box(v___x_3950_);
v___x_3963_ = lean_box(v___x_3955_);
lean_inc_ref(v_motive_3941_);
lean_inc_ref(v___x_3960_);
v___f_3964_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3964_, 0, v___x_3952_);
lean_closure_set(v___f_3964_, 1, v_v_3956_);
lean_closure_set(v___f_3964_, 2, v___x_3958_);
lean_closure_set(v___f_3964_, 3, v___x_3953_);
lean_closure_set(v___f_3964_, 4, v___x_3960_);
lean_closure_set(v___f_3964_, 5, v_motive_3941_);
lean_closure_set(v___f_3964_, 6, v___x_3961_);
lean_closure_set(v___f_3964_, 7, v___x_3962_);
lean_closure_set(v___f_3964_, 8, v___x_3963_);
v___x_3965_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3960_, v___f_3964_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3965_) == 0)
{
lean_object* v_a_3966_; size_t v___x_3967_; size_t v___x_3968_; lean_object* v___x_3969_; 
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
lean_inc(v_a_3966_);
lean_dec_ref_known(v___x_3965_, 1);
v___x_3967_ = ((size_t)1ULL);
v___x_3968_ = lean_usize_add(v_i_3943_, v___x_3967_);
v___x_3969_ = lean_array_uset(v_bs_x27_3957_, v_i_3943_, v_a_3966_);
v_i_3943_ = v___x_3968_;
v_bs_3944_ = v___x_3969_;
goto _start;
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec_ref(v_bs_x27_3957_);
lean_dec_ref(v_motive_3941_);
lean_dec(v_tail_3939_);
v_a_3971_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3965_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3965_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3979_, lean_object* v_params_3980_, lean_object* v_motive_3981_, lean_object* v_sz_3982_, lean_object* v_i_3983_, lean_object* v_bs_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_){
_start:
{
size_t v_sz_boxed_3990_; size_t v_i_boxed_3991_; lean_object* v_res_3992_; 
v_sz_boxed_3990_ = lean_unbox_usize(v_sz_3982_);
lean_dec(v_sz_3982_);
v_i_boxed_3991_ = lean_unbox_usize(v_i_3983_);
lean_dec(v_i_3983_);
v_res_3992_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3979_, v_params_3980_, v_motive_3981_, v_sz_boxed_3990_, v_i_boxed_3991_, v_bs_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec_ref(v_params_3980_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3995_, lean_object* v_tail_3996_, lean_object* v_params_3997_, lean_object* v_numIndices_3998_, lean_object* v___x_3999_, lean_object* v___x_4000_, uint8_t v___x_4001_, uint8_t v___x_4002_, uint8_t v___x_4003_, lean_object* v_is_4004_, lean_object* v___x_4005_, lean_object* v___x_4006_, lean_object* v___x_4007_, lean_object* v___x_4008_, lean_object* v___x_4009_, lean_object* v___x_4010_, lean_object* v_heq_4011_, lean_object* v_val_4012_, lean_object* v___x_4013_, lean_object* v_declName_4014_, lean_object* v_levelParams_4015_, lean_object* v___x_4016_, lean_object* v___x_4017_, lean_object* v_numParams_4018_, lean_object* v___x_4019_, lean_object* v_motive_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; size_t v_sz_4027_; size_t v___x_4028_; lean_object* v___x_4029_; 
v___x_4026_ = lean_array_mk(v_ctors_3995_);
v_sz_4027_ = lean_array_size(v___x_4026_);
v___x_4028_ = ((size_t)0ULL);
lean_inc_ref(v___x_4026_);
lean_inc_ref(v_motive_4020_);
lean_inc(v_tail_3996_);
v___x_4029_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3996_, v_params_3997_, v_motive_4020_, v_sz_4027_, v___x_4028_, v___x_4026_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4031_; lean_object* v_fst_4032_; lean_object* v_snd_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___f_4039_; uint8_t v___x_4040_; lean_object* v___x_4041_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v___x_4031_ = l_Array_unzip___redArg(v_a_4030_);
lean_dec(v_a_4030_);
v_fst_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_fst_4032_);
v_snd_4033_ = lean_ctor_get(v___x_4031_, 1);
lean_inc(v_snd_4033_);
lean_dec_ref(v___x_4031_);
v___x_4034_ = lean_box(v___x_4001_);
v___x_4035_ = lean_box(v___x_4002_);
v___x_4036_ = lean_box(v___x_4003_);
v___x_4037_ = lean_box_usize(v_sz_4027_);
v___x_4038_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4039_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4039_, 0, v_numIndices_3998_);
lean_closure_set(v___f_4039_, 1, v___x_3999_);
lean_closure_set(v___f_4039_, 2, v_motive_4020_);
lean_closure_set(v___f_4039_, 3, v___x_4000_);
lean_closure_set(v___f_4039_, 4, v___x_4034_);
lean_closure_set(v___f_4039_, 5, v___x_4035_);
lean_closure_set(v___f_4039_, 6, v___x_4036_);
lean_closure_set(v___f_4039_, 7, v_is_4004_);
lean_closure_set(v___f_4039_, 8, v___x_4005_);
lean_closure_set(v___f_4039_, 9, v___x_4006_);
lean_closure_set(v___f_4039_, 10, v___x_4007_);
lean_closure_set(v___f_4039_, 11, v___x_4008_);
lean_closure_set(v___f_4039_, 12, v_params_3997_);
lean_closure_set(v___f_4039_, 13, v___x_4009_);
lean_closure_set(v___f_4039_, 14, v___x_4010_);
lean_closure_set(v___f_4039_, 15, v_heq_4011_);
lean_closure_set(v___f_4039_, 16, v_val_4012_);
lean_closure_set(v___f_4039_, 17, v_tail_3996_);
lean_closure_set(v___f_4039_, 18, v___x_4037_);
lean_closure_set(v___f_4039_, 19, v___x_4038_);
lean_closure_set(v___f_4039_, 20, v___x_4026_);
lean_closure_set(v___f_4039_, 21, v___x_4013_);
lean_closure_set(v___f_4039_, 22, v_declName_4014_);
lean_closure_set(v___f_4039_, 23, v_levelParams_4015_);
lean_closure_set(v___f_4039_, 24, v___x_4016_);
lean_closure_set(v___f_4039_, 25, v___x_4017_);
lean_closure_set(v___f_4039_, 26, v_numParams_4018_);
lean_closure_set(v___f_4039_, 27, v_snd_4033_);
lean_closure_set(v___f_4039_, 28, v___x_4019_);
v___x_4040_ = 0;
v___x_4041_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_4032_, v___f_4039_, v___x_4040_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_);
return v___x_4041_;
}
else
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4049_; 
lean_dec_ref(v___x_4026_);
lean_dec_ref(v_motive_4020_);
lean_dec_ref(v___x_4019_);
lean_dec(v_numParams_4018_);
lean_dec(v___x_4017_);
lean_dec(v___x_4016_);
lean_dec(v_levelParams_4015_);
lean_dec(v_declName_4014_);
lean_dec_ref(v___x_4013_);
lean_dec_ref(v_val_4012_);
lean_dec_ref(v_heq_4011_);
lean_dec_ref(v___x_4010_);
lean_dec_ref(v___x_4009_);
lean_dec(v___x_4008_);
lean_dec(v___x_4007_);
lean_dec_ref(v___x_4006_);
lean_dec_ref(v___x_4005_);
lean_dec_ref(v_is_4004_);
lean_dec_ref(v___x_4000_);
lean_dec(v___x_3999_);
lean_dec(v_numIndices_3998_);
lean_dec_ref(v_params_3997_);
lean_dec(v_tail_3996_);
v_a_4042_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4049_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4049_ == 0)
{
v___x_4044_ = v___x_4029_;
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4029_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4049_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4047_; 
if (v_isShared_4045_ == 0)
{
v___x_4047_ = v___x_4044_;
goto v_reusejp_4046_;
}
else
{
lean_object* v_reuseFailAlloc_4048_; 
v_reuseFailAlloc_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4048_, 0, v_a_4042_);
v___x_4047_ = v_reuseFailAlloc_4048_;
goto v_reusejp_4046_;
}
v_reusejp_4046_:
{
return v___x_4047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4050_ = _args[0];
lean_object* v_tail_4051_ = _args[1];
lean_object* v_params_4052_ = _args[2];
lean_object* v_numIndices_4053_ = _args[3];
lean_object* v___x_4054_ = _args[4];
lean_object* v___x_4055_ = _args[5];
lean_object* v___x_4056_ = _args[6];
lean_object* v___x_4057_ = _args[7];
lean_object* v___x_4058_ = _args[8];
lean_object* v_is_4059_ = _args[9];
lean_object* v___x_4060_ = _args[10];
lean_object* v___x_4061_ = _args[11];
lean_object* v___x_4062_ = _args[12];
lean_object* v___x_4063_ = _args[13];
lean_object* v___x_4064_ = _args[14];
lean_object* v___x_4065_ = _args[15];
lean_object* v_heq_4066_ = _args[16];
lean_object* v_val_4067_ = _args[17];
lean_object* v___x_4068_ = _args[18];
lean_object* v_declName_4069_ = _args[19];
lean_object* v_levelParams_4070_ = _args[20];
lean_object* v___x_4071_ = _args[21];
lean_object* v___x_4072_ = _args[22];
lean_object* v_numParams_4073_ = _args[23];
lean_object* v___x_4074_ = _args[24];
lean_object* v_motive_4075_ = _args[25];
lean_object* v___y_4076_ = _args[26];
lean_object* v___y_4077_ = _args[27];
lean_object* v___y_4078_ = _args[28];
lean_object* v___y_4079_ = _args[29];
lean_object* v___y_4080_ = _args[30];
_start:
{
uint8_t v___x_16527__boxed_4081_; uint8_t v___x_16528__boxed_4082_; uint8_t v___x_16529__boxed_4083_; lean_object* v_res_4084_; 
v___x_16527__boxed_4081_ = lean_unbox(v___x_4056_);
v___x_16528__boxed_4082_ = lean_unbox(v___x_4057_);
v___x_16529__boxed_4083_ = lean_unbox(v___x_4058_);
v_res_4084_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4050_, v_tail_4051_, v_params_4052_, v_numIndices_4053_, v___x_4054_, v___x_4055_, v___x_16527__boxed_4081_, v___x_16528__boxed_4082_, v___x_16529__boxed_4083_, v_is_4059_, v___x_4060_, v___x_4061_, v___x_4062_, v___x_4063_, v___x_4064_, v___x_4065_, v_heq_4066_, v_val_4067_, v___x_4068_, v_declName_4069_, v_levelParams_4070_, v___x_4071_, v___x_4072_, v_numParams_4073_, v___x_4074_, v_motive_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec(v___y_4077_);
lean_dec_ref(v___y_4076_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4085_, lean_object* v___x_4086_, lean_object* v_is_4087_, lean_object* v_head_4088_, lean_object* v_ctors_4089_, lean_object* v_tail_4090_, lean_object* v_params_4091_, lean_object* v_numIndices_4092_, lean_object* v___x_4093_, lean_object* v___x_4094_, lean_object* v___x_4095_, lean_object* v___x_4096_, lean_object* v___x_4097_, lean_object* v_val_4098_, lean_object* v___x_4099_, lean_object* v_declName_4100_, lean_object* v_levelParams_4101_, lean_object* v___x_4102_, lean_object* v_numParams_4103_, lean_object* v___x_4104_, lean_object* v_heq_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; uint8_t v___x_4118_; uint8_t v___x_4119_; uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___f_4124_; lean_object* v___x_4125_; 
v___x_4111_ = lean_unsigned_to_nat(3u);
v___x_4112_ = lean_mk_empty_array_with_capacity(v___x_4111_);
lean_inc_ref(v___x_4085_);
v___x_4113_ = lean_array_push(v___x_4112_, v___x_4085_);
lean_inc_ref(v___x_4086_);
v___x_4114_ = lean_array_push(v___x_4113_, v___x_4086_);
lean_inc_ref(v_heq_4105_);
v___x_4115_ = lean_array_push(v___x_4114_, v_heq_4105_);
lean_inc_ref(v_is_4087_);
v___x_4116_ = l_Array_append___redArg(v_is_4087_, v___x_4115_);
lean_dec_ref(v___x_4115_);
v___x_4117_ = l_Lean_mkSort(v_head_4088_);
v___x_4118_ = 0;
v___x_4119_ = 1;
v___x_4120_ = 1;
v___x_4121_ = lean_box(v___x_4118_);
v___x_4122_ = lean_box(v___x_4119_);
v___x_4123_ = lean_box(v___x_4120_);
lean_inc_ref(v___x_4116_);
v___f_4124_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4124_, 0, v_ctors_4089_);
lean_closure_set(v___f_4124_, 1, v_tail_4090_);
lean_closure_set(v___f_4124_, 2, v_params_4091_);
lean_closure_set(v___f_4124_, 3, v_numIndices_4092_);
lean_closure_set(v___f_4124_, 4, v___x_4093_);
lean_closure_set(v___f_4124_, 5, v___x_4116_);
lean_closure_set(v___f_4124_, 6, v___x_4121_);
lean_closure_set(v___f_4124_, 7, v___x_4122_);
lean_closure_set(v___f_4124_, 8, v___x_4123_);
lean_closure_set(v___f_4124_, 9, v_is_4087_);
lean_closure_set(v___f_4124_, 10, v___x_4086_);
lean_closure_set(v___f_4124_, 11, v___x_4085_);
lean_closure_set(v___f_4124_, 12, v___x_4094_);
lean_closure_set(v___f_4124_, 13, v___x_4095_);
lean_closure_set(v___f_4124_, 14, v___x_4096_);
lean_closure_set(v___f_4124_, 15, v___x_4097_);
lean_closure_set(v___f_4124_, 16, v_heq_4105_);
lean_closure_set(v___f_4124_, 17, v_val_4098_);
lean_closure_set(v___f_4124_, 18, v___x_4099_);
lean_closure_set(v___f_4124_, 19, v_declName_4100_);
lean_closure_set(v___f_4124_, 20, v_levelParams_4101_);
lean_closure_set(v___f_4124_, 21, v___x_4111_);
lean_closure_set(v___f_4124_, 22, v___x_4102_);
lean_closure_set(v___f_4124_, 23, v_numParams_4103_);
lean_closure_set(v___f_4124_, 24, v___x_4104_);
v___x_4125_ = l_Lean_Meta_mkForallFVars(v___x_4116_, v___x_4117_, v___x_4118_, v___x_4119_, v___x_4119_, v___x_4120_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec_ref(v___x_4116_);
if (lean_obj_tag(v___x_4125_) == 0)
{
lean_object* v_a_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; lean_object* v___x_4129_; 
v_a_4126_ = lean_ctor_get(v___x_4125_, 0);
lean_inc(v_a_4126_);
lean_dec_ref_known(v___x_4125_, 1);
v___x_4127_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4128_ = 0;
v___x_4129_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4127_, v___x_4120_, v_a_4126_, v___f_4124_, v___x_4128_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
return v___x_4129_;
}
else
{
lean_object* v_a_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
lean_dec_ref(v___f_4124_);
v_a_4130_ = lean_ctor_get(v___x_4125_, 0);
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4125_);
if (v_isSharedCheck_4137_ == 0)
{
v___x_4132_ = v___x_4125_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_a_4130_);
lean_dec(v___x_4125_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v_a_4130_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4138_ = _args[0];
lean_object* v___x_4139_ = _args[1];
lean_object* v_is_4140_ = _args[2];
lean_object* v_head_4141_ = _args[3];
lean_object* v_ctors_4142_ = _args[4];
lean_object* v_tail_4143_ = _args[5];
lean_object* v_params_4144_ = _args[6];
lean_object* v_numIndices_4145_ = _args[7];
lean_object* v___x_4146_ = _args[8];
lean_object* v___x_4147_ = _args[9];
lean_object* v___x_4148_ = _args[10];
lean_object* v___x_4149_ = _args[11];
lean_object* v___x_4150_ = _args[12];
lean_object* v_val_4151_ = _args[13];
lean_object* v___x_4152_ = _args[14];
lean_object* v_declName_4153_ = _args[15];
lean_object* v_levelParams_4154_ = _args[16];
lean_object* v___x_4155_ = _args[17];
lean_object* v_numParams_4156_ = _args[18];
lean_object* v___x_4157_ = _args[19];
lean_object* v_heq_4158_ = _args[20];
lean_object* v___y_4159_ = _args[21];
lean_object* v___y_4160_ = _args[22];
lean_object* v___y_4161_ = _args[23];
lean_object* v___y_4162_ = _args[24];
lean_object* v___y_4163_ = _args[25];
_start:
{
lean_object* v_res_4164_; 
v_res_4164_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4138_, v___x_4139_, v_is_4140_, v_head_4141_, v_ctors_4142_, v_tail_4143_, v_params_4144_, v_numIndices_4145_, v___x_4146_, v___x_4147_, v___x_4148_, v___x_4149_, v___x_4150_, v_val_4151_, v___x_4152_, v_declName_4153_, v_levelParams_4154_, v___x_4155_, v_numParams_4156_, v___x_4157_, v_heq_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4165_, lean_object* v_x1_4166_, lean_object* v_indName_4167_, lean_object* v_tail_4168_, lean_object* v_params_4169_, lean_object* v_is_4170_, lean_object* v___x_4171_, lean_object* v_head_4172_, lean_object* v_ctors_4173_, lean_object* v_numIndices_4174_, lean_object* v___x_4175_, lean_object* v___x_4176_, lean_object* v_val_4177_, lean_object* v_declName_4178_, lean_object* v_levelParams_4179_, lean_object* v_numParams_4180_, lean_object* v___x_4181_, lean_object* v_x2_4182_, lean_object* v_x_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___f_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4189_ = lean_unsigned_to_nat(0u);
v___x_4190_ = lean_array_get_borrowed(v___x_4165_, v_x1_4166_, v___x_4189_);
v___x_4191_ = lean_array_get_borrowed(v___x_4165_, v_x2_4182_, v___x_4189_);
v___x_4192_ = l_Lean_mkCtorIdxName(v_indName_4167_);
lean_inc(v_tail_4168_);
v___x_4193_ = l_Lean_mkConst(v___x_4192_, v_tail_4168_);
lean_inc_ref(v_params_4169_);
v___x_4194_ = l_Array_append___redArg(v_params_4169_, v_is_4170_);
v___x_4195_ = lean_mk_empty_array_with_capacity(v___x_4171_);
lean_inc_n(v___x_4190_, 2);
lean_inc_ref_n(v___x_4195_, 2);
v___x_4196_ = lean_array_push(v___x_4195_, v___x_4190_);
lean_inc_ref(v___x_4194_);
v___x_4197_ = l_Array_append___redArg(v___x_4194_, v___x_4196_);
lean_inc_ref(v___x_4193_);
v___x_4198_ = l_Lean_mkAppN(v___x_4193_, v___x_4197_);
lean_dec_ref(v___x_4197_);
lean_inc_n(v___x_4191_, 2);
v___x_4199_ = lean_array_push(v___x_4195_, v___x_4191_);
lean_inc_ref(v___x_4199_);
v___f_4200_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4200_, 0, v___x_4190_);
lean_closure_set(v___f_4200_, 1, v___x_4191_);
lean_closure_set(v___f_4200_, 2, v_is_4170_);
lean_closure_set(v___f_4200_, 3, v_head_4172_);
lean_closure_set(v___f_4200_, 4, v_ctors_4173_);
lean_closure_set(v___f_4200_, 5, v_tail_4168_);
lean_closure_set(v___f_4200_, 6, v_params_4169_);
lean_closure_set(v___f_4200_, 7, v_numIndices_4174_);
lean_closure_set(v___f_4200_, 8, v___x_4171_);
lean_closure_set(v___f_4200_, 9, v___x_4175_);
lean_closure_set(v___f_4200_, 10, v___x_4176_);
lean_closure_set(v___f_4200_, 11, v___x_4196_);
lean_closure_set(v___f_4200_, 12, v___x_4199_);
lean_closure_set(v___f_4200_, 13, v_val_4177_);
lean_closure_set(v___f_4200_, 14, v___x_4195_);
lean_closure_set(v___f_4200_, 15, v_declName_4178_);
lean_closure_set(v___f_4200_, 16, v_levelParams_4179_);
lean_closure_set(v___f_4200_, 17, v___x_4189_);
lean_closure_set(v___f_4200_, 18, v_numParams_4180_);
lean_closure_set(v___f_4200_, 19, v___x_4181_);
v___x_4201_ = l_Array_append___redArg(v___x_4194_, v___x_4199_);
lean_dec_ref(v___x_4199_);
v___x_4202_ = l_Lean_mkAppN(v___x_4193_, v___x_4201_);
lean_dec_ref(v___x_4201_);
v___x_4203_ = l_Lean_Meta_mkEq(v___x_4198_, v___x_4202_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v___x_4205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4206_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4205_, v_a_4204_, v___f_4200_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
return v___x_4206_;
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec_ref(v___f_4200_);
v_a_4207_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4203_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4203_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4215_ = _args[0];
lean_object* v_x1_4216_ = _args[1];
lean_object* v_indName_4217_ = _args[2];
lean_object* v_tail_4218_ = _args[3];
lean_object* v_params_4219_ = _args[4];
lean_object* v_is_4220_ = _args[5];
lean_object* v___x_4221_ = _args[6];
lean_object* v_head_4222_ = _args[7];
lean_object* v_ctors_4223_ = _args[8];
lean_object* v_numIndices_4224_ = _args[9];
lean_object* v___x_4225_ = _args[10];
lean_object* v___x_4226_ = _args[11];
lean_object* v_val_4227_ = _args[12];
lean_object* v_declName_4228_ = _args[13];
lean_object* v_levelParams_4229_ = _args[14];
lean_object* v_numParams_4230_ = _args[15];
lean_object* v___x_4231_ = _args[16];
lean_object* v_x2_4232_ = _args[17];
lean_object* v_x_4233_ = _args[18];
lean_object* v___y_4234_ = _args[19];
lean_object* v___y_4235_ = _args[20];
lean_object* v___y_4236_ = _args[21];
lean_object* v___y_4237_ = _args[22];
lean_object* v___y_4238_ = _args[23];
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4215_, v_x1_4216_, v_indName_4217_, v_tail_4218_, v_params_4219_, v_is_4220_, v___x_4221_, v_head_4222_, v_ctors_4223_, v_numIndices_4224_, v___x_4225_, v___x_4226_, v_val_4227_, v_declName_4228_, v_levelParams_4229_, v_numParams_4230_, v___x_4231_, v_x2_4232_, v_x_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec_ref(v_x_4233_);
lean_dec_ref(v_x2_4232_);
lean_dec_ref(v_x1_4216_);
lean_dec_ref(v___x_4215_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4240_, lean_object* v_indName_4241_, lean_object* v_tail_4242_, lean_object* v_params_4243_, lean_object* v_is_4244_, lean_object* v___x_4245_, lean_object* v_head_4246_, lean_object* v_ctors_4247_, lean_object* v_numIndices_4248_, lean_object* v___x_4249_, lean_object* v___x_4250_, lean_object* v_val_4251_, lean_object* v_declName_4252_, lean_object* v_levelParams_4253_, lean_object* v_numParams_4254_, lean_object* v___x_4255_, lean_object* v_t_4256_, lean_object* v___x_4257_, lean_object* v_x1_4258_, lean_object* v_x_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___f_4265_; uint8_t v___x_4266_; lean_object* v___x_4267_; 
v___f_4265_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4265_, 0, v___x_4240_);
lean_closure_set(v___f_4265_, 1, v_x1_4258_);
lean_closure_set(v___f_4265_, 2, v_indName_4241_);
lean_closure_set(v___f_4265_, 3, v_tail_4242_);
lean_closure_set(v___f_4265_, 4, v_params_4243_);
lean_closure_set(v___f_4265_, 5, v_is_4244_);
lean_closure_set(v___f_4265_, 6, v___x_4245_);
lean_closure_set(v___f_4265_, 7, v_head_4246_);
lean_closure_set(v___f_4265_, 8, v_ctors_4247_);
lean_closure_set(v___f_4265_, 9, v_numIndices_4248_);
lean_closure_set(v___f_4265_, 10, v___x_4249_);
lean_closure_set(v___f_4265_, 11, v___x_4250_);
lean_closure_set(v___f_4265_, 12, v_val_4251_);
lean_closure_set(v___f_4265_, 13, v_declName_4252_);
lean_closure_set(v___f_4265_, 14, v_levelParams_4253_);
lean_closure_set(v___f_4265_, 15, v_numParams_4254_);
lean_closure_set(v___f_4265_, 16, v___x_4255_);
v___x_4266_ = 0;
v___x_4267_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4256_, v___x_4257_, v___f_4265_, v___x_4266_, v___x_4266_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4268_ = _args[0];
lean_object* v_indName_4269_ = _args[1];
lean_object* v_tail_4270_ = _args[2];
lean_object* v_params_4271_ = _args[3];
lean_object* v_is_4272_ = _args[4];
lean_object* v___x_4273_ = _args[5];
lean_object* v_head_4274_ = _args[6];
lean_object* v_ctors_4275_ = _args[7];
lean_object* v_numIndices_4276_ = _args[8];
lean_object* v___x_4277_ = _args[9];
lean_object* v___x_4278_ = _args[10];
lean_object* v_val_4279_ = _args[11];
lean_object* v_declName_4280_ = _args[12];
lean_object* v_levelParams_4281_ = _args[13];
lean_object* v_numParams_4282_ = _args[14];
lean_object* v___x_4283_ = _args[15];
lean_object* v_t_4284_ = _args[16];
lean_object* v___x_4285_ = _args[17];
lean_object* v_x1_4286_ = _args[18];
lean_object* v_x_4287_ = _args[19];
lean_object* v___y_4288_ = _args[20];
lean_object* v___y_4289_ = _args[21];
lean_object* v___y_4290_ = _args[22];
lean_object* v___y_4291_ = _args[23];
lean_object* v___y_4292_ = _args[24];
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4268_, v_indName_4269_, v_tail_4270_, v_params_4271_, v_is_4272_, v___x_4273_, v_head_4274_, v_ctors_4275_, v_numIndices_4276_, v___x_4277_, v___x_4278_, v_val_4279_, v_declName_4280_, v_levelParams_4281_, v_numParams_4282_, v___x_4283_, v_t_4284_, v___x_4285_, v_x1_4286_, v_x_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec_ref(v_x_4287_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4294_, lean_object* v_indName_4295_, lean_object* v_tail_4296_, lean_object* v_params_4297_, lean_object* v_head_4298_, lean_object* v_ctors_4299_, lean_object* v_numIndices_4300_, lean_object* v___x_4301_, lean_object* v___x_4302_, lean_object* v_val_4303_, lean_object* v_declName_4304_, lean_object* v_levelParams_4305_, lean_object* v_numParams_4306_, lean_object* v___x_4307_, lean_object* v_is_4308_, lean_object* v_t_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___f_4317_; uint8_t v___x_4318_; lean_object* v___x_4319_; 
v___x_4315_ = lean_unsigned_to_nat(1u);
v___x_4316_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4309_);
v___f_4317_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4317_, 0, v___x_4294_);
lean_closure_set(v___f_4317_, 1, v_indName_4295_);
lean_closure_set(v___f_4317_, 2, v_tail_4296_);
lean_closure_set(v___f_4317_, 3, v_params_4297_);
lean_closure_set(v___f_4317_, 4, v_is_4308_);
lean_closure_set(v___f_4317_, 5, v___x_4315_);
lean_closure_set(v___f_4317_, 6, v_head_4298_);
lean_closure_set(v___f_4317_, 7, v_ctors_4299_);
lean_closure_set(v___f_4317_, 8, v_numIndices_4300_);
lean_closure_set(v___f_4317_, 9, v___x_4301_);
lean_closure_set(v___f_4317_, 10, v___x_4302_);
lean_closure_set(v___f_4317_, 11, v_val_4303_);
lean_closure_set(v___f_4317_, 12, v_declName_4304_);
lean_closure_set(v___f_4317_, 13, v_levelParams_4305_);
lean_closure_set(v___f_4317_, 14, v_numParams_4306_);
lean_closure_set(v___f_4317_, 15, v___x_4307_);
lean_closure_set(v___f_4317_, 16, v_t_4309_);
lean_closure_set(v___f_4317_, 17, v___x_4316_);
v___x_4318_ = 0;
v___x_4319_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4309_, v___x_4316_, v___f_4317_, v___x_4318_, v___x_4318_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_);
return v___x_4319_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4320_ = _args[0];
lean_object* v_indName_4321_ = _args[1];
lean_object* v_tail_4322_ = _args[2];
lean_object* v_params_4323_ = _args[3];
lean_object* v_head_4324_ = _args[4];
lean_object* v_ctors_4325_ = _args[5];
lean_object* v_numIndices_4326_ = _args[6];
lean_object* v___x_4327_ = _args[7];
lean_object* v___x_4328_ = _args[8];
lean_object* v_val_4329_ = _args[9];
lean_object* v_declName_4330_ = _args[10];
lean_object* v_levelParams_4331_ = _args[11];
lean_object* v_numParams_4332_ = _args[12];
lean_object* v___x_4333_ = _args[13];
lean_object* v_is_4334_ = _args[14];
lean_object* v_t_4335_ = _args[15];
lean_object* v___y_4336_ = _args[16];
lean_object* v___y_4337_ = _args[17];
lean_object* v___y_4338_ = _args[18];
lean_object* v___y_4339_ = _args[19];
lean_object* v___y_4340_ = _args[20];
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4320_, v_indName_4321_, v_tail_4322_, v_params_4323_, v_head_4324_, v_ctors_4325_, v_numIndices_4326_, v___x_4327_, v___x_4328_, v_val_4329_, v_declName_4330_, v_levelParams_4331_, v_numParams_4332_, v___x_4333_, v_is_4334_, v_t_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4342_, lean_object* v_indName_4343_, lean_object* v_tail_4344_, lean_object* v_head_4345_, lean_object* v_ctors_4346_, lean_object* v_numIndices_4347_, lean_object* v___x_4348_, lean_object* v___x_4349_, lean_object* v_val_4350_, lean_object* v_declName_4351_, lean_object* v_levelParams_4352_, lean_object* v_numParams_4353_, lean_object* v_params_4354_, lean_object* v_t_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v___x_4361_; lean_object* v___f_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; lean_object* v___x_4365_; 
v___x_4361_ = l_Lean_Expr_bindingBody_x21(v_t_4355_);
lean_inc_ref(v___x_4361_);
lean_inc(v_numIndices_4347_);
v___f_4362_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4362_, 0, v___x_4342_);
lean_closure_set(v___f_4362_, 1, v_indName_4343_);
lean_closure_set(v___f_4362_, 2, v_tail_4344_);
lean_closure_set(v___f_4362_, 3, v_params_4354_);
lean_closure_set(v___f_4362_, 4, v_head_4345_);
lean_closure_set(v___f_4362_, 5, v_ctors_4346_);
lean_closure_set(v___f_4362_, 6, v_numIndices_4347_);
lean_closure_set(v___f_4362_, 7, v___x_4348_);
lean_closure_set(v___f_4362_, 8, v___x_4349_);
lean_closure_set(v___f_4362_, 9, v_val_4350_);
lean_closure_set(v___f_4362_, 10, v_declName_4351_);
lean_closure_set(v___f_4362_, 11, v_levelParams_4352_);
lean_closure_set(v___f_4362_, 12, v_numParams_4353_);
lean_closure_set(v___f_4362_, 13, v___x_4361_);
v___x_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4363_, 0, v_numIndices_4347_);
v___x_4364_ = 0;
v___x_4365_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4361_, v___x_4363_, v___f_4362_, v___x_4364_, v___x_4364_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4366_ = _args[0];
lean_object* v_indName_4367_ = _args[1];
lean_object* v_tail_4368_ = _args[2];
lean_object* v_head_4369_ = _args[3];
lean_object* v_ctors_4370_ = _args[4];
lean_object* v_numIndices_4371_ = _args[5];
lean_object* v___x_4372_ = _args[6];
lean_object* v___x_4373_ = _args[7];
lean_object* v_val_4374_ = _args[8];
lean_object* v_declName_4375_ = _args[9];
lean_object* v_levelParams_4376_ = _args[10];
lean_object* v_numParams_4377_ = _args[11];
lean_object* v_params_4378_ = _args[12];
lean_object* v_t_4379_ = _args[13];
lean_object* v___y_4380_ = _args[14];
lean_object* v___y_4381_ = _args[15];
lean_object* v___y_4382_ = _args[16];
lean_object* v___y_4383_ = _args[17];
lean_object* v___y_4384_ = _args[18];
_start:
{
lean_object* v_res_4385_; 
v_res_4385_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4366_, v_indName_4367_, v_tail_4368_, v_head_4369_, v_ctors_4370_, v_numIndices_4371_, v___x_4372_, v___x_4373_, v_val_4374_, v_declName_4375_, v_levelParams_4376_, v_numParams_4377_, v_params_4378_, v_t_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
lean_dec(v___y_4381_);
lean_dec_ref(v___y_4380_);
lean_dec_ref(v_t_4379_);
return v_res_4385_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4390_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4391_ = lean_unsigned_to_nat(58u);
v___x_4392_ = lean_unsigned_to_nat(142u);
v___x_4393_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4394_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4395_ = l_mkPanicMessageWithDecl(v___x_4394_, v___x_4393_, v___x_4392_, v___x_4391_, v___x_4390_);
return v___x_4395_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4396_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4397_ = lean_unsigned_to_nat(60u);
v___x_4398_ = lean_unsigned_to_nat(136u);
v___x_4399_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4400_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4401_ = l_mkPanicMessageWithDecl(v___x_4400_, v___x_4399_, v___x_4398_, v___x_4397_, v___x_4396_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4402_, lean_object* v_indName_4403_, lean_object* v_a_4404_, lean_object* v_a_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4409_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_4403_);
v___x_4410_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
if (lean_obj_tag(v_a_4411_) == 5)
{
lean_object* v_val_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v_val_4412_ = lean_ctor_get(v_a_4411_, 0);
lean_inc_ref(v_val_4412_);
lean_dec_ref_known(v_a_4411_, 1);
v___x_4413_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4402_);
v___x_4414_ = l_Lean_Name_append(v_declName_4402_, v___x_4413_);
lean_inc(v_indName_4403_);
lean_inc(v___x_4414_);
v___x_4415_ = l_Lean_mkCasesOnSameCtorHet(v___x_4414_, v_indName_4403_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4447_; 
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4447_ == 0)
{
lean_object* v_unused_4448_; 
v_unused_4448_ = lean_ctor_get(v___x_4415_, 0);
lean_dec(v_unused_4448_);
v___x_4417_ = v___x_4415_;
v_isShared_4418_ = v_isSharedCheck_4447_;
goto v_resetjp_4416_;
}
else
{
lean_dec(v___x_4415_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4447_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4419_; lean_object* v___x_4420_; 
lean_inc(v_indName_4403_);
v___x_4419_ = l_Lean_mkCasesOnName(v_indName_4403_);
v___x_4420_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4419_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v_levelParams_4422_; lean_object* v_type_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref_known(v___x_4420_, 1);
v_levelParams_4422_ = lean_ctor_get(v_a_4421_, 1);
lean_inc_n(v_levelParams_4422_, 2);
v_type_4423_ = lean_ctor_get(v_a_4421_, 2);
lean_inc_ref(v_type_4423_);
lean_dec(v_a_4421_);
v___x_4424_ = lean_box(0);
v___x_4425_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4422_, v___x_4424_);
if (lean_obj_tag(v___x_4425_) == 1)
{
lean_object* v_head_4426_; lean_object* v_tail_4427_; lean_object* v_numParams_4428_; lean_object* v_numIndices_4429_; lean_object* v_ctors_4430_; lean_object* v___f_4431_; lean_object* v___x_4433_; 
v_head_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_head_4426_);
v_tail_4427_ = lean_ctor_get(v___x_4425_, 1);
lean_inc(v_tail_4427_);
v_numParams_4428_ = lean_ctor_get(v_val_4412_, 1);
lean_inc_n(v_numParams_4428_, 2);
v_numIndices_4429_ = lean_ctor_get(v_val_4412_, 2);
lean_inc(v_numIndices_4429_);
v_ctors_4430_ = lean_ctor_get(v_val_4412_, 4);
lean_inc(v_ctors_4430_);
v___f_4431_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4431_, 0, v___x_4409_);
lean_closure_set(v___f_4431_, 1, v_indName_4403_);
lean_closure_set(v___f_4431_, 2, v_tail_4427_);
lean_closure_set(v___f_4431_, 3, v_head_4426_);
lean_closure_set(v___f_4431_, 4, v_ctors_4430_);
lean_closure_set(v___f_4431_, 5, v_numIndices_4429_);
lean_closure_set(v___f_4431_, 6, v___x_4414_);
lean_closure_set(v___f_4431_, 7, v___x_4425_);
lean_closure_set(v___f_4431_, 8, v_val_4412_);
lean_closure_set(v___f_4431_, 9, v_declName_4402_);
lean_closure_set(v___f_4431_, 10, v_levelParams_4422_);
lean_closure_set(v___f_4431_, 11, v_numParams_4428_);
if (v_isShared_4418_ == 0)
{
lean_ctor_set_tag(v___x_4417_, 1);
lean_ctor_set(v___x_4417_, 0, v_numParams_4428_);
v___x_4433_ = v___x_4417_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_numParams_4428_);
v___x_4433_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
uint8_t v___x_4434_; lean_object* v___x_4435_; 
v___x_4434_ = 0;
v___x_4435_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4423_, v___x_4433_, v___f_4431_, v___x_4434_, v___x_4434_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
return v___x_4435_;
}
}
else
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
lean_dec(v___x_4425_);
lean_dec_ref(v_type_4423_);
lean_dec(v_levelParams_4422_);
lean_del_object(v___x_4417_);
lean_dec(v___x_4414_);
lean_dec_ref(v_val_4412_);
lean_dec(v_indName_4403_);
lean_dec(v_declName_4402_);
v___x_4437_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4438_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4437_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
return v___x_4438_;
}
}
else
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4446_; 
lean_del_object(v___x_4417_);
lean_dec(v___x_4414_);
lean_dec_ref(v_val_4412_);
lean_dec(v_indName_4403_);
lean_dec(v_declName_4402_);
v_a_4439_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4446_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4446_ == 0)
{
v___x_4441_ = v___x_4420_;
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4420_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4446_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4444_; 
if (v_isShared_4442_ == 0)
{
v___x_4444_ = v___x_4441_;
goto v_reusejp_4443_;
}
else
{
lean_object* v_reuseFailAlloc_4445_; 
v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4445_, 0, v_a_4439_);
v___x_4444_ = v_reuseFailAlloc_4445_;
goto v_reusejp_4443_;
}
v_reusejp_4443_:
{
return v___x_4444_;
}
}
}
}
}
else
{
lean_dec(v___x_4414_);
lean_dec_ref(v_val_4412_);
lean_dec(v_indName_4403_);
lean_dec(v_declName_4402_);
return v___x_4415_;
}
}
else
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_dec(v_a_4411_);
lean_dec(v_indName_4403_);
lean_dec(v_declName_4402_);
v___x_4449_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4450_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4449_, v_a_4404_, v_a_4405_, v_a_4406_, v_a_4407_);
return v___x_4450_;
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec(v_indName_4403_);
lean_dec(v_declName_4402_);
v_a_4451_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4410_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4410_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4459_, lean_object* v_indName_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_){
_start:
{
lean_object* v_res_4466_; 
v_res_4466_ = l_Lean_mkCasesOnSameCtor(v_declName_4459_, v_indName_4460_, v_a_4461_, v_a_4462_, v_a_4463_, v_a_4464_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
lean_dec(v_a_4462_);
lean_dec_ref(v_a_4461_);
return v_res_4466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4467_, lean_object* v_params_4468_, lean_object* v_motive_4469_, lean_object* v_as_4470_, size_t v_sz_4471_, size_t v_i_4472_, lean_object* v_bs_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4467_, v_params_4468_, v_motive_4469_, v_sz_4471_, v_i_4472_, v_bs_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4480_, lean_object* v_params_4481_, lean_object* v_motive_4482_, lean_object* v_as_4483_, lean_object* v_sz_4484_, lean_object* v_i_4485_, lean_object* v_bs_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
size_t v_sz_boxed_4492_; size_t v_i_boxed_4493_; lean_object* v_res_4494_; 
v_sz_boxed_4492_ = lean_unbox_usize(v_sz_4484_);
lean_dec(v_sz_4484_);
v_i_boxed_4493_ = lean_unbox_usize(v_i_4485_);
lean_dec(v_i_4485_);
v_res_4494_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4480_, v_params_4481_, v_motive_4482_, v_as_4483_, v_sz_boxed_4492_, v_i_boxed_4493_, v_bs_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec_ref(v_as_4483_);
lean_dec_ref(v_params_4481_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4495_, lean_object* v_params_4496_, lean_object* v_a_4497_, lean_object* v_snd_4498_, lean_object* v_alts_4499_, lean_object* v_as_4500_, size_t v_sz_4501_, size_t v_i_4502_, lean_object* v_bs_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v___x_4509_; 
v___x_4509_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4495_, v_params_4496_, v_a_4497_, v_snd_4498_, v_alts_4499_, v_sz_4501_, v_i_4502_, v_bs_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
return v___x_4509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4510_, lean_object* v_params_4511_, lean_object* v_a_4512_, lean_object* v_snd_4513_, lean_object* v_alts_4514_, lean_object* v_as_4515_, lean_object* v_sz_4516_, lean_object* v_i_4517_, lean_object* v_bs_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
size_t v_sz_boxed_4524_; size_t v_i_boxed_4525_; lean_object* v_res_4526_; 
v_sz_boxed_4524_ = lean_unbox_usize(v_sz_4516_);
lean_dec(v_sz_4516_);
v_i_boxed_4525_ = lean_unbox_usize(v_i_4517_);
lean_dec(v_i_4517_);
v_res_4526_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4510_, v_params_4511_, v_a_4512_, v_snd_4513_, v_alts_4514_, v_as_4515_, v_sz_boxed_4524_, v_i_boxed_4525_, v_bs_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec_ref(v_as_4515_);
lean_dec_ref(v_params_4511_);
return v_res_4526_;
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
