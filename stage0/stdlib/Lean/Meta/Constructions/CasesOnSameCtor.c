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
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v_isExporting_351_ = lean_ctor_get_uint8(v_env_347_, sizeof(void*)*8);
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
lean_object* v___f_455_; lean_object* v___x_15724__overap_456_; lean_object* v___x_457_; 
v___f_455_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15724__overap_456_ = lean_panic_fn_borrowed(v___f_455_, v_msg_449_);
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
v___x_457_ = lean_apply_5(v___x_15724__overap_456_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, lean_box(0));
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
uint8_t v___x_20754__boxed_561_; uint8_t v___x_20755__boxed_562_; uint8_t v___x_20756__boxed_563_; lean_object* v_res_564_; 
v___x_20754__boxed_561_ = lean_unbox(v___x_542_);
v___x_20755__boxed_562_ = lean_unbox(v___x_543_);
v___x_20756__boxed_563_ = lean_unbox(v___x_544_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_539_, v_ism2_540_, v_motive_541_, v___x_20754__boxed_561_, v___x_20755__boxed_562_, v___x_20756__boxed_563_, v_a_545_, v___f_546_, v_zs1_547_, v_val_548_, v___x_549_, v_indName_550_, v_v_551_, v___x_552_, v_params_553_, v___x_554_, v_h_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
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
uint8_t v___x_20866__boxed_597_; uint8_t v___x_20867__boxed_598_; uint8_t v___x_20868__boxed_599_; lean_object* v_res_600_; 
v___x_20866__boxed_597_ = lean_unbox(v___x_587_);
v___x_20867__boxed_598_ = lean_unbox(v___x_588_);
v___x_20868__boxed_599_ = lean_unbox(v___x_589_);
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_583_, v_alts_584_, v___x_585_, v_zs1_586_, v___x_20866__boxed_597_, v___x_20867__boxed_598_, v___x_20868__boxed_599_, v_zs2_590_, v_x_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
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
uint8_t v___x_20927__boxed_695_; uint8_t v___x_20928__boxed_696_; uint8_t v___x_20929__boxed_697_; lean_object* v_res_698_; 
v___x_20927__boxed_695_ = lean_unbox(v___x_671_);
v___x_20928__boxed_696_ = lean_unbox(v___x_672_);
v___x_20929__boxed_697_ = lean_unbox(v___x_673_);
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_668_, v_alts_669_, v___x_670_, v___x_20927__boxed_695_, v___x_20928__boxed_696_, v___x_20929__boxed_697_, v___x_674_, v___x_675_, v___x_676_, v_ism2_677_, v_motive_678_, v_a_679_, v_val_680_, v_indName_681_, v_v_682_, v___x_683_, v_params_684_, v___x_685_, v___x_686_, v___x_687_, v_zs1_688_, v_ctorRet1_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
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
uint8_t v___x_21158__boxed_864_; uint8_t v___x_21159__boxed_865_; uint8_t v___x_21160__boxed_866_; lean_object* v_res_867_; 
v___x_21158__boxed_864_ = lean_unbox(v___x_842_);
v___x_21159__boxed_865_ = lean_unbox(v___x_843_);
v___x_21160__boxed_866_ = lean_unbox(v___x_844_);
v_res_867_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_838_, v___x_839_, v_a_840_, v_ism1_841_, v___x_21158__boxed_864_, v___x_21159__boxed_865_, v___x_21160__boxed_866_, v_name_845_, v___x_846_, v_params_847_, v___x_848_, v_tail_849_, v_alts_850_, v_numParams_851_, v_ism2_852_, v_val_853_, v_indName_854_, v___x_855_, v___x_856_, v___x_857_, v_heq_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
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
uint8_t v___x_21281__boxed_930_; uint8_t v___x_21282__boxed_931_; uint8_t v___x_21283__boxed_932_; lean_object* v_res_933_; 
v___x_21281__boxed_930_ = lean_unbox(v___x_914_);
v___x_21282__boxed_931_ = lean_unbox(v___x_915_);
v___x_21283__boxed_932_ = lean_unbox(v___x_916_);
v_res_933_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_907_, v_tail_908_, v_params_909_, v_ism1_910_, v_ism2_911_, v_motive_912_, v___x_913_, v___x_21281__boxed_930_, v___x_21282__boxed_931_, v___x_21283__boxed_932_, v_name_917_, v___x_918_, v___x_919_, v_numParams_920_, v_val_921_, v___x_922_, v___x_923_, v_alts_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
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
lean_object* v___x_20165__overap_985_; lean_object* v___x_986_; 
v___x_20165__overap_985_ = l_instInhabitedOfMonad___redArg(v___x_977_, v___x_978_);
lean_inc(v___y_983_);
lean_inc_ref(v___y_982_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
v___x_986_ = lean_apply_5(v___x_20165__overap_985_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, lean_box(0));
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
uint8_t v___x_21720__boxed_1301_; uint8_t v___x_21721__boxed_1302_; uint8_t v___x_21722__boxed_1303_; lean_object* v_res_1304_; 
v___x_21720__boxed_1301_ = lean_unbox(v___x_1289_);
v___x_21721__boxed_1302_ = lean_unbox(v___x_1290_);
v___x_21722__boxed_1303_ = lean_unbox(v___x_1291_);
v_res_1304_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1282_, v_dummy_1283_, v___x_1284_, v___x_1285_, v___x_1286_, v_motive_1287_, v_zs1_1288_, v___x_21720__boxed_1301_, v___x_21721__boxed_1302_, v___x_21722__boxed_1303_, v_v_1292_, v___x_1293_, v_zs2_1294_, v_ctorRet2_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
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
uint8_t v___x_21861__boxed_1364_; uint8_t v___x_21862__boxed_1365_; uint8_t v___x_21863__boxed_1366_; lean_object* v_res_1367_; 
v___x_21861__boxed_1364_ = lean_unbox(v___x_1351_);
v___x_21862__boxed_1365_ = lean_unbox(v___x_1352_);
v___x_21863__boxed_1366_ = lean_unbox(v___x_1353_);
v_res_1367_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1347_, v___x_1348_, v___x_1349_, v_motive_1350_, v___x_21861__boxed_1364_, v___x_21862__boxed_1365_, v___x_21863__boxed_1366_, v_v_1354_, v___x_1355_, v_a_1356_, v_zs1_1357_, v_ctorRet1_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
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
uint8_t v___x_22041__boxed_1497_; uint8_t v___x_22042__boxed_1498_; uint8_t v___x_22043__boxed_1499_; lean_object* v_res_1500_; 
v___x_22041__boxed_1497_ = lean_unbox(v___x_1482_);
v___x_22042__boxed_1498_ = lean_unbox(v___x_1483_);
v___x_22043__boxed_1499_ = lean_unbox(v___x_1484_);
v_res_1500_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1475_, v_indName_1476_, v_tail_1477_, v_params_1478_, v_ism1_1479_, v_ism2_1480_, v___x_1481_, v___x_22041__boxed_1497_, v___x_22042__boxed_1498_, v___x_22043__boxed_1499_, v_name_1485_, v___x_1486_, v_numParams_1487_, v_val_1488_, v___x_1489_, v___x_1490_, v_motive_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_);
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
uint8_t v___x_22329__boxed_1726_; lean_object* v_res_1727_; 
v___x_22329__boxed_1726_ = lean_unbox(v___x_1720_);
v_res_1727_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1717_, v_declName_1718_, v_levelParams_1719_, v___x_22329__boxed_1726_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
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
lean_object* v___x_1748_; lean_object* v_env_1749_; lean_object* v___x_1750_; lean_object* v_toCold_1751_; lean_object* v_mctx_1752_; lean_object* v_lctx_1753_; lean_object* v_options_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1748_ = lean_st_ref_get(v___y_1746_);
v_env_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc_ref(v_env_1749_);
lean_dec(v___x_1748_);
v___x_1750_ = lean_st_ref_get(v___y_1744_);
v_toCold_1751_ = lean_ctor_get(v___y_1745_, 0);
v_mctx_1752_ = lean_ctor_get(v___x_1750_, 0);
lean_inc_ref(v_mctx_1752_);
lean_dec(v___x_1750_);
v_lctx_1753_ = lean_ctor_get(v___y_1743_, 2);
v_options_1754_ = lean_ctor_get(v_toCold_1751_, 2);
lean_inc_ref(v_options_1754_);
lean_inc_ref(v_lctx_1753_);
v___x_1755_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1755_, 0, v_env_1749_);
lean_ctor_set(v___x_1755_, 1, v_mctx_1752_);
lean_ctor_set(v___x_1755_, 2, v_lctx_1753_);
lean_ctor_set(v___x_1755_, 3, v_options_1754_);
v___x_1756_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
lean_ctor_set(v___x_1756_, 1, v_msgData_1742_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_){
_start:
{
lean_object* v_ref_1771_; lean_object* v___x_1772_; lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1781_; 
v_ref_1771_ = lean_ctor_get(v___y_1768_, 2);
v___x_1772_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_);
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1772_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1775_ = v___x_1772_;
v_isShared_1776_ = v_isSharedCheck_1781_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1772_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1781_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
lean_inc(v_ref_1771_);
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v_ref_1771_);
lean_ctor_set(v___x_1777_, 1, v_a_1773_);
if (v_isShared_1776_ == 0)
{
lean_ctor_set_tag(v___x_1775_, 1);
lean_ctor_set(v___x_1775_, 0, v___x_1777_);
v___x_1779_ = v___x_1775_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1789_, lean_object* v_msg_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v_toCold_1796_; lean_object* v_currRecDepth_1797_; lean_object* v_ref_1798_; uint16_t v_optionFlags_1799_; uint8_t v_suppressElabErrors_1800_; uint8_t v_isRecordingDeps_1801_; lean_object* v_ref_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v_toCold_1796_ = lean_ctor_get(v___y_1793_, 0);
v_currRecDepth_1797_ = lean_ctor_get(v___y_1793_, 1);
v_ref_1798_ = lean_ctor_get(v___y_1793_, 2);
v_optionFlags_1799_ = lean_ctor_get_uint16(v___y_1793_, sizeof(void*)*3);
v_suppressElabErrors_1800_ = lean_ctor_get_uint8(v___y_1793_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1801_ = lean_ctor_get_uint8(v___y_1793_, sizeof(void*)*3 + 3);
v_ref_1802_ = l_Lean_replaceRef(v_ref_1789_, v_ref_1798_);
lean_inc(v_currRecDepth_1797_);
lean_inc_ref(v_toCold_1796_);
v___x_1803_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1803_, 0, v_toCold_1796_);
lean_ctor_set(v___x_1803_, 1, v_currRecDepth_1797_);
lean_ctor_set(v___x_1803_, 2, v_ref_1802_);
lean_ctor_set_uint16(v___x_1803_, sizeof(void*)*3, v_optionFlags_1799_);
lean_ctor_set_uint8(v___x_1803_, sizeof(void*)*3 + 2, v_suppressElabErrors_1800_);
lean_ctor_set_uint8(v___x_1803_, sizeof(void*)*3 + 3, v_isRecordingDeps_1801_);
v___x_1804_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1790_, v___y_1791_, v___y_1792_, v___x_1803_, v___y_1794_);
lean_dec_ref_known(v___x_1803_, 3);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1805_, lean_object* v_msg_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1805_, v_msg_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v_ref_1805_);
return v_res_1812_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v___x_1816_);
lean_ctor_set(v___x_1817_, 2, v___x_1816_);
lean_ctor_set(v___x_1817_, 3, v___x_1816_);
lean_ctor_set(v___x_1817_, 4, v___x_1815_);
lean_ctor_set(v___x_1817_, 5, v___x_1815_);
lean_ctor_set(v___x_1817_, 6, v___x_1815_);
lean_ctor_set(v___x_1817_, 7, v___x_1815_);
lean_ctor_set(v___x_1817_, 8, v___x_1815_);
lean_ctor_set(v___x_1817_, 9, v___x_1815_);
lean_ctor_set(v___x_1817_, 10, v___x_1815_);
return v___x_1817_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1818_ = lean_unsigned_to_nat(32u);
v___x_1819_ = lean_mk_empty_array_with_capacity(v___x_1818_);
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
size_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1821_ = ((size_t)5ULL);
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = lean_unsigned_to_nat(32u);
v___x_1824_ = lean_mk_empty_array_with_capacity(v___x_1823_);
v___x_1825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1826_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1824_);
lean_ctor_set(v___x_1826_, 2, v___x_1822_);
lean_ctor_set(v___x_1826_, 3, v___x_1822_);
lean_ctor_set_usize(v___x_1826_, 4, v___x_1821_);
return v___x_1826_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1827_ = lean_box(1);
v___x_1828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v___x_1828_);
lean_ctor_set(v___x_1830_, 2, v___x_1827_);
return v___x_1830_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5));
v___x_1833_ = l_Lean_stringToMessageData(v___x_1832_);
return v___x_1833_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7));
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9));
v___x_1839_ = l_Lean_stringToMessageData(v___x_1838_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11));
v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15));
v___x_1848_ = l_Lean_stringToMessageData(v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17));
v___x_1851_ = l_Lean_stringToMessageData(v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1852_, lean_object* v_declHint_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_env_1858_; uint8_t v___x_1859_; 
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_st_ref_get(v___y_1854_);
v_env_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc_ref(v_env_1858_);
lean_dec(v___x_1857_);
v___x_1859_ = l_Lean_Name_isAnonymous(v_declHint_1853_);
if (v___x_1859_ == 0)
{
uint8_t v_isExporting_1860_; 
v_isExporting_1860_ = lean_ctor_get_uint8(v_env_1858_, sizeof(void*)*8);
if (v_isExporting_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v_env_1858_);
lean_dec(v_declHint_1853_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_msg_1852_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; uint8_t v___x_1863_; 
lean_inc_ref(v_env_1858_);
v___x_1862_ = l_Lean_Environment_setExporting(v_env_1858_, v___x_1859_);
lean_inc(v_declHint_1853_);
lean_inc_ref(v___x_1862_);
v___x_1863_ = l_Lean_Environment_contains(v___x_1862_, v_declHint_1853_, v_isExporting_1860_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; 
lean_dec_ref(v___x_1862_);
lean_dec_ref(v_env_1858_);
lean_dec(v_declHint_1853_);
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v_msg_1852_);
return v___x_1864_;
}
else
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v_c_1870_; lean_object* v___x_1871_; 
v___x_1865_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1866_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1867_ = l_Lean_Options_empty;
v___x_1868_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1862_);
lean_ctor_set(v___x_1868_, 1, v___x_1865_);
lean_ctor_set(v___x_1868_, 2, v___x_1866_);
lean_ctor_set(v___x_1868_, 3, v___x_1867_);
lean_inc(v_declHint_1853_);
v___x_1869_ = l_Lean_MessageData_ofConstName(v_declHint_1853_, v___x_1859_);
v_c_1870_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1870_, 0, v___x_1868_);
lean_ctor_set(v_c_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1858_, v_declHint_1853_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
lean_dec_ref(v_env_1858_);
lean_dec(v_declHint_1853_);
v___x_1872_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
lean_ctor_set(v___x_1873_, 1, v_c_1870_);
v___x_1874_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = l_Lean_MessageData_note(v___x_1875_);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v_msg_1852_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
else
{
lean_object* v_val_1879_; lean_object* v___x_1881_; uint8_t v_isShared_1882_; uint8_t v_isSharedCheck_1913_; 
v_val_1879_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1881_ = v___x_1871_;
v_isShared_1882_ = v_isSharedCheck_1913_;
goto v_resetjp_1880_;
}
else
{
lean_inc(v_val_1879_);
lean_dec(v___x_1871_);
v___x_1881_ = lean_box(0);
v_isShared_1882_ = v_isSharedCheck_1913_;
goto v_resetjp_1880_;
}
v_resetjp_1880_:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v_mod_1885_; uint8_t v___x_1886_; 
v___x_1883_ = l_Lean_Environment_header(v_env_1858_);
lean_dec_ref(v_env_1858_);
v___x_1884_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1883_);
v_mod_1885_ = lean_array_get(v___x_1856_, v___x_1884_, v_val_1879_);
lean_dec(v_val_1879_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l_Lean_isPrivateName(v_declHint_1853_);
lean_dec(v_declHint_1853_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1887_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_c_1870_);
v___x_1889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_MessageData_ofName(v_mod_1885_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = l_Lean_MessageData_note(v___x_1894_);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_msg_1852_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set_tag(v___x_1881_, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1896_);
v___x_1898_ = v___x_1881_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_c_1870_);
v___x_1902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_MessageData_ofName(v_mod_1885_);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Lean_MessageData_note(v___x_1907_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v_msg_1852_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
if (v_isShared_1882_ == 0)
{
lean_ctor_set_tag(v___x_1881_, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1909_);
v___x_1911_ = v___x_1881_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1914_; 
lean_dec_ref(v_env_1858_);
lean_dec(v_declHint_1853_);
v___x_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_msg_1852_);
return v___x_1914_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1915_, lean_object* v_declHint_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1915_, v_declHint_1916_, v___y_1917_);
lean_dec(v___y_1917_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1920_, lean_object* v_declHint_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1937_; 
v___x_1927_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1920_, v_declHint_1921_, v___y_1925_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1927_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1930_ = v___x_1927_;
v_isShared_1931_ = v_isSharedCheck_1937_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1927_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1937_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1932_ = l_Lean_unknownIdentifierMessageTag;
v___x_1933_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v_a_1928_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v___x_1933_);
v___x_1935_ = v___x_1930_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1938_, lean_object* v_declHint_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1938_, v_declHint_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1946_, lean_object* v_msg_1947_, lean_object* v_declHint_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v_a_1955_; lean_object* v___x_1956_; 
v___x_1954_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1947_, v_declHint_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref(v___x_1954_);
v___x_1956_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1946_, v_a_1955_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1957_, lean_object* v_msg_1958_, lean_object* v_declHint_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1957_, v_msg_1958_, v_declHint_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1962_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v_ref_1957_);
return v_res_1965_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_1968_ = l_Lean_stringToMessageData(v___x_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_1971_ = l_Lean_stringToMessageData(v___x_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_1972_, lean_object* v_constName_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v___x_1979_; uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; 
v___x_1979_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_1980_ = 0;
lean_inc(v_constName_1973_);
v___x_1981_ = l_Lean_MessageData_ofConstName(v_constName_1973_, v___x_1980_);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1979_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1982_);
lean_ctor_set(v___x_1984_, 1, v___x_1983_);
v___x_1985_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1972_, v___x_1984_, v_constName_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_1986_, lean_object* v_constName_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1986_, v_constName_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v_ref_1986_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_ref_2000_; lean_object* v___x_2001_; 
v_ref_2000_ = lean_ctor_get(v___y_1997_, 2);
v___x_2001_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2000_, v_constName_1994_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2002_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v___x_2015_; lean_object* v_env_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; 
v___x_2015_ = lean_st_ref_get(v___y_2013_);
v_env_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_ref(v_env_2016_);
lean_dec(v___x_2015_);
v___x_2017_ = 0;
lean_inc(v_constName_2009_);
v___x_2018_ = l_Lean_Environment_findConstVal_x3f(v_env_2016_, v_constName_2009_, v___x_2017_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
return v___x_2019_;
}
else
{
lean_object* v_val_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v_constName_2009_);
v_val_2020_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2018_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_val_2020_);
lean_dec(v___x_2018_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
lean_ctor_set_tag(v___x_2022_, 0);
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_val_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_);
lean_dec(v___y_2032_);
lean_dec_ref(v___y_2031_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2035_, uint8_t v_s_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; lean_object* v_env_2041_; lean_object* v_nextMacroScope_2042_; lean_object* v_ngen_2043_; lean_object* v_auxDeclNGen_2044_; lean_object* v_traceState_2045_; lean_object* v_recordedDeps_2046_; lean_object* v_messages_2047_; lean_object* v_infoState_2048_; lean_object* v_snapshotTasks_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2078_; 
v___x_2040_ = lean_st_ref_take(v___y_2038_);
v_env_2041_ = lean_ctor_get(v___x_2040_, 0);
v_nextMacroScope_2042_ = lean_ctor_get(v___x_2040_, 1);
v_ngen_2043_ = lean_ctor_get(v___x_2040_, 2);
v_auxDeclNGen_2044_ = lean_ctor_get(v___x_2040_, 3);
v_traceState_2045_ = lean_ctor_get(v___x_2040_, 4);
v_recordedDeps_2046_ = lean_ctor_get(v___x_2040_, 6);
v_messages_2047_ = lean_ctor_get(v___x_2040_, 7);
v_infoState_2048_ = lean_ctor_get(v___x_2040_, 8);
v_snapshotTasks_2049_ = lean_ctor_get(v___x_2040_, 9);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2078_ == 0)
{
lean_object* v_unused_2079_; 
v_unused_2079_ = lean_ctor_get(v___x_2040_, 5);
lean_dec(v_unused_2079_);
v___x_2051_ = v___x_2040_;
v_isShared_2052_ = v_isSharedCheck_2078_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_snapshotTasks_2049_);
lean_inc(v_infoState_2048_);
lean_inc(v_messages_2047_);
lean_inc(v_recordedDeps_2046_);
lean_inc(v_traceState_2045_);
lean_inc(v_auxDeclNGen_2044_);
lean_inc(v_ngen_2043_);
lean_inc(v_nextMacroScope_2042_);
lean_inc(v_env_2041_);
lean_dec(v___x_2040_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2078_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2053_ = 0;
v___x_2054_ = lean_box(0);
v___x_2055_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2041_, v_declName_2035_, v_s_2036_, v___x_2053_, v___x_2054_);
v___x_2056_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 5, v___x_2056_);
lean_ctor_set(v___x_2051_, 0, v___x_2055_);
v___x_2058_ = v___x_2051_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_nextMacroScope_2042_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_ngen_2043_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_auxDeclNGen_2044_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_traceState_2045_);
lean_ctor_set(v_reuseFailAlloc_2077_, 5, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2077_, 6, v_recordedDeps_2046_);
lean_ctor_set(v_reuseFailAlloc_2077_, 7, v_messages_2047_);
lean_ctor_set(v_reuseFailAlloc_2077_, 8, v_infoState_2048_);
lean_ctor_set(v_reuseFailAlloc_2077_, 9, v_snapshotTasks_2049_);
v___x_2058_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v_mctx_2061_; lean_object* v_zetaDeltaFVarIds_2062_; lean_object* v_postponed_2063_; lean_object* v_diag_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2075_; 
v___x_2059_ = lean_st_ref_put(v___y_2038_, v___x_2058_);
v___x_2060_ = lean_st_ref_take(v___y_2037_);
v_mctx_2061_ = lean_ctor_get(v___x_2060_, 0);
v_zetaDeltaFVarIds_2062_ = lean_ctor_get(v___x_2060_, 2);
v_postponed_2063_ = lean_ctor_get(v___x_2060_, 3);
v_diag_2064_ = lean_ctor_get(v___x_2060_, 4);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v___x_2060_, 1);
lean_dec(v_unused_2076_);
v___x_2066_ = v___x_2060_;
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_diag_2064_);
lean_inc(v_postponed_2063_);
lean_inc(v_zetaDeltaFVarIds_2062_);
lean_inc(v_mctx_2061_);
lean_dec(v___x_2060_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2075_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 1, v___x_2069_);
v___x_2071_ = v___x_2066_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_mctx_2061_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_zetaDeltaFVarIds_2062_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_postponed_2063_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_diag_2064_);
v___x_2071_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2072_ = lean_st_ref_put(v___y_2037_, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2068_);
return v___x_2073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2080_, lean_object* v_s_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
uint8_t v_s_boxed_2085_; lean_object* v_res_2086_; 
v_s_boxed_2085_ = lean_unbox(v_s_2081_);
v_res_2086_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2080_, v_s_boxed_2085_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec(v___y_2082_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
uint8_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = 0;
v___x_2094_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2087_, v___x_2093_, v___y_2089_, v___y_2091_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
return v_res_2101_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2104_ = l_Lean_stringToMessageData(v___x_2103_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2107_ = l_Lean_stringToMessageData(v___x_2106_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2110_ = l_Lean_stringToMessageData(v___x_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2111_, lean_object* v_declName_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2118_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2119_ = l_Lean_MessageData_ofName(v_attrName_2111_);
v___x_2120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = 0;
v___x_2124_ = l_Lean_MessageData_ofConstName(v_declName_2112_, v___x_2123_);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2122_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2127_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2129_, lean_object* v_declName_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2129_, v_declName_2130_, v___y_2131_, v___y_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec(v___y_2132_);
lean_dec_ref(v___y_2131_);
return v_res_2136_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2143_, lean_object* v_declName_2144_, lean_object* v_asyncPrefix_x3f_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___y_2152_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2145_) == 0)
{
lean_object* v___x_2165_; 
v___x_2165_ = l_Lean_MessageData_nil;
v___y_2152_ = v___x_2165_;
goto v___jp_2151_;
}
else
{
lean_object* v_val_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v_val_2166_ = lean_ctor_get(v_asyncPrefix_x3f_2145_, 0);
lean_inc(v_val_2166_);
lean_dec_ref_known(v_asyncPrefix_x3f_2145_, 1);
v___x_2167_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2168_ = l_Lean_MessageData_ofName(v_val_2166_);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2169_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___y_2152_ = v___x_2171_;
goto v___jp_2151_;
}
v___jp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2153_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2154_ = l_Lean_MessageData_ofName(v_attrName_2143_);
v___x_2155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2153_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2155_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = 0;
v___x_2159_ = l_Lean_MessageData_ofConstName(v_declName_2144_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2157_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v___y_2152_);
v___x_2164_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2163_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
return v___x_2164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2172_, lean_object* v_declName_2173_, lean_object* v_asyncPrefix_x3f_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2172_, v_declName_2173_, v_asyncPrefix_x3f_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2181_, lean_object* v_decl_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___y_2189_; lean_object* v___y_2190_; lean_object* v___x_2232_; lean_object* v_env_2233_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___y_2237_; lean_object* v___y_2238_; lean_object* v___x_2248_; 
v___x_2232_ = lean_st_ref_get(v___y_2186_);
v_env_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc_ref(v_env_2233_);
lean_dec(v___x_2232_);
v___x_2248_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2233_, v_decl_2182_);
if (lean_obj_tag(v___x_2248_) == 0)
{
v___y_2235_ = v___y_2183_;
v___y_2236_ = v___y_2184_;
v___y_2237_ = v___y_2185_;
v___y_2238_ = v___y_2186_;
goto v___jp_2234_;
}
else
{
lean_object* v_attr_2249_; lean_object* v_toAttributeImplCore_2250_; lean_object* v_name_2251_; lean_object* v___x_2252_; 
lean_dec_ref_known(v___x_2248_, 1);
lean_dec_ref(v_env_2233_);
v_attr_2249_ = lean_ctor_get(v_attr_2181_, 0);
lean_inc_ref(v_attr_2249_);
lean_dec_ref(v_attr_2181_);
v_toAttributeImplCore_2250_ = lean_ctor_get(v_attr_2249_, 0);
lean_inc_ref(v_toAttributeImplCore_2250_);
lean_dec_ref(v_attr_2249_);
v_name_2251_ = lean_ctor_get(v_toAttributeImplCore_2250_, 1);
lean_inc(v_name_2251_);
lean_dec_ref(v_toAttributeImplCore_2250_);
v___x_2252_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2251_, v_decl_2182_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
return v___x_2252_;
}
v___jp_2188_:
{
lean_object* v___x_2191_; lean_object* v_ext_2192_; lean_object* v_toEnvExtension_2193_; lean_object* v_env_2194_; lean_object* v_nextMacroScope_2195_; lean_object* v_ngen_2196_; lean_object* v_auxDeclNGen_2197_; lean_object* v_traceState_2198_; lean_object* v_recordedDeps_2199_; lean_object* v_messages_2200_; lean_object* v_infoState_2201_; lean_object* v_snapshotTasks_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2230_; 
v___x_2191_ = lean_st_ref_take(v___y_2190_);
v_ext_2192_ = lean_ctor_get(v_attr_2181_, 1);
lean_inc_ref(v_ext_2192_);
lean_dec_ref(v_attr_2181_);
v_toEnvExtension_2193_ = lean_ctor_get(v_ext_2192_, 0);
v_env_2194_ = lean_ctor_get(v___x_2191_, 0);
v_nextMacroScope_2195_ = lean_ctor_get(v___x_2191_, 1);
v_ngen_2196_ = lean_ctor_get(v___x_2191_, 2);
v_auxDeclNGen_2197_ = lean_ctor_get(v___x_2191_, 3);
v_traceState_2198_ = lean_ctor_get(v___x_2191_, 4);
v_recordedDeps_2199_ = lean_ctor_get(v___x_2191_, 6);
v_messages_2200_ = lean_ctor_get(v___x_2191_, 7);
v_infoState_2201_ = lean_ctor_get(v___x_2191_, 8);
v_snapshotTasks_2202_ = lean_ctor_get(v___x_2191_, 9);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v___x_2191_, 5);
lean_dec(v_unused_2231_);
v___x_2204_ = v___x_2191_;
v_isShared_2205_ = v_isSharedCheck_2230_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_snapshotTasks_2202_);
lean_inc(v_infoState_2201_);
lean_inc(v_messages_2200_);
lean_inc(v_recordedDeps_2199_);
lean_inc(v_traceState_2198_);
lean_inc(v_auxDeclNGen_2197_);
lean_inc(v_ngen_2196_);
lean_inc(v_nextMacroScope_2195_);
lean_inc(v_env_2194_);
lean_dec(v___x_2191_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2230_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_asyncMode_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v_asyncMode_2206_ = lean_ctor_get(v_toEnvExtension_2193_, 2);
lean_inc(v_asyncMode_2206_);
lean_inc(v_decl_2182_);
v___x_2207_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2192_, v_env_2194_, v_decl_2182_, v_asyncMode_2206_, v_decl_2182_);
lean_dec(v_asyncMode_2206_);
v___x_2208_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 5, v___x_2208_);
lean_ctor_set(v___x_2204_, 0, v___x_2207_);
v___x_2210_ = v___x_2204_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v___x_2207_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_nextMacroScope_2195_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_ngen_2196_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_auxDeclNGen_2197_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v_traceState_2198_);
lean_ctor_set(v_reuseFailAlloc_2229_, 5, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2229_, 6, v_recordedDeps_2199_);
lean_ctor_set(v_reuseFailAlloc_2229_, 7, v_messages_2200_);
lean_ctor_set(v_reuseFailAlloc_2229_, 8, v_infoState_2201_);
lean_ctor_set(v_reuseFailAlloc_2229_, 9, v_snapshotTasks_2202_);
v___x_2210_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v_mctx_2213_; lean_object* v_zetaDeltaFVarIds_2214_; lean_object* v_postponed_2215_; lean_object* v_diag_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2227_; 
v___x_2211_ = lean_st_ref_put(v___y_2190_, v___x_2210_);
v___x_2212_ = lean_st_ref_take(v___y_2189_);
v_mctx_2213_ = lean_ctor_get(v___x_2212_, 0);
v_zetaDeltaFVarIds_2214_ = lean_ctor_get(v___x_2212_, 2);
v_postponed_2215_ = lean_ctor_get(v___x_2212_, 3);
v_diag_2216_ = lean_ctor_get(v___x_2212_, 4);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2227_ == 0)
{
lean_object* v_unused_2228_; 
v_unused_2228_ = lean_ctor_get(v___x_2212_, 1);
lean_dec(v_unused_2228_);
v___x_2218_ = v___x_2212_;
v_isShared_2219_ = v_isSharedCheck_2227_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_diag_2216_);
lean_inc(v_postponed_2215_);
lean_inc(v_zetaDeltaFVarIds_2214_);
lean_inc(v_mctx_2213_);
lean_dec(v___x_2212_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2227_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2223_; 
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 1, v___x_2221_);
v___x_2223_ = v___x_2218_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_mctx_2213_);
lean_ctor_set(v_reuseFailAlloc_2226_, 1, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2226_, 2, v_zetaDeltaFVarIds_2214_);
lean_ctor_set(v_reuseFailAlloc_2226_, 3, v_postponed_2215_);
lean_ctor_set(v_reuseFailAlloc_2226_, 4, v_diag_2216_);
v___x_2223_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_st_ref_put(v___y_2189_, v___x_2223_);
v___x_2225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2225_, 0, v___x_2220_);
return v___x_2225_;
}
}
}
}
}
v___jp_2234_:
{
lean_object* v_ext_2239_; lean_object* v_toEnvExtension_2240_; lean_object* v_attr_2241_; lean_object* v_asyncMode_2242_; uint8_t v___x_2243_; 
v_ext_2239_ = lean_ctor_get(v_attr_2181_, 1);
v_toEnvExtension_2240_ = lean_ctor_get(v_ext_2239_, 0);
v_attr_2241_ = lean_ctor_get(v_attr_2181_, 0);
v_asyncMode_2242_ = lean_ctor_get(v_toEnvExtension_2240_, 2);
lean_inc(v_decl_2182_);
lean_inc_ref(v_env_2233_);
v___x_2243_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2233_, v_decl_2182_, v_asyncMode_2242_);
if (v___x_2243_ == 0)
{
lean_object* v_toAttributeImplCore_2244_; lean_object* v_name_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_inc_ref(v_attr_2241_);
lean_dec_ref(v_attr_2181_);
v_toAttributeImplCore_2244_ = lean_ctor_get(v_attr_2241_, 0);
lean_inc_ref(v_toAttributeImplCore_2244_);
lean_dec_ref(v_attr_2241_);
v_name_2245_ = lean_ctor_get(v_toAttributeImplCore_2244_, 1);
lean_inc(v_name_2245_);
lean_dec_ref(v_toAttributeImplCore_2244_);
v___x_2246_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2233_);
v___x_2247_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2245_, v_decl_2182_, v___x_2246_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
return v___x_2247_;
}
else
{
lean_dec_ref(v_env_2233_);
v___y_2189_ = v___y_2236_;
v___y_2190_ = v___y_2238_;
goto v___jp_2188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2253_, lean_object* v_decl_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2253_, v_decl_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; lean_object* v_env_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; 
v___x_2267_ = lean_st_ref_get(v___y_2265_);
v_env_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc_ref(v_env_2268_);
lean_dec(v___x_2267_);
v___x_2269_ = 0;
lean_inc(v_constName_2261_);
v___x_2270_ = l_Lean_Environment_find_x3f(v_env_2268_, v_constName_2261_, v___x_2269_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2271_;
}
else
{
lean_object* v_val_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2279_; 
lean_dec(v_constName_2261_);
v_val_2272_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2274_ = v___x_2270_;
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_val_2272_);
lean_dec(v___x_2270_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2279_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2277_; 
if (v_isShared_2275_ == 0)
{
lean_ctor_set_tag(v___x_2274_, 0);
v___x_2277_ = v___x_2274_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_val_2272_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2286_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2290_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2291_ = lean_unsigned_to_nat(58u);
v___x_2292_ = lean_unsigned_to_nat(33u);
v___x_2293_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2294_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2295_ = l_mkPanicMessageWithDecl(v___x_2294_, v___x_2293_, v___x_2292_, v___x_2291_, v___x_2290_);
return v___x_2295_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2297_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2298_ = lean_unsigned_to_nat(60u);
v___x_2299_ = lean_unsigned_to_nat(30u);
v___x_2300_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2301_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2302_ = l_mkPanicMessageWithDecl(v___x_2301_, v___x_2300_, v___x_2299_, v___x_2298_, v___x_2297_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2303_, lean_object* v_indName_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2310_; 
lean_inc(v_indName_2304_);
v___x_2310_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v_a_2311_; 
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___x_2310_, 1);
if (lean_obj_tag(v_a_2311_) == 5)
{
lean_object* v_val_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2502_; 
v_val_2312_ = lean_ctor_get(v_a_2311_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_a_2311_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2314_ = v_a_2311_;
v_isShared_2315_ = v_isSharedCheck_2502_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_val_2312_);
lean_dec(v_a_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2502_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_inc(v_indName_2304_);
v___x_2316_ = l_Lean_mkCasesOnName(v_indName_2304_);
lean_inc(v___x_2316_);
v___x_2317_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2316_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v_name_2319_; lean_object* v_levelParams_2320_; lean_object* v_type_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v_name_2319_ = lean_ctor_get(v_a_2318_, 0);
lean_inc(v_name_2319_);
v_levelParams_2320_ = lean_ctor_get(v_a_2318_, 1);
lean_inc_n(v_levelParams_2320_, 2);
v_type_2321_ = lean_ctor_get(v_a_2318_, 2);
lean_inc_ref(v_type_2321_);
lean_dec(v_a_2318_);
v___x_2322_ = lean_box(0);
v___x_2323_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2320_, v___x_2322_);
if (lean_obj_tag(v___x_2323_) == 1)
{
lean_object* v_head_2324_; lean_object* v_tail_2325_; lean_object* v_numParams_2326_; lean_object* v_numIndices_2327_; lean_object* v_ctors_2328_; lean_object* v___f_2329_; lean_object* v___x_2331_; 
v_head_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_head_2324_);
v_tail_2325_ = lean_ctor_get(v___x_2323_, 1);
lean_inc(v_tail_2325_);
v_numParams_2326_ = lean_ctor_get(v_val_2312_, 1);
lean_inc_n(v_numParams_2326_, 2);
v_numIndices_2327_ = lean_ctor_get(v_val_2312_, 2);
lean_inc(v_numIndices_2327_);
v_ctors_2328_ = lean_ctor_get(v_val_2312_, 4);
lean_inc(v_ctors_2328_);
v___f_2329_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2329_, 0, v_numIndices_2327_);
lean_closure_set(v___f_2329_, 1, v_head_2324_);
lean_closure_set(v___f_2329_, 2, v_ctors_2328_);
lean_closure_set(v___f_2329_, 3, v_indName_2304_);
lean_closure_set(v___f_2329_, 4, v_tail_2325_);
lean_closure_set(v___f_2329_, 5, v_name_2319_);
lean_closure_set(v___f_2329_, 6, v___x_2323_);
lean_closure_set(v___f_2329_, 7, v_numParams_2326_);
lean_closure_set(v___f_2329_, 8, v_val_2312_);
lean_closure_set(v___f_2329_, 9, v___x_2316_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set_tag(v___x_2314_, 1);
lean_ctor_set(v___x_2314_, 0, v_numParams_2326_);
v___x_2331_ = v___x_2314_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_numParams_2326_);
v___x_2331_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
uint8_t v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = 0;
v___x_2333_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2321_, v___x_2331_, v___f_2329_, v___x_2332_, v___x_2332_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; lean_object* v___f_2336_; uint8_t v___y_2338_; uint8_t v___x_2481_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref_known(v___x_2333_, 1);
v___x_2335_ = lean_box(v___x_2332_);
lean_inc(v_declName_2303_);
v___f_2336_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2336_, 0, v_a_2334_);
lean_closure_set(v___f_2336_, 1, v_declName_2303_);
lean_closure_set(v___f_2336_, 2, v_levelParams_2320_);
lean_closure_set(v___f_2336_, 3, v___x_2335_);
v___x_2481_ = l_Lean_isPrivateName(v_declName_2303_);
if (v___x_2481_ == 0)
{
uint8_t v___x_2482_; 
v___x_2482_ = 1;
v___y_2338_ = v___x_2482_;
goto v___jp_2337_;
}
else
{
v___y_2338_ = v___x_2332_;
goto v___jp_2337_;
}
v___jp_2337_:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2336_, v___y_2338_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v___x_2340_; lean_object* v_env_2341_; lean_object* v_nextMacroScope_2342_; lean_object* v_ngen_2343_; lean_object* v_auxDeclNGen_2344_; lean_object* v_traceState_2345_; lean_object* v_recordedDeps_2346_; lean_object* v_messages_2347_; lean_object* v_infoState_2348_; lean_object* v_snapshotTasks_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref_known(v___x_2339_, 1);
v___x_2340_ = lean_st_ref_take(v_a_2308_);
v_env_2341_ = lean_ctor_get(v___x_2340_, 0);
v_nextMacroScope_2342_ = lean_ctor_get(v___x_2340_, 1);
v_ngen_2343_ = lean_ctor_get(v___x_2340_, 2);
v_auxDeclNGen_2344_ = lean_ctor_get(v___x_2340_, 3);
v_traceState_2345_ = lean_ctor_get(v___x_2340_, 4);
v_recordedDeps_2346_ = lean_ctor_get(v___x_2340_, 6);
v_messages_2347_ = lean_ctor_get(v___x_2340_, 7);
v_infoState_2348_ = lean_ctor_get(v___x_2340_, 8);
v_snapshotTasks_2349_ = lean_ctor_get(v___x_2340_, 9);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2340_, 5);
lean_dec(v_unused_2480_);
v___x_2351_ = v___x_2340_;
v_isShared_2352_ = v_isSharedCheck_2479_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_snapshotTasks_2349_);
lean_inc(v_infoState_2348_);
lean_inc(v_messages_2347_);
lean_inc(v_recordedDeps_2346_);
lean_inc(v_traceState_2345_);
lean_inc(v_auxDeclNGen_2344_);
lean_inc(v_ngen_2343_);
lean_inc(v_nextMacroScope_2342_);
lean_inc(v_env_2341_);
lean_dec(v___x_2340_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2479_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
lean_inc(v_declName_2303_);
v___x_2353_ = l_Lean_Meta_markMatcherLike(v_env_2341_, v_declName_2303_);
v___x_2354_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 5, v___x_2354_);
lean_ctor_set(v___x_2351_, 0, v___x_2353_);
v___x_2356_ = v___x_2351_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_nextMacroScope_2342_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_ngen_2343_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_auxDeclNGen_2344_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v_traceState_2345_);
lean_ctor_set(v_reuseFailAlloc_2478_, 5, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2478_, 6, v_recordedDeps_2346_);
lean_ctor_set(v_reuseFailAlloc_2478_, 7, v_messages_2347_);
lean_ctor_set(v_reuseFailAlloc_2478_, 8, v_infoState_2348_);
lean_ctor_set(v_reuseFailAlloc_2478_, 9, v_snapshotTasks_2349_);
v___x_2356_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v_mctx_2359_; lean_object* v_zetaDeltaFVarIds_2360_; lean_object* v_postponed_2361_; lean_object* v_diag_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2476_; 
v___x_2357_ = lean_st_ref_put(v_a_2308_, v___x_2356_);
v___x_2358_ = lean_st_ref_take(v_a_2306_);
v_mctx_2359_ = lean_ctor_get(v___x_2358_, 0);
v_zetaDeltaFVarIds_2360_ = lean_ctor_get(v___x_2358_, 2);
v_postponed_2361_ = lean_ctor_get(v___x_2358_, 3);
v_diag_2362_ = lean_ctor_get(v___x_2358_, 4);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2358_, 1);
lean_dec(v_unused_2477_);
v___x_2364_ = v___x_2358_;
v_isShared_2365_ = v_isSharedCheck_2476_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_diag_2362_);
lean_inc(v_postponed_2361_);
lean_inc(v_zetaDeltaFVarIds_2360_);
lean_inc(v_mctx_2359_);
lean_dec(v___x_2358_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2476_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2368_; 
v___x_2366_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v___x_2366_);
v___x_2368_ = v___x_2364_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_mctx_2359_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_zetaDeltaFVarIds_2360_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_postponed_2361_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_diag_2362_);
v___x_2368_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v_env_2371_; lean_object* v_nextMacroScope_2372_; lean_object* v_ngen_2373_; lean_object* v_auxDeclNGen_2374_; lean_object* v_traceState_2375_; lean_object* v_recordedDeps_2376_; lean_object* v_messages_2377_; lean_object* v_infoState_2378_; lean_object* v_snapshotTasks_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2473_; 
v___x_2369_ = lean_st_ref_put(v_a_2306_, v___x_2368_);
v___x_2370_ = lean_st_ref_take(v_a_2308_);
v_env_2371_ = lean_ctor_get(v___x_2370_, 0);
v_nextMacroScope_2372_ = lean_ctor_get(v___x_2370_, 1);
v_ngen_2373_ = lean_ctor_get(v___x_2370_, 2);
v_auxDeclNGen_2374_ = lean_ctor_get(v___x_2370_, 3);
v_traceState_2375_ = lean_ctor_get(v___x_2370_, 4);
v_recordedDeps_2376_ = lean_ctor_get(v___x_2370_, 6);
v_messages_2377_ = lean_ctor_get(v___x_2370_, 7);
v_infoState_2378_ = lean_ctor_get(v___x_2370_, 8);
v_snapshotTasks_2379_ = lean_ctor_get(v___x_2370_, 9);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2370_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v___x_2370_, 5);
lean_dec(v_unused_2474_);
v___x_2381_ = v___x_2370_;
v_isShared_2382_ = v_isSharedCheck_2473_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_snapshotTasks_2379_);
lean_inc(v_infoState_2378_);
lean_inc(v_messages_2377_);
lean_inc(v_recordedDeps_2376_);
lean_inc(v_traceState_2375_);
lean_inc(v_auxDeclNGen_2374_);
lean_inc(v_ngen_2373_);
lean_inc(v_nextMacroScope_2372_);
lean_inc(v_env_2371_);
lean_dec(v___x_2370_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2473_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2383_; lean_object* v___x_2385_; 
lean_inc(v_declName_2303_);
v___x_2383_ = l_Lean_markAuxRecursor(v_env_2371_, v_declName_2303_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 5, v___x_2354_);
lean_ctor_set(v___x_2381_, 0, v___x_2383_);
v___x_2385_ = v___x_2381_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_nextMacroScope_2372_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_ngen_2373_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_auxDeclNGen_2374_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_traceState_2375_);
lean_ctor_set(v_reuseFailAlloc_2472_, 5, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2472_, 6, v_recordedDeps_2376_);
lean_ctor_set(v_reuseFailAlloc_2472_, 7, v_messages_2377_);
lean_ctor_set(v_reuseFailAlloc_2472_, 8, v_infoState_2378_);
lean_ctor_set(v_reuseFailAlloc_2472_, 9, v_snapshotTasks_2379_);
v___x_2385_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v_mctx_2388_; lean_object* v_zetaDeltaFVarIds_2389_; lean_object* v_postponed_2390_; lean_object* v_diag_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2470_; 
v___x_2386_ = lean_st_ref_put(v_a_2308_, v___x_2385_);
v___x_2387_ = lean_st_ref_take(v_a_2306_);
v_mctx_2388_ = lean_ctor_get(v___x_2387_, 0);
v_zetaDeltaFVarIds_2389_ = lean_ctor_get(v___x_2387_, 2);
v_postponed_2390_ = lean_ctor_get(v___x_2387_, 3);
v_diag_2391_ = lean_ctor_get(v___x_2387_, 4);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v___x_2387_, 1);
lean_dec(v_unused_2471_);
v___x_2393_ = v___x_2387_;
v_isShared_2394_ = v_isSharedCheck_2470_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_diag_2391_);
lean_inc(v_postponed_2390_);
lean_inc(v_zetaDeltaFVarIds_2389_);
lean_inc(v_mctx_2388_);
lean_dec(v___x_2387_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2470_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v___x_2366_);
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_mctx_2388_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_zetaDeltaFVarIds_2389_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_postponed_2390_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v_diag_2391_);
v___x_2396_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v_env_2399_; lean_object* v_nextMacroScope_2400_; lean_object* v_ngen_2401_; lean_object* v_auxDeclNGen_2402_; lean_object* v_traceState_2403_; lean_object* v_recordedDeps_2404_; lean_object* v_messages_2405_; lean_object* v_infoState_2406_; lean_object* v_snapshotTasks_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2467_; 
v___x_2397_ = lean_st_ref_put(v_a_2306_, v___x_2396_);
v___x_2398_ = lean_st_ref_take(v_a_2308_);
v_env_2399_ = lean_ctor_get(v___x_2398_, 0);
v_nextMacroScope_2400_ = lean_ctor_get(v___x_2398_, 1);
v_ngen_2401_ = lean_ctor_get(v___x_2398_, 2);
v_auxDeclNGen_2402_ = lean_ctor_get(v___x_2398_, 3);
v_traceState_2403_ = lean_ctor_get(v___x_2398_, 4);
v_recordedDeps_2404_ = lean_ctor_get(v___x_2398_, 6);
v_messages_2405_ = lean_ctor_get(v___x_2398_, 7);
v_infoState_2406_ = lean_ctor_get(v___x_2398_, 8);
v_snapshotTasks_2407_ = lean_ctor_get(v___x_2398_, 9);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; 
v_unused_2468_ = lean_ctor_get(v___x_2398_, 5);
lean_dec(v_unused_2468_);
v___x_2409_ = v___x_2398_;
v_isShared_2410_ = v_isSharedCheck_2467_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_snapshotTasks_2407_);
lean_inc(v_infoState_2406_);
lean_inc(v_messages_2405_);
lean_inc(v_recordedDeps_2404_);
lean_inc(v_traceState_2403_);
lean_inc(v_auxDeclNGen_2402_);
lean_inc(v_ngen_2401_);
lean_inc(v_nextMacroScope_2400_);
lean_inc(v_env_2399_);
lean_dec(v___x_2398_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2467_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
lean_inc(v_declName_2303_);
v___x_2411_ = l_Lean_Meta_addToCompletionBlackList(v_env_2399_, v_declName_2303_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 5, v___x_2354_);
lean_ctor_set(v___x_2409_, 0, v___x_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_nextMacroScope_2400_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v_ngen_2401_);
lean_ctor_set(v_reuseFailAlloc_2466_, 3, v_auxDeclNGen_2402_);
lean_ctor_set(v_reuseFailAlloc_2466_, 4, v_traceState_2403_);
lean_ctor_set(v_reuseFailAlloc_2466_, 5, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2466_, 6, v_recordedDeps_2404_);
lean_ctor_set(v_reuseFailAlloc_2466_, 7, v_messages_2405_);
lean_ctor_set(v_reuseFailAlloc_2466_, 8, v_infoState_2406_);
lean_ctor_set(v_reuseFailAlloc_2466_, 9, v_snapshotTasks_2407_);
v___x_2413_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v_mctx_2416_; lean_object* v_zetaDeltaFVarIds_2417_; lean_object* v_postponed_2418_; lean_object* v_diag_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2464_; 
v___x_2414_ = lean_st_ref_put(v_a_2308_, v___x_2413_);
v___x_2415_ = lean_st_ref_take(v_a_2306_);
v_mctx_2416_ = lean_ctor_get(v___x_2415_, 0);
v_zetaDeltaFVarIds_2417_ = lean_ctor_get(v___x_2415_, 2);
v_postponed_2418_ = lean_ctor_get(v___x_2415_, 3);
v_diag_2419_ = lean_ctor_get(v___x_2415_, 4);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2415_, 1);
lean_dec(v_unused_2465_);
v___x_2421_ = v___x_2415_;
v_isShared_2422_ = v_isSharedCheck_2464_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_diag_2419_);
lean_inc(v_postponed_2418_);
lean_inc(v_zetaDeltaFVarIds_2417_);
lean_inc(v_mctx_2416_);
lean_dec(v___x_2415_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2464_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v___x_2366_);
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_mctx_2416_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v_zetaDeltaFVarIds_2417_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v_postponed_2418_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_diag_2419_);
v___x_2424_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v_env_2427_; lean_object* v_nextMacroScope_2428_; lean_object* v_ngen_2429_; lean_object* v_auxDeclNGen_2430_; lean_object* v_traceState_2431_; lean_object* v_recordedDeps_2432_; lean_object* v_messages_2433_; lean_object* v_infoState_2434_; lean_object* v_snapshotTasks_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2461_; 
v___x_2425_ = lean_st_ref_put(v_a_2306_, v___x_2424_);
v___x_2426_ = lean_st_ref_take(v_a_2308_);
v_env_2427_ = lean_ctor_get(v___x_2426_, 0);
v_nextMacroScope_2428_ = lean_ctor_get(v___x_2426_, 1);
v_ngen_2429_ = lean_ctor_get(v___x_2426_, 2);
v_auxDeclNGen_2430_ = lean_ctor_get(v___x_2426_, 3);
v_traceState_2431_ = lean_ctor_get(v___x_2426_, 4);
v_recordedDeps_2432_ = lean_ctor_get(v___x_2426_, 6);
v_messages_2433_ = lean_ctor_get(v___x_2426_, 7);
v_infoState_2434_ = lean_ctor_get(v___x_2426_, 8);
v_snapshotTasks_2435_ = lean_ctor_get(v___x_2426_, 9);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v___x_2426_, 5);
lean_dec(v_unused_2462_);
v___x_2437_ = v___x_2426_;
v_isShared_2438_ = v_isSharedCheck_2461_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_snapshotTasks_2435_);
lean_inc(v_infoState_2434_);
lean_inc(v_messages_2433_);
lean_inc(v_recordedDeps_2432_);
lean_inc(v_traceState_2431_);
lean_inc(v_auxDeclNGen_2430_);
lean_inc(v_ngen_2429_);
lean_inc(v_nextMacroScope_2428_);
lean_inc(v_env_2427_);
lean_dec(v___x_2426_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2461_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_inc(v_declName_2303_);
v___x_2439_ = l_Lean_addProtected(v_env_2427_, v_declName_2303_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 5, v___x_2354_);
lean_ctor_set(v___x_2437_, 0, v___x_2439_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_nextMacroScope_2428_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_ngen_2429_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v_auxDeclNGen_2430_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v_traceState_2431_);
lean_ctor_set(v_reuseFailAlloc_2460_, 5, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2460_, 6, v_recordedDeps_2432_);
lean_ctor_set(v_reuseFailAlloc_2460_, 7, v_messages_2433_);
lean_ctor_set(v_reuseFailAlloc_2460_, 8, v_infoState_2434_);
lean_ctor_set(v_reuseFailAlloc_2460_, 9, v_snapshotTasks_2435_);
v___x_2441_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_mctx_2444_; lean_object* v_zetaDeltaFVarIds_2445_; lean_object* v_postponed_2446_; lean_object* v_diag_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2458_; 
v___x_2442_ = lean_st_ref_put(v_a_2308_, v___x_2441_);
v___x_2443_ = lean_st_ref_take(v_a_2306_);
v_mctx_2444_ = lean_ctor_get(v___x_2443_, 0);
v_zetaDeltaFVarIds_2445_ = lean_ctor_get(v___x_2443_, 2);
v_postponed_2446_ = lean_ctor_get(v___x_2443_, 3);
v_diag_2447_ = lean_ctor_get(v___x_2443_, 4);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v___x_2443_, 1);
lean_dec(v_unused_2459_);
v___x_2449_ = v___x_2443_;
v_isShared_2450_ = v_isSharedCheck_2458_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_diag_2447_);
lean_inc(v_postponed_2446_);
lean_inc(v_zetaDeltaFVarIds_2445_);
lean_inc(v_mctx_2444_);
lean_dec(v___x_2443_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2458_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v___x_2366_);
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_mctx_2444_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2366_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_zetaDeltaFVarIds_2445_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_postponed_2446_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_diag_2447_);
v___x_2452_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = lean_st_ref_put(v_a_2306_, v___x_2452_);
v___x_2454_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2303_);
v___x_2455_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2454_, v_declName_2303_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v___x_2456_; 
lean_dec_ref_known(v___x_2455_, 1);
v___x_2456_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2303_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
return v___x_2456_;
}
else
{
lean_dec(v_declName_2303_);
return v___x_2455_;
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
lean_dec(v_declName_2303_);
return v___x_2339_;
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_levelParams_2320_);
lean_dec(v_declName_2303_);
v_a_2483_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2333_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2333_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
lean_dec(v___x_2323_);
lean_dec_ref(v_type_2321_);
lean_dec(v_levelParams_2320_);
lean_dec(v_name_2319_);
lean_dec(v___x_2316_);
lean_del_object(v___x_2314_);
lean_dec_ref(v_val_2312_);
lean_dec(v_indName_2304_);
lean_dec(v_declName_2303_);
v___x_2492_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2493_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2492_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
return v___x_2493_;
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v___x_2316_);
lean_del_object(v___x_2314_);
lean_dec_ref(v_val_2312_);
lean_dec(v_indName_2304_);
lean_dec(v_declName_2303_);
v_a_2494_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2317_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2317_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
}
else
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec(v_a_2311_);
lean_dec(v_indName_2304_);
lean_dec(v_declName_2303_);
v___x_2503_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2504_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2503_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
return v___x_2504_;
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_indName_2304_);
lean_dec(v_declName_2303_);
v_a_2505_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2310_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2310_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v_a_2505_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2513_, lean_object* v_indName_2514_, lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2513_, v_indName_2514_, v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2521_, lean_object* v_name_2522_, lean_object* v_type_2523_, lean_object* v_k_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2522_, v_type_2523_, v_k_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2531_, lean_object* v_name_2532_, lean_object* v_type_2533_, lean_object* v_k_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2531_, v_name_2532_, v_type_2533_, v_k_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v___y_2536_);
lean_dec_ref(v___y_2535_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2541_, lean_object* v_params_2542_, lean_object* v_alts_2543_, lean_object* v___x_2544_, lean_object* v_ism2_2545_, lean_object* v_motive_2546_, lean_object* v_val_2547_, lean_object* v_indName_2548_, lean_object* v___x_2549_, lean_object* v___x_2550_, lean_object* v___x_2551_, lean_object* v_as_2552_, size_t v_sz_2553_, size_t v_i_2554_, lean_object* v_bs_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_){
_start:
{
lean_object* v___x_2561_; 
v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2541_, v_params_2542_, v_alts_2543_, v___x_2544_, v_ism2_2545_, v_motive_2546_, v_val_2547_, v_indName_2548_, v___x_2549_, v___x_2550_, v___x_2551_, v_sz_2553_, v_i_2554_, v_bs_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2562_ = _args[0];
lean_object* v_params_2563_ = _args[1];
lean_object* v_alts_2564_ = _args[2];
lean_object* v___x_2565_ = _args[3];
lean_object* v_ism2_2566_ = _args[4];
lean_object* v_motive_2567_ = _args[5];
lean_object* v_val_2568_ = _args[6];
lean_object* v_indName_2569_ = _args[7];
lean_object* v___x_2570_ = _args[8];
lean_object* v___x_2571_ = _args[9];
lean_object* v___x_2572_ = _args[10];
lean_object* v_as_2573_ = _args[11];
lean_object* v_sz_2574_ = _args[12];
lean_object* v_i_2575_ = _args[13];
lean_object* v_bs_2576_ = _args[14];
lean_object* v___y_2577_ = _args[15];
lean_object* v___y_2578_ = _args[16];
lean_object* v___y_2579_ = _args[17];
lean_object* v___y_2580_ = _args[18];
lean_object* v___y_2581_ = _args[19];
_start:
{
size_t v_sz_boxed_2582_; size_t v_i_boxed_2583_; lean_object* v_res_2584_; 
v_sz_boxed_2582_ = lean_unbox_usize(v_sz_2574_);
lean_dec(v_sz_2574_);
v_i_boxed_2583_ = lean_unbox_usize(v_i_2575_);
lean_dec(v_i_2575_);
v_res_2584_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2562_, v_params_2563_, v_alts_2564_, v___x_2565_, v_ism2_2566_, v_motive_2567_, v_val_2568_, v_indName_2569_, v___x_2570_, v___x_2571_, v___x_2572_, v_as_2573_, v_sz_boxed_2582_, v_i_boxed_2583_, v_bs_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
lean_dec_ref(v_as_2573_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2585_, lean_object* v_params_2586_, lean_object* v___x_2587_, lean_object* v_motive_2588_, lean_object* v_as_2589_, size_t v_sz_2590_, size_t v_i_2591_, lean_object* v_bs_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2585_, v_params_2586_, v___x_2587_, v_motive_2588_, v_sz_2590_, v_i_2591_, v_bs_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2599_, lean_object* v_params_2600_, lean_object* v___x_2601_, lean_object* v_motive_2602_, lean_object* v_as_2603_, lean_object* v_sz_2604_, lean_object* v_i_2605_, lean_object* v_bs_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
size_t v_sz_boxed_2612_; size_t v_i_boxed_2613_; lean_object* v_res_2614_; 
v_sz_boxed_2612_ = lean_unbox_usize(v_sz_2604_);
lean_dec(v_sz_2604_);
v_i_boxed_2613_ = lean_unbox_usize(v_i_2605_);
lean_dec(v_i_2605_);
v_res_2614_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2599_, v_params_2600_, v___x_2601_, v_motive_2602_, v_as_2603_, v_sz_boxed_2612_, v_i_boxed_2613_, v_bs_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec_ref(v_as_2603_);
lean_dec_ref(v_params_2600_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2615_, uint8_t v_s_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v___x_2622_; 
v___x_2622_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2615_, v_s_2616_, v___y_2618_, v___y_2620_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2623_, lean_object* v_s_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
uint8_t v_s_boxed_2630_; lean_object* v_res_2631_; 
v_s_boxed_2630_ = lean_unbox(v_s_2624_);
v_res_2631_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2623_, v_s_boxed_2630_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2632_, lean_object* v_constName_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2640_, lean_object* v_constName_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2640_, v_constName_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
lean_dec(v___y_2643_);
lean_dec_ref(v___y_2642_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2648_, lean_object* v_attrName_2649_, lean_object* v_declName_2650_, lean_object* v_asyncPrefix_x3f_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2649_, v_declName_2650_, v_asyncPrefix_x3f_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2658_, lean_object* v_attrName_2659_, lean_object* v_declName_2660_, lean_object* v_asyncPrefix_x3f_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2658_, v_attrName_2659_, v_declName_2660_, v_asyncPrefix_x3f_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2668_, lean_object* v_attrName_2669_, lean_object* v_declName_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v___x_2676_; 
v___x_2676_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2669_, v_declName_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2677_, lean_object* v_attrName_2678_, lean_object* v_declName_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2677_, v_attrName_2678_, v_declName_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2686_, lean_object* v_ref_2687_, lean_object* v_constName_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2687_, v_constName_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2695_, lean_object* v_ref_2696_, lean_object* v_constName_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2695_, v_ref_2696_, v_constName_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v_ref_2696_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2704_, lean_object* v_msg_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2712_, lean_object* v_msg_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2712_, v_msg_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2720_, lean_object* v_ref_2721_, lean_object* v_msg_2722_, lean_object* v_declHint_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2721_, v_msg_2722_, v_declHint_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2730_, lean_object* v_ref_2731_, lean_object* v_msg_2732_, lean_object* v_declHint_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2730_, v_ref_2731_, v_msg_2732_, v_declHint_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v_ref_2731_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2740_, lean_object* v_declHint_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v___x_2747_; 
v___x_2747_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2740_, v_declHint_2741_, v___y_2745_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2748_, lean_object* v_declHint_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2748_, v_declHint_2749_, v___y_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec(v___y_2751_);
lean_dec_ref(v___y_2750_);
return v_res_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2756_, lean_object* v_ref_2757_, lean_object* v_msg_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2757_, v_msg_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2765_, lean_object* v_ref_2766_, lean_object* v_msg_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2765_, v_ref_2766_, v_msg_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v_ref_2766_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2774_, lean_object* v___y_2775_){
_start:
{
uint8_t v___x_2777_; 
v___x_2777_ = l_Lean_Expr_hasMVar(v_e_2774_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; 
v___x_2778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2778_, 0, v_e_2774_);
return v___x_2778_;
}
else
{
lean_object* v___x_2779_; lean_object* v_mctx_2780_; lean_object* v___x_2781_; lean_object* v_fst_2782_; lean_object* v_snd_2783_; lean_object* v___x_2784_; lean_object* v_cache_2785_; lean_object* v_zetaDeltaFVarIds_2786_; lean_object* v_postponed_2787_; lean_object* v_diag_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2797_; 
v___x_2779_ = lean_st_ref_get(v___y_2775_);
v_mctx_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc_ref(v_mctx_2780_);
lean_dec(v___x_2779_);
v___x_2781_ = l_Lean_instantiateMVarsCore(v_mctx_2780_, v_e_2774_);
v_fst_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_fst_2782_);
v_snd_2783_ = lean_ctor_get(v___x_2781_, 1);
lean_inc(v_snd_2783_);
lean_dec_ref(v___x_2781_);
v___x_2784_ = lean_st_ref_take(v___y_2775_);
v_cache_2785_ = lean_ctor_get(v___x_2784_, 1);
v_zetaDeltaFVarIds_2786_ = lean_ctor_get(v___x_2784_, 2);
v_postponed_2787_ = lean_ctor_get(v___x_2784_, 3);
v_diag_2788_ = lean_ctor_get(v___x_2784_, 4);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2797_ == 0)
{
lean_object* v_unused_2798_; 
v_unused_2798_ = lean_ctor_get(v___x_2784_, 0);
lean_dec(v_unused_2798_);
v___x_2790_ = v___x_2784_;
v_isShared_2791_ = v_isSharedCheck_2797_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_diag_2788_);
lean_inc(v_postponed_2787_);
lean_inc(v_zetaDeltaFVarIds_2786_);
lean_inc(v_cache_2785_);
lean_dec(v___x_2784_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2797_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v_snd_2783_);
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_snd_2783_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_cache_2785_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_zetaDeltaFVarIds_2786_);
lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_postponed_2787_);
lean_ctor_set(v_reuseFailAlloc_2796_, 4, v_diag_2788_);
v___x_2793_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_st_ref_put(v___y_2775_, v___x_2793_);
v___x_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2795_, 0, v_fst_2782_);
return v___x_2795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2799_, v___y_2800_);
lean_dec(v___y_2800_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v___x_2809_; 
v___x_2809_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2803_, v___y_2805_);
return v___x_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2817_, lean_object* v_info_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; lean_object* v_env_2823_; lean_object* v_nextMacroScope_2824_; lean_object* v_ngen_2825_; lean_object* v_auxDeclNGen_2826_; lean_object* v_traceState_2827_; lean_object* v_recordedDeps_2828_; lean_object* v_messages_2829_; lean_object* v_infoState_2830_; lean_object* v_snapshotTasks_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2858_; 
v___x_2822_ = lean_st_ref_take(v___y_2820_);
v_env_2823_ = lean_ctor_get(v___x_2822_, 0);
v_nextMacroScope_2824_ = lean_ctor_get(v___x_2822_, 1);
v_ngen_2825_ = lean_ctor_get(v___x_2822_, 2);
v_auxDeclNGen_2826_ = lean_ctor_get(v___x_2822_, 3);
v_traceState_2827_ = lean_ctor_get(v___x_2822_, 4);
v_recordedDeps_2828_ = lean_ctor_get(v___x_2822_, 6);
v_messages_2829_ = lean_ctor_get(v___x_2822_, 7);
v_infoState_2830_ = lean_ctor_get(v___x_2822_, 8);
v_snapshotTasks_2831_ = lean_ctor_get(v___x_2822_, 9);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v___x_2822_, 5);
lean_dec(v_unused_2859_);
v___x_2833_ = v___x_2822_;
v_isShared_2834_ = v_isSharedCheck_2858_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_snapshotTasks_2831_);
lean_inc(v_infoState_2830_);
lean_inc(v_messages_2829_);
lean_inc(v_recordedDeps_2828_);
lean_inc(v_traceState_2827_);
lean_inc(v_auxDeclNGen_2826_);
lean_inc(v_ngen_2825_);
lean_inc(v_nextMacroScope_2824_);
lean_inc(v_env_2823_);
lean_dec(v___x_2822_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2858_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2835_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2823_, v_matcherName_2817_, v_info_2818_);
v___x_2836_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 5, v___x_2836_);
lean_ctor_set(v___x_2833_, 0, v___x_2835_);
v___x_2838_ = v___x_2833_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_nextMacroScope_2824_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_ngen_2825_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_auxDeclNGen_2826_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_traceState_2827_);
lean_ctor_set(v_reuseFailAlloc_2857_, 5, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2857_, 6, v_recordedDeps_2828_);
lean_ctor_set(v_reuseFailAlloc_2857_, 7, v_messages_2829_);
lean_ctor_set(v_reuseFailAlloc_2857_, 8, v_infoState_2830_);
lean_ctor_set(v_reuseFailAlloc_2857_, 9, v_snapshotTasks_2831_);
v___x_2838_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v_mctx_2841_; lean_object* v_zetaDeltaFVarIds_2842_; lean_object* v_postponed_2843_; lean_object* v_diag_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2855_; 
v___x_2839_ = lean_st_ref_put(v___y_2820_, v___x_2838_);
v___x_2840_ = lean_st_ref_take(v___y_2819_);
v_mctx_2841_ = lean_ctor_get(v___x_2840_, 0);
v_zetaDeltaFVarIds_2842_ = lean_ctor_get(v___x_2840_, 2);
v_postponed_2843_ = lean_ctor_get(v___x_2840_, 3);
v_diag_2844_ = lean_ctor_get(v___x_2840_, 4);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2840_, 1);
lean_dec(v_unused_2856_);
v___x_2846_ = v___x_2840_;
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_diag_2844_);
lean_inc(v_postponed_2843_);
lean_inc(v_zetaDeltaFVarIds_2842_);
lean_inc(v_mctx_2841_);
lean_dec(v___x_2840_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2848_ = lean_box(0);
v___x_2849_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 1, v___x_2849_);
v___x_2851_ = v___x_2846_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_mctx_2841_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_zetaDeltaFVarIds_2842_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_postponed_2843_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_diag_2844_);
v___x_2851_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_st_ref_put(v___y_2819_, v___x_2851_);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2848_);
return v___x_2853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2860_, lean_object* v_info_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2860_, v_info_2861_, v___y_2862_, v___y_2863_);
lean_dec(v___y_2863_);
lean_dec(v___y_2862_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2866_, lean_object* v_info_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2866_, v_info_2867_, v___y_2869_, v___y_2871_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2874_, lean_object* v_info_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2874_, v_info_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
lean_dec(v___y_2879_);
lean_dec_ref(v___y_2878_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2882_, lean_object* v___x_2883_, lean_object* v_newEqs1_2884_, uint8_t v___x_2885_, uint8_t v___x_2886_, uint8_t v___x_2887_, lean_object* v_ism1_x27_2888_, lean_object* v_ism2_x27_2889_, lean_object* v_newRefls1_2890_, lean_object* v_newEqs2_2891_, lean_object* v_newRefls2_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2898_ = l_Lean_mkAppN(v_motive_2882_, v___x_2883_);
v___x_2899_ = l_Array_append___redArg(v_newEqs1_2884_, v_newEqs2_2891_);
v___x_2900_ = l_Lean_Meta_mkForallFVars(v___x_2899_, v___x_2898_, v___x_2885_, v___x_2886_, v___x_2886_, v___x_2887_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec_ref(v___x_2899_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_a_2901_);
lean_dec_ref_known(v___x_2900_, 1);
v___x_2902_ = l_Array_append___redArg(v_ism1_x27_2888_, v_ism2_x27_2889_);
v___x_2903_ = l_Lean_Meta_mkLambdaFVars(v___x_2902_, v_a_2901_, v___x_2885_, v___x_2886_, v___x_2885_, v___x_2886_, v___x_2887_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
lean_dec_ref(v___x_2902_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2913_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2906_ = v___x_2903_;
v_isShared_2907_ = v_isSharedCheck_2913_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2903_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2913_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2908_ = l_Array_append___redArg(v_newRefls1_2890_, v_newRefls2_2892_);
v___x_2909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2909_, 0, v_a_2904_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2909_);
v___x_2911_ = v___x_2906_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v_newRefls1_2890_);
v_a_2914_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2903_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2903_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec_ref(v_newRefls1_2890_);
lean_dec_ref(v_ism1_x27_2888_);
v_a_2922_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2900_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2900_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2930_, lean_object* v___x_2931_, lean_object* v_newEqs1_2932_, lean_object* v___x_2933_, lean_object* v___x_2934_, lean_object* v___x_2935_, lean_object* v_ism1_x27_2936_, lean_object* v_ism2_x27_2937_, lean_object* v_newRefls1_2938_, lean_object* v_newEqs2_2939_, lean_object* v_newRefls2_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
uint8_t v___x_14959__boxed_2946_; uint8_t v___x_14960__boxed_2947_; uint8_t v___x_14961__boxed_2948_; lean_object* v_res_2949_; 
v___x_14959__boxed_2946_ = lean_unbox(v___x_2933_);
v___x_14960__boxed_2947_ = lean_unbox(v___x_2934_);
v___x_14961__boxed_2948_ = lean_unbox(v___x_2935_);
v_res_2949_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2930_, v___x_2931_, v_newEqs1_2932_, v___x_14959__boxed_2946_, v___x_14960__boxed_2947_, v___x_14961__boxed_2948_, v_ism1_x27_2936_, v_ism2_x27_2937_, v_newRefls1_2938_, v_newEqs2_2939_, v_newRefls2_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
lean_dec(v___y_2944_);
lean_dec_ref(v___y_2943_);
lean_dec(v___y_2942_);
lean_dec_ref(v___y_2941_);
lean_dec_ref(v_newRefls2_2940_);
lean_dec_ref(v_newEqs2_2939_);
lean_dec_ref(v_ism2_x27_2937_);
lean_dec_ref(v___x_2931_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2950_, lean_object* v___x_2951_, uint8_t v___x_2952_, uint8_t v___x_2953_, uint8_t v___x_2954_, lean_object* v_ism1_x27_2955_, lean_object* v_ism2_x27_2956_, lean_object* v_is_2957_, lean_object* v___x_2958_, lean_object* v_newEqs1_2959_, lean_object* v_newRefls1_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___f_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2966_ = lean_box(v___x_2952_);
v___x_2967_ = lean_box(v___x_2953_);
v___x_2968_ = lean_box(v___x_2954_);
lean_inc_ref(v_ism2_x27_2956_);
v___f_2969_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2969_, 0, v_motive_2950_);
lean_closure_set(v___f_2969_, 1, v___x_2951_);
lean_closure_set(v___f_2969_, 2, v_newEqs1_2959_);
lean_closure_set(v___f_2969_, 3, v___x_2966_);
lean_closure_set(v___f_2969_, 4, v___x_2967_);
lean_closure_set(v___f_2969_, 5, v___x_2968_);
lean_closure_set(v___f_2969_, 6, v_ism1_x27_2955_);
lean_closure_set(v___f_2969_, 7, v_ism2_x27_2956_);
lean_closure_set(v___f_2969_, 8, v_newRefls1_2960_);
v___x_2970_ = lean_array_push(v_is_2957_, v___x_2958_);
v___x_2971_ = l_Lean_Meta_withNewEqs___redArg(v___x_2970_, v_ism2_x27_2956_, v___f_2969_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2972_, lean_object* v___x_2973_, lean_object* v___x_2974_, lean_object* v___x_2975_, lean_object* v___x_2976_, lean_object* v_ism1_x27_2977_, lean_object* v_ism2_x27_2978_, lean_object* v_is_2979_, lean_object* v___x_2980_, lean_object* v_newEqs1_2981_, lean_object* v_newRefls1_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
uint8_t v___x_15050__boxed_2988_; uint8_t v___x_15051__boxed_2989_; uint8_t v___x_15052__boxed_2990_; lean_object* v_res_2991_; 
v___x_15050__boxed_2988_ = lean_unbox(v___x_2974_);
v___x_15051__boxed_2989_ = lean_unbox(v___x_2975_);
v___x_15052__boxed_2990_ = lean_unbox(v___x_2976_);
v_res_2991_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2972_, v___x_2973_, v___x_15050__boxed_2988_, v___x_15051__boxed_2989_, v___x_15052__boxed_2990_, v_ism1_x27_2977_, v_ism2_x27_2978_, v_is_2979_, v___x_2980_, v_newEqs1_2981_, v_newRefls1_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec(v___y_2984_);
lean_dec_ref(v___y_2983_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_2992_, uint8_t v___x_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Lean_addDecl(v___x_2992_, v___x_2993_, v___y_2996_, v___y_2997_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3000_, lean_object* v___x_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
uint8_t v___x_15092__boxed_3007_; lean_object* v_res_3008_; 
v___x_15092__boxed_3007_ = lean_unbox(v___x_3001_);
v_res_3008_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3000_, v___x_15092__boxed_3007_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
lean_dec(v___y_3003_);
lean_dec_ref(v___y_3002_);
return v_res_3008_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3011_ = l_Lean_stringToMessageData(v___x_3010_);
return v___x_3011_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3014_ = l_Lean_stringToMessageData(v___x_3013_);
return v___x_3014_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = lean_box(0);
v___x_3021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3022_ = l_Lean_mkConst(v___x_3021_, v___x_3020_);
return v___x_3022_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3025_ = l_Lean_stringToMessageData(v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3026_, lean_object* v_a_3027_, lean_object* v___x_3028_, lean_object* v_zs1_3029_, lean_object* v_snd_3030_, uint8_t v___x_3031_, uint8_t v___x_3032_, uint8_t v___x_3033_, lean_object* v_alts_3034_, lean_object* v_zs2_3035_, lean_object* v___ctorRet2_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3042_ = lean_array_get_borrowed(v___x_3026_, v_a_3027_, v___x_3028_);
lean_inc_ref(v_zs1_3029_);
v___x_3043_ = l_Array_append___redArg(v_zs1_3029_, v_zs2_3035_);
lean_inc(v___x_3042_);
v___x_3044_ = l_Lean_Meta_instantiateForall(v___x_3042_, v___x_3043_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
v___x_3046_ = lean_box(0);
v___x_3047_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3045_, v___x_3046_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___x_3049_ = l_Lean_Expr_mvarId_x21(v_a_3048_);
v___x_3050_ = lean_array_get_size(v_snd_3030_);
v___x_3051_ = lean_box(0);
v___x_3052_ = lean_box(0);
lean_inc_ref(v___y_3039_);
v___x_3053_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3050_, v___x_3049_, v___x_3051_, v___x_3052_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v___x_3053_, 1);
if (lean_obj_tag(v_a_3054_) == 1)
{
lean_object* v_val_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3102_; 
v_val_3055_ = lean_ctor_get(v_a_3054_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_a_3054_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3057_ = v_a_3054_;
v_isShared_3058_ = v_isSharedCheck_3102_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_val_3055_);
lean_dec(v_a_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3102_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v_fst_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3100_; 
v_fst_3059_ = lean_ctor_get(v_val_3055_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v_val_3055_);
if (v_isSharedCheck_3100_ == 0)
{
lean_object* v_unused_3101_; 
v_unused_3101_ = lean_ctor_get(v_val_3055_, 1);
lean_dec(v_unused_3101_);
v___x_3061_ = v_val_3055_;
v_isShared_3062_ = v_isSharedCheck_3100_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_fst_3059_);
lean_dec(v_val_3055_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3100_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___y_3064_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v___x_3092_ = lean_array_get_borrowed(v___x_3026_, v_alts_3034_, v___x_3028_);
v___x_3093_ = lean_array_get_size(v_zs1_3029_);
lean_dec_ref(v_zs1_3029_);
v___x_3094_ = lean_unsigned_to_nat(0u);
v___x_3095_ = lean_nat_dec_eq(v___x_3093_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_inc(v___x_3092_);
v___y_3064_ = v___x_3092_;
goto v___jp_3063_;
}
else
{
lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3096_ = lean_array_get_size(v_zs2_3035_);
v___x_3097_ = lean_nat_dec_eq(v___x_3096_, v___x_3094_);
if (v___x_3097_ == 0)
{
lean_inc(v___x_3092_);
v___y_3064_ = v___x_3092_;
goto v___jp_3063_;
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3092_);
v___x_3099_ = l_Lean_Expr_app___override(v___x_3092_, v___x_3098_);
v___y_3064_ = v___x_3099_;
goto v___jp_3063_;
}
}
v___jp_3063_:
{
uint8_t v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = 0;
v___x_3066_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3066_, 0, v___x_3065_);
lean_ctor_set_uint8(v___x_3066_, 1, v___x_3031_);
lean_ctor_set_uint8(v___x_3066_, 2, v___x_3032_);
lean_ctor_set_uint8(v___x_3066_, 3, v___x_3031_);
lean_inc_ref(v___y_3064_);
lean_inc(v_fst_3059_);
v___x_3067_ = l_Lean_MVarId_apply(v_fst_3059_, v___y_3064_, v___x_3066_, v___x_3052_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
if (lean_obj_tag(v_a_3068_) == 0)
{
lean_object* v___x_3069_; 
lean_dec_ref(v___y_3064_);
lean_del_object(v___x_3061_);
lean_dec(v_fst_3059_);
lean_del_object(v___x_3057_);
v___x_3069_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3048_, v___y_3038_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3071_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3070_);
lean_dec_ref_known(v___x_3069_, 1);
v___x_3071_ = l_Lean_Meta_mkLambdaFVars(v___x_3043_, v_a_3070_, v___x_3032_, v___x_3031_, v___x_3032_, v___x_3031_, v___x_3033_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec_ref(v___x_3043_);
return v___x_3071_;
}
else
{
lean_dec_ref(v___x_3043_);
return v___x_3069_;
}
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3075_; 
lean_dec(v_a_3068_);
lean_dec(v_a_3048_);
lean_dec_ref(v___x_3043_);
v___x_3072_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3073_ = l_Lean_MessageData_ofExpr(v___y_3064_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set_tag(v___x_3061_, 7);
lean_ctor_set(v___x_3061_, 1, v___x_3073_);
lean_ctor_set(v___x_3061_, 0, v___x_3072_);
v___x_3075_ = v___x_3061_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3083_, 1, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3079_; 
v___x_3076_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3075_);
lean_ctor_set(v___x_3077_, 1, v___x_3076_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v_fst_3059_);
v___x_3079_ = v___x_3057_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_fst_3059_);
v___x_3079_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3077_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
v___x_3081_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3080_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v___y_3064_);
lean_del_object(v___x_3061_);
lean_dec(v_fst_3059_);
lean_del_object(v___x_3057_);
lean_dec(v_a_3048_);
lean_dec_ref(v___x_3043_);
v_a_3084_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3067_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3067_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
lean_dec(v_a_3054_);
lean_dec(v_a_3048_);
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_zs1_3029_);
v___x_3103_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3104_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3103_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
return v___x_3104_;
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec(v_a_3048_);
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_zs1_3029_);
v_a_3105_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3053_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3053_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
else
{
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_zs1_3029_);
return v___x_3047_;
}
}
else
{
lean_dec_ref(v___x_3043_);
lean_dec_ref(v_zs1_3029_);
return v___x_3044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3113_, lean_object* v_a_3114_, lean_object* v___x_3115_, lean_object* v_zs1_3116_, lean_object* v_snd_3117_, lean_object* v___x_3118_, lean_object* v___x_3119_, lean_object* v___x_3120_, lean_object* v_alts_3121_, lean_object* v_zs2_3122_, lean_object* v___ctorRet2_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
uint8_t v___x_15152__boxed_3129_; uint8_t v___x_15153__boxed_3130_; uint8_t v___x_15154__boxed_3131_; lean_object* v_res_3132_; 
v___x_15152__boxed_3129_ = lean_unbox(v___x_3118_);
v___x_15153__boxed_3130_ = lean_unbox(v___x_3119_);
v___x_15154__boxed_3131_ = lean_unbox(v___x_3120_);
v_res_3132_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3113_, v_a_3114_, v___x_3115_, v_zs1_3116_, v_snd_3117_, v___x_15152__boxed_3129_, v___x_15153__boxed_3130_, v___x_15154__boxed_3131_, v_alts_3121_, v_zs2_3122_, v___ctorRet2_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec_ref(v___ctorRet2_3123_);
lean_dec_ref(v_zs2_3122_);
lean_dec_ref(v_alts_3121_);
lean_dec_ref(v_snd_3117_);
lean_dec(v___x_3115_);
lean_dec_ref(v_a_3114_);
lean_dec_ref(v___x_3113_);
return v_res_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3133_, lean_object* v_a_3134_, lean_object* v___x_3135_, lean_object* v_snd_3136_, uint8_t v___x_3137_, uint8_t v___x_3138_, uint8_t v___x_3139_, lean_object* v_alts_3140_, lean_object* v_a_3141_, lean_object* v_zs1_3142_, lean_object* v___ctorRet1_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___f_3152_; lean_object* v___x_3153_; 
v___x_3149_ = lean_box(v___x_3137_);
v___x_3150_ = lean_box(v___x_3138_);
v___x_3151_ = lean_box(v___x_3139_);
v___f_3152_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3152_, 0, v___x_3133_);
lean_closure_set(v___f_3152_, 1, v_a_3134_);
lean_closure_set(v___f_3152_, 2, v___x_3135_);
lean_closure_set(v___f_3152_, 3, v_zs1_3142_);
lean_closure_set(v___f_3152_, 4, v_snd_3136_);
lean_closure_set(v___f_3152_, 5, v___x_3149_);
lean_closure_set(v___f_3152_, 6, v___x_3150_);
lean_closure_set(v___f_3152_, 7, v___x_3151_);
lean_closure_set(v___f_3152_, 8, v_alts_3140_);
v___x_3153_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3141_, v___f_3152_, v___x_3138_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3154_, lean_object* v_a_3155_, lean_object* v___x_3156_, lean_object* v_snd_3157_, lean_object* v___x_3158_, lean_object* v___x_3159_, lean_object* v___x_3160_, lean_object* v_alts_3161_, lean_object* v_a_3162_, lean_object* v_zs1_3163_, lean_object* v___ctorRet1_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
uint8_t v___x_15351__boxed_3170_; uint8_t v___x_15352__boxed_3171_; uint8_t v___x_15353__boxed_3172_; lean_object* v_res_3173_; 
v___x_15351__boxed_3170_ = lean_unbox(v___x_3158_);
v___x_15352__boxed_3171_ = lean_unbox(v___x_3159_);
v___x_15353__boxed_3172_ = lean_unbox(v___x_3160_);
v_res_3173_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3154_, v_a_3155_, v___x_3156_, v_snd_3157_, v___x_15351__boxed_3170_, v___x_15352__boxed_3171_, v___x_15353__boxed_3172_, v_alts_3161_, v_a_3162_, v_zs1_3163_, v___ctorRet1_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec_ref(v___ctorRet1_3164_);
return v_res_3173_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3174_, lean_object* v_params_3175_, lean_object* v_a_3176_, lean_object* v_snd_3177_, lean_object* v_alts_3178_, size_t v_sz_3179_, size_t v_i_3180_, lean_object* v_bs_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
uint8_t v___x_3187_; 
v___x_3187_ = lean_usize_dec_lt(v_i_3180_, v_sz_3179_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; 
lean_dec_ref(v_alts_3178_);
lean_dec_ref(v_snd_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_tail_3174_);
v___x_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3188_, 0, v_bs_3181_);
return v___x_3188_;
}
else
{
lean_object* v___x_3189_; uint8_t v___x_3190_; uint8_t v___x_3191_; lean_object* v_v_3192_; lean_object* v___x_3193_; lean_object* v_bs_x27_3194_; lean_object* v___y_3196_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3189_ = l_Lean_instInhabitedExpr;
v___x_3190_ = 0;
v___x_3191_ = 1;
v_v_3192_ = lean_array_uget(v_bs_3181_, v_i_3180_);
v___x_3193_ = lean_unsigned_to_nat(0u);
v_bs_x27_3194_ = lean_array_uset(v_bs_3181_, v_i_3180_, v___x_3193_);
v___x_3210_ = lean_usize_to_nat(v_i_3180_);
lean_inc(v_tail_3174_);
v___x_3211_ = l_Lean_mkConst(v_v_3192_, v_tail_3174_);
v___x_3212_ = l_Lean_mkAppN(v___x_3211_, v_params_3175_);
lean_inc(v___y_3185_);
lean_inc_ref(v___y_3184_);
lean_inc(v___y_3183_);
lean_inc_ref(v___y_3182_);
v___x_3213_ = lean_infer_type(v___x_3212_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v_a_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___f_3218_; lean_object* v___x_3219_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc_n(v_a_3214_, 2);
lean_dec_ref_known(v___x_3213_, 1);
v___x_3215_ = lean_box(v___x_3187_);
v___x_3216_ = lean_box(v___x_3190_);
v___x_3217_ = lean_box(v___x_3191_);
lean_inc_ref(v_alts_3178_);
lean_inc_ref(v_snd_3177_);
lean_inc_ref(v_a_3176_);
v___f_3218_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3218_, 0, v___x_3189_);
lean_closure_set(v___f_3218_, 1, v_a_3176_);
lean_closure_set(v___f_3218_, 2, v___x_3210_);
lean_closure_set(v___f_3218_, 3, v_snd_3177_);
lean_closure_set(v___f_3218_, 4, v___x_3215_);
lean_closure_set(v___f_3218_, 5, v___x_3216_);
lean_closure_set(v___f_3218_, 6, v___x_3217_);
lean_closure_set(v___f_3218_, 7, v_alts_3178_);
lean_closure_set(v___f_3218_, 8, v_a_3214_);
v___x_3219_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3214_, v___f_3218_, v___x_3190_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
v___y_3196_ = v___x_3219_;
goto v___jp_3195_;
}
else
{
lean_dec(v___x_3210_);
v___y_3196_ = v___x_3213_;
goto v___jp_3195_;
}
v___jp_3195_:
{
if (lean_obj_tag(v___y_3196_) == 0)
{
lean_object* v_a_3197_; size_t v___x_3198_; size_t v___x_3199_; lean_object* v___x_3200_; 
v_a_3197_ = lean_ctor_get(v___y_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___y_3196_, 1);
v___x_3198_ = ((size_t)1ULL);
v___x_3199_ = lean_usize_add(v_i_3180_, v___x_3198_);
v___x_3200_ = lean_array_uset(v_bs_x27_3194_, v_i_3180_, v_a_3197_);
v_i_3180_ = v___x_3199_;
v_bs_3181_ = v___x_3200_;
goto _start;
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v_bs_x27_3194_);
lean_dec_ref(v_alts_3178_);
lean_dec_ref(v_snd_3177_);
lean_dec_ref(v_a_3176_);
lean_dec(v_tail_3174_);
v_a_3202_ = lean_ctor_get(v___y_3196_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___y_3196_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___y_3196_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___y_3196_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3220_, lean_object* v_params_3221_, lean_object* v_a_3222_, lean_object* v_snd_3223_, lean_object* v_alts_3224_, lean_object* v_sz_3225_, lean_object* v_i_3226_, lean_object* v_bs_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
size_t v_sz_boxed_3233_; size_t v_i_boxed_3234_; lean_object* v_res_3235_; 
v_sz_boxed_3233_ = lean_unbox_usize(v_sz_3225_);
lean_dec(v_sz_3225_);
v_i_boxed_3234_ = lean_unbox_usize(v_i_3226_);
lean_dec(v_i_3226_);
v_res_3235_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3220_, v_params_3221_, v_a_3222_, v_snd_3223_, v_alts_3224_, v_sz_boxed_3233_, v_i_boxed_3234_, v_bs_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec_ref(v_params_3221_);
return v_res_3235_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v___x_3236_ = lean_box(0);
v___x_3237_ = lean_unsigned_to_nat(16u);
v___x_3238_ = lean_mk_array(v___x_3237_, v___x_3236_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3239_, lean_object* v___x_3240_, uint8_t v___x_3241_, uint8_t v___x_3242_, uint8_t v___x_3243_, lean_object* v_ism1_x27_3244_, lean_object* v_is_3245_, lean_object* v___x_3246_, lean_object* v___x_3247_, lean_object* v___x_3248_, lean_object* v___x_3249_, lean_object* v_params_3250_, lean_object* v___x_3251_, lean_object* v___x_3252_, lean_object* v_heq_3253_, lean_object* v_val_3254_, lean_object* v_tail_3255_, lean_object* v_alts_3256_, size_t v_sz_3257_, size_t v___x_3258_, lean_object* v___x_3259_, lean_object* v___x_3260_, lean_object* v_declName_3261_, lean_object* v_levelParams_3262_, lean_object* v_numIndices_3263_, lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v_numParams_3266_, lean_object* v_snd_3267_, lean_object* v_ism2_x27_3268_, lean_object* v_x_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___f_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3275_ = lean_box(v___x_3241_);
v___x_3276_ = lean_box(v___x_3242_);
v___x_3277_ = lean_box(v___x_3243_);
lean_inc_ref(v___x_3246_);
lean_inc_ref_n(v_is_3245_, 2);
lean_inc_ref(v_ism1_x27_3244_);
lean_inc_ref(v_motive_3239_);
v___f_3278_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3278_, 0, v_motive_3239_);
lean_closure_set(v___f_3278_, 1, v___x_3240_);
lean_closure_set(v___f_3278_, 2, v___x_3275_);
lean_closure_set(v___f_3278_, 3, v___x_3276_);
lean_closure_set(v___f_3278_, 4, v___x_3277_);
lean_closure_set(v___f_3278_, 5, v_ism1_x27_3244_);
lean_closure_set(v___f_3278_, 6, v_ism2_x27_3268_);
lean_closure_set(v___f_3278_, 7, v_is_3245_);
lean_closure_set(v___f_3278_, 8, v___x_3246_);
lean_inc_ref(v___x_3247_);
v___x_3279_ = lean_array_push(v_is_3245_, v___x_3247_);
v___x_3280_ = l_Lean_Meta_withNewEqs___redArg(v___x_3279_, v_ism1_x27_3244_, v___f_3278_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v_fst_3282_; lean_object* v_snd_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3384_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___x_3280_, 1);
v_fst_3282_ = lean_ctor_get(v_a_3281_, 0);
v_snd_3283_ = lean_ctor_get(v_a_3281_, 1);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_a_3281_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3285_ = v_a_3281_;
v_isShared_3286_ = v_isSharedCheck_3384_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_snd_3283_);
lean_inc(v_fst_3282_);
lean_dec(v_a_3281_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3384_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3287_ = l_Lean_mkConst(v___x_3248_, v___x_3249_);
v___x_3288_ = l_Lean_mkAppN(v___x_3287_, v_params_3250_);
v___x_3289_ = l_Lean_Expr_app___override(v___x_3288_, v_fst_3282_);
lean_inc_ref(v_is_3245_);
v___x_3290_ = l_Array_append___redArg(v_is_3245_, v___x_3251_);
v___x_3291_ = l_Array_append___redArg(v___x_3290_, v_is_3245_);
v___x_3292_ = l_Array_append___redArg(v___x_3291_, v___x_3252_);
v___x_3293_ = l_Lean_mkAppN(v___x_3289_, v___x_3292_);
lean_dec_ref(v___x_3292_);
lean_inc_ref(v_heq_3253_);
v___x_3294_ = l_Lean_Expr_app___override(v___x_3293_, v_heq_3253_);
v___x_3295_ = l_Lean_InductiveVal_numCtors(v_val_3254_);
lean_inc_ref(v___x_3294_);
v___x_3296_ = l_Lean_Meta_inferArgumentTypesN(v___x_3295_, v___x_3294_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; lean_object* v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref_known(v___x_3296_, 1);
lean_inc_ref(v_alts_3256_);
lean_inc(v_snd_3283_);
v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3255_, v_params_3250_, v_a_3297_, v_snd_3283_, v_alts_3256_, v_sz_3257_, v___x_3258_, v___x_3259_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3298_, 1);
v___x_3300_ = l_Lean_mkAppN(v___x_3294_, v_a_3299_);
lean_dec(v_a_3299_);
v___x_3301_ = l_Lean_mkAppN(v___x_3300_, v_snd_3283_);
lean_dec(v_snd_3283_);
lean_inc_ref(v___x_3260_);
v___x_3302_ = lean_array_push(v___x_3260_, v_motive_3239_);
v___x_3303_ = l_Array_append___redArg(v_params_3250_, v___x_3302_);
lean_dec_ref(v___x_3302_);
v___x_3304_ = l_Array_append___redArg(v___x_3303_, v_is_3245_);
lean_dec_ref(v_is_3245_);
v___x_3305_ = lean_unsigned_to_nat(2u);
v___x_3306_ = lean_mk_empty_array_with_capacity(v___x_3305_);
v___x_3307_ = lean_array_push(v___x_3306_, v___x_3247_);
v___x_3308_ = lean_array_push(v___x_3307_, v___x_3246_);
v___x_3309_ = l_Array_append___redArg(v___x_3304_, v___x_3308_);
lean_dec_ref(v___x_3308_);
v___x_3310_ = lean_array_push(v___x_3260_, v_heq_3253_);
v___x_3311_ = l_Array_append___redArg(v___x_3309_, v___x_3310_);
lean_dec_ref(v___x_3310_);
v___x_3312_ = l_Array_append___redArg(v___x_3311_, v_alts_3256_);
lean_dec_ref(v_alts_3256_);
v___x_3313_ = l_Lean_Meta_mkLambdaFVars(v___x_3312_, v___x_3301_, v___x_3241_, v___x_3242_, v___x_3241_, v___x_3242_, v___x_3243_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
lean_dec_ref(v___x_3312_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_object* v_a_3314_; lean_object* v___x_3315_; 
v_a_3314_ = lean_ctor_get(v___x_3313_, 0);
lean_inc_n(v_a_3314_, 2);
lean_dec_ref_known(v___x_3313_, 1);
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3271_);
lean_inc_ref(v___y_3270_);
v___x_3315_ = lean_infer_type(v_a_3314_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3315_) == 0)
{
lean_object* v_a_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3351_; 
v_a_3316_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_a_3316_);
lean_dec_ref_known(v___x_3315_, 1);
v___x_3317_ = lean_box(1);
lean_inc(v_declName_3261_);
v___x_3318_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3261_, v_levelParams_3262_, v_a_3316_, v_a_3314_, v___x_3317_, v___y_3273_);
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3351_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3351_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3324_; 
if (v_isShared_3322_ == 0)
{
lean_ctor_set_tag(v___x_3321_, 1);
v___x_3324_ = v___x_3321_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v_a_3319_);
v___x_3324_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
lean_object* v___x_3325_; lean_object* v___f_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3336_; 
v___x_3325_ = lean_box(v___x_3241_);
lean_inc_ref(v___x_3324_);
v___f_3326_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3326_, 0, v___x_3324_);
lean_closure_set(v___f_3326_, 1, v___x_3325_);
v___x_3327_ = lean_nat_add(v_numIndices_3263_, v___x_3264_);
lean_inc(v___x_3265_);
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3265_);
v___x_3329_ = lean_box(0);
v___x_3330_ = lean_mk_empty_array_with_capacity(v___x_3264_);
v___x_3331_ = lean_array_push(v___x_3330_, v___x_3329_);
v___x_3332_ = lean_array_push(v___x_3331_, v___x_3329_);
v___x_3333_ = lean_array_push(v___x_3332_, v___x_3329_);
v___x_3334_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 1, v___x_3334_);
lean_ctor_set(v___x_3285_, 0, v___x_3265_);
v___x_3336_ = v___x_3285_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3265_);
lean_ctor_set(v_reuseFailAlloc_3349_, 1, v___x_3334_);
v___x_3336_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
lean_object* v___x_3337_; uint8_t v___y_3339_; uint8_t v___x_3348_; 
v___x_3337_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3337_, 0, v_numParams_3266_);
lean_ctor_set(v___x_3337_, 1, v___x_3327_);
lean_ctor_set(v___x_3337_, 2, v_snd_3267_);
lean_ctor_set(v___x_3337_, 3, v___x_3328_);
lean_ctor_set(v___x_3337_, 4, v___x_3333_);
lean_ctor_set(v___x_3337_, 5, v___x_3336_);
v___x_3348_ = l_Lean_isPrivateName(v_declName_3261_);
if (v___x_3348_ == 0)
{
v___y_3339_ = v___x_3242_;
goto v___jp_3338_;
}
else
{
v___y_3339_ = v___x_3241_;
goto v___jp_3338_;
}
v___jp_3338_:
{
lean_object* v___x_3340_; 
v___x_3340_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3326_, v___y_3339_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3340_) == 0)
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
lean_dec_ref_known(v___x_3340_, 1);
v___x_3341_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3261_);
v___x_3342_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3341_, v_declName_3261_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3342_) == 0)
{
lean_object* v___x_3343_; uint8_t v___x_3344_; lean_object* v___x_3345_; 
lean_dec_ref_known(v___x_3342_, 1);
lean_inc_n(v_declName_3261_, 2);
v___x_3343_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3261_, v___x_3337_, v___y_3271_, v___y_3273_);
lean_dec_ref(v___x_3343_);
v___x_3344_ = 0;
v___x_3345_ = l_Lean_Meta_setInlineAttribute(v_declName_3261_, v___x_3344_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v___x_3346_; 
lean_dec_ref_known(v___x_3345_, 1);
v___x_3346_ = l_Lean_enableRealizationsForConst(v_declName_3261_, v___y_3272_, v___y_3273_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v___x_3347_; 
lean_dec_ref_known(v___x_3346_, 1);
v___x_3347_ = l_Lean_compileDecl(v___x_3324_, v___x_3242_, v___y_3272_, v___y_3273_);
return v___x_3347_;
}
else
{
lean_dec_ref(v___x_3324_);
return v___x_3346_;
}
}
else
{
lean_dec_ref(v___x_3324_);
lean_dec(v_declName_3261_);
return v___x_3345_;
}
}
else
{
lean_dec_ref_known(v___x_3337_, 6);
lean_dec_ref(v___x_3324_);
lean_dec(v_declName_3261_);
return v___x_3342_;
}
}
else
{
lean_dec_ref_known(v___x_3337_, 6);
lean_dec_ref(v___x_3324_);
lean_dec(v_declName_3261_);
return v___x_3340_;
}
}
}
}
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec(v_a_3314_);
lean_del_object(v___x_3285_);
lean_dec_ref(v_snd_3267_);
lean_dec(v_numParams_3266_);
lean_dec(v___x_3265_);
lean_dec(v_levelParams_3262_);
lean_dec(v_declName_3261_);
v_a_3352_ = lean_ctor_get(v___x_3315_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3315_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3315_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
else
{
lean_object* v_a_3360_; lean_object* v___x_3362_; uint8_t v_isShared_3363_; uint8_t v_isSharedCheck_3367_; 
lean_del_object(v___x_3285_);
lean_dec_ref(v_snd_3267_);
lean_dec(v_numParams_3266_);
lean_dec(v___x_3265_);
lean_dec(v_levelParams_3262_);
lean_dec(v_declName_3261_);
v_a_3360_ = lean_ctor_get(v___x_3313_, 0);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3313_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3362_ = v___x_3313_;
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
else
{
lean_inc(v_a_3360_);
lean_dec(v___x_3313_);
v___x_3362_ = lean_box(0);
v_isShared_3363_ = v_isSharedCheck_3367_;
goto v_resetjp_3361_;
}
v_resetjp_3361_:
{
lean_object* v___x_3365_; 
if (v_isShared_3363_ == 0)
{
v___x_3365_ = v___x_3362_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v_a_3360_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
}
else
{
lean_object* v_a_3368_; lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3375_; 
lean_dec_ref(v___x_3294_);
lean_del_object(v___x_3285_);
lean_dec(v_snd_3283_);
lean_dec_ref(v_snd_3267_);
lean_dec(v_numParams_3266_);
lean_dec(v___x_3265_);
lean_dec(v_levelParams_3262_);
lean_dec(v_declName_3261_);
lean_dec_ref(v___x_3260_);
lean_dec_ref(v_alts_3256_);
lean_dec_ref(v_heq_3253_);
lean_dec_ref(v_params_3250_);
lean_dec_ref(v___x_3247_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v_is_3245_);
lean_dec_ref(v_motive_3239_);
v_a_3368_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3370_ = v___x_3298_;
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
else
{
lean_inc(v_a_3368_);
lean_dec(v___x_3298_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3375_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3373_; 
if (v_isShared_3371_ == 0)
{
v___x_3373_ = v___x_3370_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec_ref(v___x_3294_);
lean_del_object(v___x_3285_);
lean_dec(v_snd_3283_);
lean_dec_ref(v_snd_3267_);
lean_dec(v_numParams_3266_);
lean_dec(v___x_3265_);
lean_dec(v_levelParams_3262_);
lean_dec(v_declName_3261_);
lean_dec_ref(v___x_3260_);
lean_dec_ref(v___x_3259_);
lean_dec_ref(v_alts_3256_);
lean_dec(v_tail_3255_);
lean_dec_ref(v_heq_3253_);
lean_dec_ref(v_params_3250_);
lean_dec_ref(v___x_3247_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v_is_3245_);
lean_dec_ref(v_motive_3239_);
v_a_3376_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3296_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3296_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v_snd_3267_);
lean_dec(v_numParams_3266_);
lean_dec(v___x_3265_);
lean_dec(v_levelParams_3262_);
lean_dec(v_declName_3261_);
lean_dec_ref(v___x_3260_);
lean_dec_ref(v___x_3259_);
lean_dec_ref(v_alts_3256_);
lean_dec(v_tail_3255_);
lean_dec_ref(v_heq_3253_);
lean_dec_ref(v_params_3250_);
lean_dec(v___x_3249_);
lean_dec(v___x_3248_);
lean_dec_ref(v___x_3247_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v_is_3245_);
lean_dec_ref(v_motive_3239_);
v_a_3385_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3280_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3280_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3390_; 
if (v_isShared_3388_ == 0)
{
v___x_3390_ = v___x_3387_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3385_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3393_ = _args[0];
lean_object* v___x_3394_ = _args[1];
lean_object* v___x_3395_ = _args[2];
lean_object* v___x_3396_ = _args[3];
lean_object* v___x_3397_ = _args[4];
lean_object* v_ism1_x27_3398_ = _args[5];
lean_object* v_is_3399_ = _args[6];
lean_object* v___x_3400_ = _args[7];
lean_object* v___x_3401_ = _args[8];
lean_object* v___x_3402_ = _args[9];
lean_object* v___x_3403_ = _args[10];
lean_object* v_params_3404_ = _args[11];
lean_object* v___x_3405_ = _args[12];
lean_object* v___x_3406_ = _args[13];
lean_object* v_heq_3407_ = _args[14];
lean_object* v_val_3408_ = _args[15];
lean_object* v_tail_3409_ = _args[16];
lean_object* v_alts_3410_ = _args[17];
lean_object* v_sz_3411_ = _args[18];
lean_object* v___x_3412_ = _args[19];
lean_object* v___x_3413_ = _args[20];
lean_object* v___x_3414_ = _args[21];
lean_object* v_declName_3415_ = _args[22];
lean_object* v_levelParams_3416_ = _args[23];
lean_object* v_numIndices_3417_ = _args[24];
lean_object* v___x_3418_ = _args[25];
lean_object* v___x_3419_ = _args[26];
lean_object* v_numParams_3420_ = _args[27];
lean_object* v_snd_3421_ = _args[28];
lean_object* v_ism2_x27_3422_ = _args[29];
lean_object* v_x_3423_ = _args[30];
lean_object* v___y_3424_ = _args[31];
lean_object* v___y_3425_ = _args[32];
lean_object* v___y_3426_ = _args[33];
lean_object* v___y_3427_ = _args[34];
lean_object* v___y_3428_ = _args[35];
_start:
{
uint8_t v___x_15490__boxed_3429_; uint8_t v___x_15491__boxed_3430_; uint8_t v___x_15492__boxed_3431_; size_t v_sz_boxed_3432_; size_t v___x_15501__boxed_3433_; lean_object* v_res_3434_; 
v___x_15490__boxed_3429_ = lean_unbox(v___x_3395_);
v___x_15491__boxed_3430_ = lean_unbox(v___x_3396_);
v___x_15492__boxed_3431_ = lean_unbox(v___x_3397_);
v_sz_boxed_3432_ = lean_unbox_usize(v_sz_3411_);
lean_dec(v_sz_3411_);
v___x_15501__boxed_3433_ = lean_unbox_usize(v___x_3412_);
lean_dec(v___x_3412_);
v_res_3434_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3393_, v___x_3394_, v___x_15490__boxed_3429_, v___x_15491__boxed_3430_, v___x_15492__boxed_3431_, v_ism1_x27_3398_, v_is_3399_, v___x_3400_, v___x_3401_, v___x_3402_, v___x_3403_, v_params_3404_, v___x_3405_, v___x_3406_, v_heq_3407_, v_val_3408_, v_tail_3409_, v_alts_3410_, v_sz_boxed_3432_, v___x_15501__boxed_3433_, v___x_3413_, v___x_3414_, v_declName_3415_, v_levelParams_3416_, v_numIndices_3417_, v___x_3418_, v___x_3419_, v_numParams_3420_, v_snd_3421_, v_ism2_x27_3422_, v_x_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec_ref(v_x_3423_);
lean_dec(v___x_3418_);
lean_dec(v_numIndices_3417_);
lean_dec_ref(v_val_3408_);
lean_dec_ref(v___x_3406_);
lean_dec_ref(v___x_3405_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3435_, lean_object* v___x_3436_, uint8_t v___x_3437_, uint8_t v___x_3438_, uint8_t v___x_3439_, lean_object* v_is_3440_, lean_object* v___x_3441_, lean_object* v___x_3442_, lean_object* v___x_3443_, lean_object* v___x_3444_, lean_object* v_params_3445_, lean_object* v___x_3446_, lean_object* v___x_3447_, lean_object* v_heq_3448_, lean_object* v_val_3449_, lean_object* v_tail_3450_, lean_object* v_alts_3451_, size_t v_sz_3452_, size_t v___x_3453_, lean_object* v___x_3454_, lean_object* v___x_3455_, lean_object* v_declName_3456_, lean_object* v_levelParams_3457_, lean_object* v_numIndices_3458_, lean_object* v___x_3459_, lean_object* v___x_3460_, lean_object* v_numParams_3461_, lean_object* v_snd_3462_, lean_object* v___x_3463_, lean_object* v___x_3464_, lean_object* v_ism1_x27_3465_, lean_object* v_x_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___f_3477_; lean_object* v___x_3478_; 
v___x_3472_ = lean_box(v___x_3437_);
v___x_3473_ = lean_box(v___x_3438_);
v___x_3474_ = lean_box(v___x_3439_);
v___x_3475_ = lean_box_usize(v_sz_3452_);
v___x_3476_ = lean_box_usize(v___x_3453_);
v___f_3477_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3477_, 0, v_motive_3435_);
lean_closure_set(v___f_3477_, 1, v___x_3436_);
lean_closure_set(v___f_3477_, 2, v___x_3472_);
lean_closure_set(v___f_3477_, 3, v___x_3473_);
lean_closure_set(v___f_3477_, 4, v___x_3474_);
lean_closure_set(v___f_3477_, 5, v_ism1_x27_3465_);
lean_closure_set(v___f_3477_, 6, v_is_3440_);
lean_closure_set(v___f_3477_, 7, v___x_3441_);
lean_closure_set(v___f_3477_, 8, v___x_3442_);
lean_closure_set(v___f_3477_, 9, v___x_3443_);
lean_closure_set(v___f_3477_, 10, v___x_3444_);
lean_closure_set(v___f_3477_, 11, v_params_3445_);
lean_closure_set(v___f_3477_, 12, v___x_3446_);
lean_closure_set(v___f_3477_, 13, v___x_3447_);
lean_closure_set(v___f_3477_, 14, v_heq_3448_);
lean_closure_set(v___f_3477_, 15, v_val_3449_);
lean_closure_set(v___f_3477_, 16, v_tail_3450_);
lean_closure_set(v___f_3477_, 17, v_alts_3451_);
lean_closure_set(v___f_3477_, 18, v___x_3475_);
lean_closure_set(v___f_3477_, 19, v___x_3476_);
lean_closure_set(v___f_3477_, 20, v___x_3454_);
lean_closure_set(v___f_3477_, 21, v___x_3455_);
lean_closure_set(v___f_3477_, 22, v_declName_3456_);
lean_closure_set(v___f_3477_, 23, v_levelParams_3457_);
lean_closure_set(v___f_3477_, 24, v_numIndices_3458_);
lean_closure_set(v___f_3477_, 25, v___x_3459_);
lean_closure_set(v___f_3477_, 26, v___x_3460_);
lean_closure_set(v___f_3477_, 27, v_numParams_3461_);
lean_closure_set(v___f_3477_, 28, v_snd_3462_);
v___x_3478_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3463_, v___x_3464_, v___f_3477_, v___x_3437_, v___x_3437_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3479_ = _args[0];
lean_object* v___x_3480_ = _args[1];
lean_object* v___x_3481_ = _args[2];
lean_object* v___x_3482_ = _args[3];
lean_object* v___x_3483_ = _args[4];
lean_object* v_is_3484_ = _args[5];
lean_object* v___x_3485_ = _args[6];
lean_object* v___x_3486_ = _args[7];
lean_object* v___x_3487_ = _args[8];
lean_object* v___x_3488_ = _args[9];
lean_object* v_params_3489_ = _args[10];
lean_object* v___x_3490_ = _args[11];
lean_object* v___x_3491_ = _args[12];
lean_object* v_heq_3492_ = _args[13];
lean_object* v_val_3493_ = _args[14];
lean_object* v_tail_3494_ = _args[15];
lean_object* v_alts_3495_ = _args[16];
lean_object* v_sz_3496_ = _args[17];
lean_object* v___x_3497_ = _args[18];
lean_object* v___x_3498_ = _args[19];
lean_object* v___x_3499_ = _args[20];
lean_object* v_declName_3500_ = _args[21];
lean_object* v_levelParams_3501_ = _args[22];
lean_object* v_numIndices_3502_ = _args[23];
lean_object* v___x_3503_ = _args[24];
lean_object* v___x_3504_ = _args[25];
lean_object* v_numParams_3505_ = _args[26];
lean_object* v_snd_3506_ = _args[27];
lean_object* v___x_3507_ = _args[28];
lean_object* v___x_3508_ = _args[29];
lean_object* v_ism1_x27_3509_ = _args[30];
lean_object* v_x_3510_ = _args[31];
lean_object* v___y_3511_ = _args[32];
lean_object* v___y_3512_ = _args[33];
lean_object* v___y_3513_ = _args[34];
lean_object* v___y_3514_ = _args[35];
lean_object* v___y_3515_ = _args[36];
_start:
{
uint8_t v___x_15812__boxed_3516_; uint8_t v___x_15813__boxed_3517_; uint8_t v___x_15814__boxed_3518_; size_t v_sz_boxed_3519_; size_t v___x_15823__boxed_3520_; lean_object* v_res_3521_; 
v___x_15812__boxed_3516_ = lean_unbox(v___x_3481_);
v___x_15813__boxed_3517_ = lean_unbox(v___x_3482_);
v___x_15814__boxed_3518_ = lean_unbox(v___x_3483_);
v_sz_boxed_3519_ = lean_unbox_usize(v_sz_3496_);
lean_dec(v_sz_3496_);
v___x_15823__boxed_3520_ = lean_unbox_usize(v___x_3497_);
lean_dec(v___x_3497_);
v_res_3521_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3479_, v___x_3480_, v___x_15812__boxed_3516_, v___x_15813__boxed_3517_, v___x_15814__boxed_3518_, v_is_3484_, v___x_3485_, v___x_3486_, v___x_3487_, v___x_3488_, v_params_3489_, v___x_3490_, v___x_3491_, v_heq_3492_, v_val_3493_, v_tail_3494_, v_alts_3495_, v_sz_boxed_3519_, v___x_15823__boxed_3520_, v___x_3498_, v___x_3499_, v_declName_3500_, v_levelParams_3501_, v_numIndices_3502_, v___x_3503_, v___x_3504_, v_numParams_3505_, v_snd_3506_, v___x_3507_, v___x_3508_, v_ism1_x27_3509_, v_x_3510_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
lean_dec_ref(v_x_3510_);
return v_res_3521_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3522_, lean_object* v___x_3523_, lean_object* v_motive_3524_, lean_object* v___x_3525_, uint8_t v___x_3526_, uint8_t v___x_3527_, uint8_t v___x_3528_, lean_object* v_is_3529_, lean_object* v___x_3530_, lean_object* v___x_3531_, lean_object* v___x_3532_, lean_object* v___x_3533_, lean_object* v_params_3534_, lean_object* v___x_3535_, lean_object* v___x_3536_, lean_object* v_heq_3537_, lean_object* v_val_3538_, lean_object* v_tail_3539_, size_t v_sz_3540_, size_t v___x_3541_, lean_object* v___x_3542_, lean_object* v___x_3543_, lean_object* v_declName_3544_, lean_object* v_levelParams_3545_, lean_object* v___x_3546_, lean_object* v___x_3547_, lean_object* v_numParams_3548_, lean_object* v_snd_3549_, lean_object* v___x_3550_, lean_object* v_alts_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___f_3564_; lean_object* v___x_3565_; 
v___x_3557_ = lean_nat_add(v_numIndices_3522_, v___x_3523_);
v___x_3558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
v___x_3559_ = lean_box(v___x_3526_);
v___x_3560_ = lean_box(v___x_3527_);
v___x_3561_ = lean_box(v___x_3528_);
v___x_3562_ = lean_box_usize(v_sz_3540_);
v___x_3563_ = lean_box_usize(v___x_3541_);
lean_inc_ref(v___x_3558_);
lean_inc_ref(v___x_3550_);
v___f_3564_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3564_, 0, v_motive_3524_);
lean_closure_set(v___f_3564_, 1, v___x_3525_);
lean_closure_set(v___f_3564_, 2, v___x_3559_);
lean_closure_set(v___f_3564_, 3, v___x_3560_);
lean_closure_set(v___f_3564_, 4, v___x_3561_);
lean_closure_set(v___f_3564_, 5, v_is_3529_);
lean_closure_set(v___f_3564_, 6, v___x_3530_);
lean_closure_set(v___f_3564_, 7, v___x_3531_);
lean_closure_set(v___f_3564_, 8, v___x_3532_);
lean_closure_set(v___f_3564_, 9, v___x_3533_);
lean_closure_set(v___f_3564_, 10, v_params_3534_);
lean_closure_set(v___f_3564_, 11, v___x_3535_);
lean_closure_set(v___f_3564_, 12, v___x_3536_);
lean_closure_set(v___f_3564_, 13, v_heq_3537_);
lean_closure_set(v___f_3564_, 14, v_val_3538_);
lean_closure_set(v___f_3564_, 15, v_tail_3539_);
lean_closure_set(v___f_3564_, 16, v_alts_3551_);
lean_closure_set(v___f_3564_, 17, v___x_3562_);
lean_closure_set(v___f_3564_, 18, v___x_3563_);
lean_closure_set(v___f_3564_, 19, v___x_3542_);
lean_closure_set(v___f_3564_, 20, v___x_3543_);
lean_closure_set(v___f_3564_, 21, v_declName_3544_);
lean_closure_set(v___f_3564_, 22, v_levelParams_3545_);
lean_closure_set(v___f_3564_, 23, v_numIndices_3522_);
lean_closure_set(v___f_3564_, 24, v___x_3546_);
lean_closure_set(v___f_3564_, 25, v___x_3547_);
lean_closure_set(v___f_3564_, 26, v_numParams_3548_);
lean_closure_set(v___f_3564_, 27, v_snd_3549_);
lean_closure_set(v___f_3564_, 28, v___x_3550_);
lean_closure_set(v___f_3564_, 29, v___x_3558_);
v___x_3565_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3550_, v___x_3558_, v___f_3564_, v___x_3526_, v___x_3526_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3566_ = _args[0];
lean_object* v___x_3567_ = _args[1];
lean_object* v_motive_3568_ = _args[2];
lean_object* v___x_3569_ = _args[3];
lean_object* v___x_3570_ = _args[4];
lean_object* v___x_3571_ = _args[5];
lean_object* v___x_3572_ = _args[6];
lean_object* v_is_3573_ = _args[7];
lean_object* v___x_3574_ = _args[8];
lean_object* v___x_3575_ = _args[9];
lean_object* v___x_3576_ = _args[10];
lean_object* v___x_3577_ = _args[11];
lean_object* v_params_3578_ = _args[12];
lean_object* v___x_3579_ = _args[13];
lean_object* v___x_3580_ = _args[14];
lean_object* v_heq_3581_ = _args[15];
lean_object* v_val_3582_ = _args[16];
lean_object* v_tail_3583_ = _args[17];
lean_object* v_sz_3584_ = _args[18];
lean_object* v___x_3585_ = _args[19];
lean_object* v___x_3586_ = _args[20];
lean_object* v___x_3587_ = _args[21];
lean_object* v_declName_3588_ = _args[22];
lean_object* v_levelParams_3589_ = _args[23];
lean_object* v___x_3590_ = _args[24];
lean_object* v___x_3591_ = _args[25];
lean_object* v_numParams_3592_ = _args[26];
lean_object* v_snd_3593_ = _args[27];
lean_object* v___x_3594_ = _args[28];
lean_object* v_alts_3595_ = _args[29];
lean_object* v___y_3596_ = _args[30];
lean_object* v___y_3597_ = _args[31];
lean_object* v___y_3598_ = _args[32];
lean_object* v___y_3599_ = _args[33];
lean_object* v___y_3600_ = _args[34];
_start:
{
uint8_t v___x_15905__boxed_3601_; uint8_t v___x_15906__boxed_3602_; uint8_t v___x_15907__boxed_3603_; size_t v_sz_boxed_3604_; size_t v___x_15916__boxed_3605_; lean_object* v_res_3606_; 
v___x_15905__boxed_3601_ = lean_unbox(v___x_3570_);
v___x_15906__boxed_3602_ = lean_unbox(v___x_3571_);
v___x_15907__boxed_3603_ = lean_unbox(v___x_3572_);
v_sz_boxed_3604_ = lean_unbox_usize(v_sz_3584_);
lean_dec(v_sz_3584_);
v___x_15916__boxed_3605_ = lean_unbox_usize(v___x_3585_);
lean_dec(v___x_3585_);
v_res_3606_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3566_, v___x_3567_, v_motive_3568_, v___x_3569_, v___x_15905__boxed_3601_, v___x_15906__boxed_3602_, v___x_15907__boxed_3603_, v_is_3573_, v___x_3574_, v___x_3575_, v___x_3576_, v___x_3577_, v_params_3578_, v___x_3579_, v___x_3580_, v_heq_3581_, v_val_3582_, v_tail_3583_, v_sz_boxed_3604_, v___x_15916__boxed_3605_, v___x_3586_, v___x_3587_, v_declName_3588_, v_levelParams_3589_, v___x_3590_, v___x_3591_, v_numParams_3592_, v_snd_3593_, v___x_3594_, v_alts_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v___y_3597_);
lean_dec_ref(v___y_3596_);
lean_dec(v___x_3567_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3607_, lean_object* v_declInfos_3608_, lean_object* v_k_3609_, lean_object* v_kind_3610_, lean_object* v_x_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
uint8_t v_kind_boxed_3617_; lean_object* v_res_3618_; 
v_kind_boxed_3617_ = lean_unbox(v_kind_3610_);
v_res_3618_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3607_, v_declInfos_3608_, v_k_3609_, v_kind_boxed_3617_, v_x_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3619_, lean_object* v_k_3620_, uint8_t v_kind_3621_, lean_object* v_acc_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v___x_3628_; lean_object* v_toApplicative_3629_; lean_object* v_toFunctor_3630_; lean_object* v_toSeq_3631_; lean_object* v_toSeqLeft_3632_; lean_object* v_toSeqRight_3633_; lean_object* v___f_3634_; lean_object* v___f_3635_; lean_object* v___f_3636_; lean_object* v___f_3637_; lean_object* v___x_3638_; lean_object* v___f_3639_; lean_object* v___f_3640_; lean_object* v___f_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v_toApplicative_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3703_; 
v___x_3628_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3629_ = lean_ctor_get(v___x_3628_, 0);
v_toFunctor_3630_ = lean_ctor_get(v_toApplicative_3629_, 0);
v_toSeq_3631_ = lean_ctor_get(v_toApplicative_3629_, 2);
v_toSeqLeft_3632_ = lean_ctor_get(v_toApplicative_3629_, 3);
v_toSeqRight_3633_ = lean_ctor_get(v_toApplicative_3629_, 4);
v___f_3634_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3635_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3630_, 2);
v___f_3636_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3636_, 0, v_toFunctor_3630_);
v___f_3637_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3637_, 0, v_toFunctor_3630_);
v___x_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___f_3636_);
lean_ctor_set(v___x_3638_, 1, v___f_3637_);
lean_inc(v_toSeqRight_3633_);
v___f_3639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3639_, 0, v_toSeqRight_3633_);
lean_inc(v_toSeqLeft_3632_);
v___f_3640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3640_, 0, v_toSeqLeft_3632_);
lean_inc(v_toSeq_3631_);
v___f_3641_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3641_, 0, v_toSeq_3631_);
v___x_3642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3638_);
lean_ctor_set(v___x_3642_, 1, v___f_3634_);
lean_ctor_set(v___x_3642_, 2, v___f_3641_);
lean_ctor_set(v___x_3642_, 3, v___f_3640_);
lean_ctor_set(v___x_3642_, 4, v___f_3639_);
v___x_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
lean_ctor_set(v___x_3643_, 1, v___f_3635_);
v___x_3644_ = l_StateRefT_x27_instMonad___redArg(v___x_3643_);
v_toApplicative_3645_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3703_ == 0)
{
lean_object* v_unused_3704_; 
v_unused_3704_ = lean_ctor_get(v___x_3644_, 1);
lean_dec(v_unused_3704_);
v___x_3647_ = v___x_3644_;
v_isShared_3648_ = v_isSharedCheck_3703_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_toApplicative_3645_);
lean_dec(v___x_3644_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3703_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v_toFunctor_3649_; lean_object* v_toSeq_3650_; lean_object* v_toSeqLeft_3651_; lean_object* v_toSeqRight_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3701_; 
v_toFunctor_3649_ = lean_ctor_get(v_toApplicative_3645_, 0);
v_toSeq_3650_ = lean_ctor_get(v_toApplicative_3645_, 2);
v_toSeqLeft_3651_ = lean_ctor_get(v_toApplicative_3645_, 3);
v_toSeqRight_3652_ = lean_ctor_get(v_toApplicative_3645_, 4);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_toApplicative_3645_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v_toApplicative_3645_, 1);
lean_dec(v_unused_3702_);
v___x_3654_ = v_toApplicative_3645_;
v_isShared_3655_ = v_isSharedCheck_3701_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_toSeqRight_3652_);
lean_inc(v_toSeqLeft_3651_);
lean_inc(v_toSeq_3650_);
lean_inc(v_toFunctor_3649_);
lean_dec(v_toApplicative_3645_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3701_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___f_3656_; lean_object* v___f_3657_; lean_object* v___f_3658_; lean_object* v___f_3659_; lean_object* v___x_3660_; lean_object* v___f_3661_; lean_object* v___f_3662_; lean_object* v___f_3663_; lean_object* v___x_3665_; 
v___f_3656_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3657_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3649_);
v___f_3658_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3658_, 0, v_toFunctor_3649_);
v___f_3659_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3659_, 0, v_toFunctor_3649_);
v___x_3660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___f_3658_);
lean_ctor_set(v___x_3660_, 1, v___f_3659_);
v___f_3661_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3661_, 0, v_toSeqRight_3652_);
v___f_3662_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3662_, 0, v_toSeqLeft_3651_);
v___f_3663_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3663_, 0, v_toSeq_3650_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 4, v___f_3661_);
lean_ctor_set(v___x_3654_, 3, v___f_3662_);
lean_ctor_set(v___x_3654_, 2, v___f_3663_);
lean_ctor_set(v___x_3654_, 1, v___f_3656_);
lean_ctor_set(v___x_3654_, 0, v___x_3660_);
v___x_3665_ = v___x_3654_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___f_3656_);
lean_ctor_set(v_reuseFailAlloc_3700_, 2, v___f_3663_);
lean_ctor_set(v_reuseFailAlloc_3700_, 3, v___f_3662_);
lean_ctor_set(v_reuseFailAlloc_3700_, 4, v___f_3661_);
v___x_3665_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
lean_object* v___x_3667_; 
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 1, v___f_3657_);
lean_ctor_set(v___x_3647_, 0, v___x_3665_);
v___x_3667_ = v___x_3647_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3665_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v___f_3657_);
v___x_3667_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; uint8_t v___x_3670_; 
v___x_3668_ = lean_array_get_size(v_acc_3622_);
v___x_3669_ = lean_array_get_size(v_declInfos_3619_);
v___x_3670_ = lean_nat_dec_lt(v___x_3668_, v___x_3669_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3671_; 
lean_dec_ref(v___x_3667_);
lean_dec_ref(v_declInfos_3619_);
lean_inc(v___y_3626_);
lean_inc_ref(v___y_3625_);
lean_inc(v___y_3624_);
lean_inc_ref(v___y_3623_);
v___x_3671_ = lean_apply_6(v_k_3620_, v_acc_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, lean_box(0));
return v___x_3671_;
}
else
{
lean_object* v___x_3672_; uint8_t v___x_3673_; lean_object* v___x_3674_; lean_object* v___f_3675_; lean_object* v___f_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v_snd_3681_; lean_object* v_fst_3682_; lean_object* v_fst_3683_; lean_object* v_snd_3684_; lean_object* v___x_3685_; lean_object* v___f_3686_; lean_object* v___x_3687_; 
v___x_3672_ = lean_box(0);
v___x_3673_ = 0;
v___x_3674_ = l_Lean_instInhabitedExpr;
v___f_3675_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3675_, 0, v___x_3667_);
lean_closure_set(v___f_3675_, 1, v___x_3674_);
v___f_3676_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3676_, 0, v___f_3675_);
v___x_3677_ = lean_box(v___x_3673_);
v___x_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
lean_ctor_set(v___x_3678_, 1, v___f_3676_);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3672_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = lean_array_get(v___x_3679_, v_declInfos_3619_, v___x_3668_);
lean_dec_ref_known(v___x_3679_, 2);
v_snd_3681_ = lean_ctor_get(v___x_3680_, 1);
lean_inc(v_snd_3681_);
v_fst_3682_ = lean_ctor_get(v___x_3680_, 0);
lean_inc(v_fst_3682_);
lean_dec(v___x_3680_);
v_fst_3683_ = lean_ctor_get(v_snd_3681_, 0);
lean_inc(v_fst_3683_);
v_snd_3684_ = lean_ctor_get(v_snd_3681_, 1);
lean_inc(v_snd_3684_);
lean_dec(v_snd_3681_);
v___x_3685_ = lean_box(v_kind_3621_);
lean_inc_ref(v_acc_3622_);
v___f_3686_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3686_, 0, v_acc_3622_);
lean_closure_set(v___f_3686_, 1, v_declInfos_3619_);
lean_closure_set(v___f_3686_, 2, v_k_3620_);
lean_closure_set(v___f_3686_, 3, v___x_3685_);
lean_inc(v___y_3626_);
lean_inc_ref(v___y_3625_);
lean_inc(v___y_3624_);
lean_inc_ref(v___y_3623_);
v___x_3687_ = lean_apply_6(v_snd_3684_, v_acc_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, lean_box(0));
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v_a_3688_; uint8_t v___x_3689_; lean_object* v___x_3690_; 
v_a_3688_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_a_3688_);
lean_dec_ref_known(v___x_3687_, 1);
v___x_3689_ = lean_unbox(v_fst_3683_);
lean_dec(v_fst_3683_);
v___x_3690_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3682_, v___x_3689_, v_a_3688_, v___f_3686_, v_kind_3621_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
return v___x_3690_;
}
else
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v___f_3686_);
lean_dec(v_fst_3683_);
lean_dec(v_fst_3682_);
v_a_3691_ = lean_ctor_get(v___x_3687_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3687_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3687_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3687_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3705_, lean_object* v_declInfos_3706_, lean_object* v_k_3707_, uint8_t v_kind_3708_, lean_object* v_x_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = lean_array_push(v_acc_3705_, v_x_3709_);
v___x_3716_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3706_, v_k_3707_, v_kind_3708_, v___x_3715_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3717_, lean_object* v_k_3718_, lean_object* v_kind_3719_, lean_object* v_acc_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
uint8_t v_kind_boxed_3726_; lean_object* v_res_3727_; 
v_kind_boxed_3726_ = lean_unbox(v_kind_3719_);
v_res_3727_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3717_, v_k_3718_, v_kind_boxed_3726_, v_acc_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
return v_res_3727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3728_, lean_object* v_k_3729_, uint8_t v_kind_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3737_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3728_, v_k_3729_, v_kind_3730_, v___x_3736_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3738_, lean_object* v_k_3739_, lean_object* v_kind_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
uint8_t v_kind_boxed_3746_; lean_object* v_res_3747_; 
v_kind_boxed_3746_ = lean_unbox(v_kind_3740_);
v_res_3747_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3738_, v_k_3739_, v_kind_boxed_3746_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3748_, lean_object* v_k_3749_, uint8_t v_kind_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
size_t v_sz_3756_; size_t v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v_sz_3756_ = lean_array_size(v_declInfos_3748_);
v___x_3757_ = ((size_t)0ULL);
v___x_3758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3756_, v___x_3757_, v_declInfos_3748_);
v___x_3759_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3758_, v_k_3749_, v_kind_3750_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3760_, lean_object* v_k_3761_, lean_object* v_kind_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
uint8_t v_kind_boxed_3768_; lean_object* v_res_3769_; 
v_kind_boxed_3768_ = lean_unbox(v_kind_3762_);
v_res_3769_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3760_, v_k_3761_, v_kind_boxed_3768_, v___y_3763_, v___y_3764_, v___y_3765_, v___y_3766_);
lean_dec(v___y_3766_);
lean_dec_ref(v___y_3765_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3770_, lean_object* v_k_3771_, uint8_t v_kind_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
size_t v_sz_3778_; size_t v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
v_sz_3778_ = lean_array_size(v_declInfos_3770_);
v___x_3779_ = ((size_t)0ULL);
v___x_3780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3778_, v___x_3779_, v_declInfos_3770_);
v___x_3781_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3780_, v_k_3771_, v_kind_3772_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3782_, lean_object* v_k_3783_, lean_object* v_kind_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
uint8_t v_kind_boxed_3790_; lean_object* v_res_3791_; 
v_kind_boxed_3790_ = lean_unbox(v_kind_3784_);
v_res_3791_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3782_, v_k_3783_, v_kind_boxed_3790_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
return v_res_3791_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = lean_box(0);
v___x_3795_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3796_ = l_Lean_mkConst(v___x_3795_, v___x_3794_);
return v___x_3796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3797_, lean_object* v_v_3798_, lean_object* v___x_3799_, lean_object* v___x_3800_, lean_object* v___x_3801_, lean_object* v_motive_3802_, uint8_t v___x_3803_, uint8_t v___x_3804_, uint8_t v___x_3805_, lean_object* v_zs12_3806_, lean_object* v_is_3807_, lean_object* v_fields1_3808_, lean_object* v_fields2_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v_e_3825_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
lean_inc_ref(v___x_3801_);
v___x_3835_ = l_Lean_mkAppN(v___x_3801_, v_fields1_3808_);
v___x_3836_ = l_Lean_mkAppN(v___x_3801_, v_fields2_3809_);
lean_inc(v___x_3799_);
v___x_3837_ = l_Lean_mkNatLit(v___x_3799_);
v___x_3838_ = l_Lean_Meta_mkEqRefl(v___x_3837_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v___x_3838_, 1);
v___x_3840_ = lean_unsigned_to_nat(3u);
v___x_3841_ = lean_mk_empty_array_with_capacity(v___x_3840_);
v___x_3842_ = lean_array_push(v___x_3841_, v___x_3835_);
v___x_3843_ = lean_array_push(v___x_3842_, v___x_3836_);
v___x_3844_ = lean_array_push(v___x_3843_, v_a_3839_);
v___x_3845_ = l_Array_append___redArg(v_is_3807_, v___x_3844_);
lean_dec_ref(v___x_3844_);
v___x_3846_ = l_Lean_mkAppN(v_motive_3802_, v___x_3845_);
lean_dec_ref(v___x_3845_);
v___x_3847_ = l_Lean_Meta_mkForallFVars(v_zs12_3806_, v___x_3846_, v___x_3803_, v___x_3804_, v___x_3804_, v___x_3805_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v___x_3849_ = lean_array_get_size(v_zs12_3806_);
v___x_3850_ = lean_nat_dec_eq(v___x_3849_, v___x_3797_);
if (v___x_3850_ == 0)
{
v_e_3825_ = v_a_3848_;
goto v___jp_3824_;
}
else
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3852_ = l_Lean_mkArrow(v___x_3851_, v_a_3848_, v___y_3812_, v___y_3813_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v_e_3825_ = v_a_3853_;
goto v___jp_3824_;
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v___x_3799_);
lean_dec(v_v_3798_);
lean_dec(v___x_3797_);
v_a_3854_ = lean_ctor_get(v___x_3852_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3852_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3852_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3852_);
v___x_3856_ = lean_box(0);
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
v_resetjp_3855_:
{
lean_object* v___x_3859_; 
if (v_isShared_3857_ == 0)
{
v___x_3859_ = v___x_3856_;
goto v_reusejp_3858_;
}
else
{
lean_object* v_reuseFailAlloc_3860_; 
v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
v___x_3859_ = v_reuseFailAlloc_3860_;
goto v_reusejp_3858_;
}
v_reusejp_3858_:
{
return v___x_3859_;
}
}
}
}
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec(v___x_3799_);
lean_dec(v_v_3798_);
lean_dec(v___x_3797_);
v_a_3862_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3847_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3847_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec_ref(v___x_3836_);
lean_dec_ref(v___x_3835_);
lean_dec_ref(v_is_3807_);
lean_dec_ref(v_motive_3802_);
lean_dec(v___x_3799_);
lean_dec(v_v_3798_);
lean_dec(v___x_3797_);
v_a_3870_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3838_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3838_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
v___jp_3815_:
{
lean_object* v___x_3818_; uint8_t v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3818_ = lean_array_get_size(v_zs12_3806_);
v___x_3819_ = lean_nat_dec_eq(v___x_3818_, v___x_3797_);
v___x_3820_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3820_, 0, v___x_3818_);
lean_ctor_set(v___x_3820_, 1, v___x_3797_);
lean_ctor_set_uint8(v___x_3820_, sizeof(void*)*2, v___x_3819_);
v___x_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___y_3817_);
lean_ctor_set(v___x_3821_, 1, v___y_3816_);
v___x_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
lean_ctor_set(v___x_3822_, 1, v___x_3820_);
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
return v___x_3823_;
}
v___jp_3824_:
{
if (lean_obj_tag(v_v_3798_) == 1)
{
lean_object* v_str_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
lean_dec(v___x_3799_);
v_str_3826_ = lean_ctor_get(v_v_3798_, 1);
lean_inc_ref(v_str_3826_);
lean_dec_ref_known(v_v_3798_, 2);
v___x_3827_ = lean_box(0);
v___x_3828_ = l_Lean_Name_str___override(v___x_3827_, v_str_3826_);
v___y_3816_ = v_e_3825_;
v___y_3817_ = v___x_3828_;
goto v___jp_3815_;
}
else
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_dec(v_v_3798_);
v___x_3829_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3830_ = lean_nat_add(v___x_3799_, v___x_3800_);
lean_dec(v___x_3799_);
v___x_3831_ = l_Nat_reprFast(v___x_3830_);
v___x_3832_ = lean_string_append(v___x_3829_, v___x_3831_);
lean_dec_ref(v___x_3831_);
v___x_3833_ = lean_box(0);
v___x_3834_ = l_Lean_Name_str___override(v___x_3833_, v___x_3832_);
v___y_3816_ = v_e_3825_;
v___y_3817_ = v___x_3834_;
goto v___jp_3815_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3878_ = _args[0];
lean_object* v_v_3879_ = _args[1];
lean_object* v___x_3880_ = _args[2];
lean_object* v___x_3881_ = _args[3];
lean_object* v___x_3882_ = _args[4];
lean_object* v_motive_3883_ = _args[5];
lean_object* v___x_3884_ = _args[6];
lean_object* v___x_3885_ = _args[7];
lean_object* v___x_3886_ = _args[8];
lean_object* v_zs12_3887_ = _args[9];
lean_object* v_is_3888_ = _args[10];
lean_object* v_fields1_3889_ = _args[11];
lean_object* v_fields2_3890_ = _args[12];
lean_object* v___y_3891_ = _args[13];
lean_object* v___y_3892_ = _args[14];
lean_object* v___y_3893_ = _args[15];
lean_object* v___y_3894_ = _args[16];
lean_object* v___y_3895_ = _args[17];
_start:
{
uint8_t v___x_16252__boxed_3896_; uint8_t v___x_16253__boxed_3897_; uint8_t v___x_16254__boxed_3898_; lean_object* v_res_3899_; 
v___x_16252__boxed_3896_ = lean_unbox(v___x_3884_);
v___x_16253__boxed_3897_ = lean_unbox(v___x_3885_);
v___x_16254__boxed_3898_ = lean_unbox(v___x_3886_);
v_res_3899_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3878_, v_v_3879_, v___x_3880_, v___x_3881_, v___x_3882_, v_motive_3883_, v___x_16252__boxed_3896_, v___x_16253__boxed_3897_, v___x_16254__boxed_3898_, v_zs12_3887_, v_is_3888_, v_fields1_3889_, v_fields2_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec_ref(v_fields2_3890_);
lean_dec_ref(v_fields1_3889_);
lean_dec_ref(v_zs12_3887_);
lean_dec(v___x_3881_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3900_, lean_object* v_params_3901_, lean_object* v_motive_3902_, size_t v_sz_3903_, size_t v_i_3904_, lean_object* v_bs_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
uint8_t v___x_3911_; 
v___x_3911_ = lean_usize_dec_lt(v_i_3904_, v_sz_3903_);
if (v___x_3911_ == 0)
{
lean_object* v___x_3912_; 
lean_dec_ref(v_motive_3902_);
lean_dec(v_tail_3900_);
v___x_3912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3912_, 0, v_bs_3905_);
return v___x_3912_;
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3914_; uint8_t v___x_3915_; uint8_t v___x_3916_; lean_object* v_v_3917_; lean_object* v_bs_x27_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___f_3925_; lean_object* v___x_3926_; 
v___x_3913_ = lean_unsigned_to_nat(0u);
v___x_3914_ = lean_unsigned_to_nat(1u);
v___x_3915_ = 0;
v___x_3916_ = 1;
v_v_3917_ = lean_array_uget(v_bs_3905_, v_i_3904_);
v_bs_x27_3918_ = lean_array_uset(v_bs_3905_, v_i_3904_, v___x_3913_);
v___x_3919_ = lean_usize_to_nat(v_i_3904_);
lean_inc(v_tail_3900_);
lean_inc(v_v_3917_);
v___x_3920_ = l_Lean_mkConst(v_v_3917_, v_tail_3900_);
v___x_3921_ = l_Lean_mkAppN(v___x_3920_, v_params_3901_);
v___x_3922_ = lean_box(v___x_3915_);
v___x_3923_ = lean_box(v___x_3911_);
v___x_3924_ = lean_box(v___x_3916_);
lean_inc_ref(v_motive_3902_);
lean_inc_ref(v___x_3921_);
v___f_3925_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3925_, 0, v___x_3913_);
lean_closure_set(v___f_3925_, 1, v_v_3917_);
lean_closure_set(v___f_3925_, 2, v___x_3919_);
lean_closure_set(v___f_3925_, 3, v___x_3914_);
lean_closure_set(v___f_3925_, 4, v___x_3921_);
lean_closure_set(v___f_3925_, 5, v_motive_3902_);
lean_closure_set(v___f_3925_, 6, v___x_3922_);
lean_closure_set(v___f_3925_, 7, v___x_3923_);
lean_closure_set(v___f_3925_, 8, v___x_3924_);
v___x_3926_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3921_, v___f_3925_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; size_t v___x_3928_; size_t v___x_3929_; lean_object* v___x_3930_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref_known(v___x_3926_, 1);
v___x_3928_ = ((size_t)1ULL);
v___x_3929_ = lean_usize_add(v_i_3904_, v___x_3928_);
v___x_3930_ = lean_array_uset(v_bs_x27_3918_, v_i_3904_, v_a_3927_);
v_i_3904_ = v___x_3929_;
v_bs_3905_ = v___x_3930_;
goto _start;
}
else
{
lean_object* v_a_3932_; lean_object* v___x_3934_; uint8_t v_isShared_3935_; uint8_t v_isSharedCheck_3939_; 
lean_dec_ref(v_bs_x27_3918_);
lean_dec_ref(v_motive_3902_);
lean_dec(v_tail_3900_);
v_a_3932_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3939_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3939_ == 0)
{
v___x_3934_ = v___x_3926_;
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
else
{
lean_inc(v_a_3932_);
lean_dec(v___x_3926_);
v___x_3934_ = lean_box(0);
v_isShared_3935_ = v_isSharedCheck_3939_;
goto v_resetjp_3933_;
}
v_resetjp_3933_:
{
lean_object* v___x_3937_; 
if (v_isShared_3935_ == 0)
{
v___x_3937_ = v___x_3934_;
goto v_reusejp_3936_;
}
else
{
lean_object* v_reuseFailAlloc_3938_; 
v_reuseFailAlloc_3938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3938_, 0, v_a_3932_);
v___x_3937_ = v_reuseFailAlloc_3938_;
goto v_reusejp_3936_;
}
v_reusejp_3936_:
{
return v___x_3937_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3940_, lean_object* v_params_3941_, lean_object* v_motive_3942_, lean_object* v_sz_3943_, lean_object* v_i_3944_, lean_object* v_bs_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
size_t v_sz_boxed_3951_; size_t v_i_boxed_3952_; lean_object* v_res_3953_; 
v_sz_boxed_3951_ = lean_unbox_usize(v_sz_3943_);
lean_dec(v_sz_3943_);
v_i_boxed_3952_ = lean_unbox_usize(v_i_3944_);
lean_dec(v_i_3944_);
v_res_3953_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3940_, v_params_3941_, v_motive_3942_, v_sz_boxed_3951_, v_i_boxed_3952_, v_bs_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec_ref(v_params_3941_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3956_, lean_object* v_tail_3957_, lean_object* v_params_3958_, lean_object* v_numIndices_3959_, lean_object* v___x_3960_, lean_object* v___x_3961_, uint8_t v___x_3962_, uint8_t v___x_3963_, uint8_t v___x_3964_, lean_object* v_is_3965_, lean_object* v___x_3966_, lean_object* v___x_3967_, lean_object* v___x_3968_, lean_object* v___x_3969_, lean_object* v___x_3970_, lean_object* v___x_3971_, lean_object* v_heq_3972_, lean_object* v_val_3973_, lean_object* v___x_3974_, lean_object* v_declName_3975_, lean_object* v_levelParams_3976_, lean_object* v___x_3977_, lean_object* v___x_3978_, lean_object* v_numParams_3979_, lean_object* v___x_3980_, lean_object* v_motive_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v___x_3987_; size_t v_sz_3988_; size_t v___x_3989_; lean_object* v___x_3990_; 
v___x_3987_ = lean_array_mk(v_ctors_3956_);
v_sz_3988_ = lean_array_size(v___x_3987_);
v___x_3989_ = ((size_t)0ULL);
lean_inc_ref(v___x_3987_);
lean_inc_ref(v_motive_3981_);
lean_inc(v_tail_3957_);
v___x_3990_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3957_, v_params_3958_, v_motive_3981_, v_sz_3988_, v___x_3989_, v___x_3987_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
if (lean_obj_tag(v___x_3990_) == 0)
{
lean_object* v_a_3991_; lean_object* v___x_3992_; lean_object* v_fst_3993_; lean_object* v_snd_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___f_4000_; uint8_t v___x_4001_; lean_object* v___x_4002_; 
v_a_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_a_3991_);
lean_dec_ref_known(v___x_3990_, 1);
v___x_3992_ = l_Array_unzip___redArg(v_a_3991_);
lean_dec(v_a_3991_);
v_fst_3993_ = lean_ctor_get(v___x_3992_, 0);
lean_inc(v_fst_3993_);
v_snd_3994_ = lean_ctor_get(v___x_3992_, 1);
lean_inc(v_snd_3994_);
lean_dec_ref(v___x_3992_);
v___x_3995_ = lean_box(v___x_3962_);
v___x_3996_ = lean_box(v___x_3963_);
v___x_3997_ = lean_box(v___x_3964_);
v___x_3998_ = lean_box_usize(v_sz_3988_);
v___x_3999_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4000_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4000_, 0, v_numIndices_3959_);
lean_closure_set(v___f_4000_, 1, v___x_3960_);
lean_closure_set(v___f_4000_, 2, v_motive_3981_);
lean_closure_set(v___f_4000_, 3, v___x_3961_);
lean_closure_set(v___f_4000_, 4, v___x_3995_);
lean_closure_set(v___f_4000_, 5, v___x_3996_);
lean_closure_set(v___f_4000_, 6, v___x_3997_);
lean_closure_set(v___f_4000_, 7, v_is_3965_);
lean_closure_set(v___f_4000_, 8, v___x_3966_);
lean_closure_set(v___f_4000_, 9, v___x_3967_);
lean_closure_set(v___f_4000_, 10, v___x_3968_);
lean_closure_set(v___f_4000_, 11, v___x_3969_);
lean_closure_set(v___f_4000_, 12, v_params_3958_);
lean_closure_set(v___f_4000_, 13, v___x_3970_);
lean_closure_set(v___f_4000_, 14, v___x_3971_);
lean_closure_set(v___f_4000_, 15, v_heq_3972_);
lean_closure_set(v___f_4000_, 16, v_val_3973_);
lean_closure_set(v___f_4000_, 17, v_tail_3957_);
lean_closure_set(v___f_4000_, 18, v___x_3998_);
lean_closure_set(v___f_4000_, 19, v___x_3999_);
lean_closure_set(v___f_4000_, 20, v___x_3987_);
lean_closure_set(v___f_4000_, 21, v___x_3974_);
lean_closure_set(v___f_4000_, 22, v_declName_3975_);
lean_closure_set(v___f_4000_, 23, v_levelParams_3976_);
lean_closure_set(v___f_4000_, 24, v___x_3977_);
lean_closure_set(v___f_4000_, 25, v___x_3978_);
lean_closure_set(v___f_4000_, 26, v_numParams_3979_);
lean_closure_set(v___f_4000_, 27, v_snd_3994_);
lean_closure_set(v___f_4000_, 28, v___x_3980_);
v___x_4001_ = 0;
v___x_4002_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_3993_, v___f_4000_, v___x_4001_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
return v___x_4002_;
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_dec_ref(v___x_3987_);
lean_dec_ref(v_motive_3981_);
lean_dec_ref(v___x_3980_);
lean_dec(v_numParams_3979_);
lean_dec(v___x_3978_);
lean_dec(v___x_3977_);
lean_dec(v_levelParams_3976_);
lean_dec(v_declName_3975_);
lean_dec_ref(v___x_3974_);
lean_dec_ref(v_val_3973_);
lean_dec_ref(v_heq_3972_);
lean_dec_ref(v___x_3971_);
lean_dec_ref(v___x_3970_);
lean_dec(v___x_3969_);
lean_dec(v___x_3968_);
lean_dec_ref(v___x_3967_);
lean_dec_ref(v___x_3966_);
lean_dec_ref(v_is_3965_);
lean_dec_ref(v___x_3961_);
lean_dec(v___x_3960_);
lean_dec(v_numIndices_3959_);
lean_dec_ref(v_params_3958_);
lean_dec(v_tail_3957_);
v_a_4003_ = lean_ctor_get(v___x_3990_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3990_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3990_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3990_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4011_ = _args[0];
lean_object* v_tail_4012_ = _args[1];
lean_object* v_params_4013_ = _args[2];
lean_object* v_numIndices_4014_ = _args[3];
lean_object* v___x_4015_ = _args[4];
lean_object* v___x_4016_ = _args[5];
lean_object* v___x_4017_ = _args[6];
lean_object* v___x_4018_ = _args[7];
lean_object* v___x_4019_ = _args[8];
lean_object* v_is_4020_ = _args[9];
lean_object* v___x_4021_ = _args[10];
lean_object* v___x_4022_ = _args[11];
lean_object* v___x_4023_ = _args[12];
lean_object* v___x_4024_ = _args[13];
lean_object* v___x_4025_ = _args[14];
lean_object* v___x_4026_ = _args[15];
lean_object* v_heq_4027_ = _args[16];
lean_object* v_val_4028_ = _args[17];
lean_object* v___x_4029_ = _args[18];
lean_object* v_declName_4030_ = _args[19];
lean_object* v_levelParams_4031_ = _args[20];
lean_object* v___x_4032_ = _args[21];
lean_object* v___x_4033_ = _args[22];
lean_object* v_numParams_4034_ = _args[23];
lean_object* v___x_4035_ = _args[24];
lean_object* v_motive_4036_ = _args[25];
lean_object* v___y_4037_ = _args[26];
lean_object* v___y_4038_ = _args[27];
lean_object* v___y_4039_ = _args[28];
lean_object* v___y_4040_ = _args[29];
lean_object* v___y_4041_ = _args[30];
_start:
{
uint8_t v___x_16489__boxed_4042_; uint8_t v___x_16490__boxed_4043_; uint8_t v___x_16491__boxed_4044_; lean_object* v_res_4045_; 
v___x_16489__boxed_4042_ = lean_unbox(v___x_4017_);
v___x_16490__boxed_4043_ = lean_unbox(v___x_4018_);
v___x_16491__boxed_4044_ = lean_unbox(v___x_4019_);
v_res_4045_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4011_, v_tail_4012_, v_params_4013_, v_numIndices_4014_, v___x_4015_, v___x_4016_, v___x_16489__boxed_4042_, v___x_16490__boxed_4043_, v___x_16491__boxed_4044_, v_is_4020_, v___x_4021_, v___x_4022_, v___x_4023_, v___x_4024_, v___x_4025_, v___x_4026_, v_heq_4027_, v_val_4028_, v___x_4029_, v_declName_4030_, v_levelParams_4031_, v___x_4032_, v___x_4033_, v_numParams_4034_, v___x_4035_, v_motive_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4046_, lean_object* v___x_4047_, lean_object* v_is_4048_, lean_object* v_head_4049_, lean_object* v_ctors_4050_, lean_object* v_tail_4051_, lean_object* v_params_4052_, lean_object* v_numIndices_4053_, lean_object* v___x_4054_, lean_object* v___x_4055_, lean_object* v___x_4056_, lean_object* v___x_4057_, lean_object* v___x_4058_, lean_object* v_val_4059_, lean_object* v___x_4060_, lean_object* v_declName_4061_, lean_object* v_levelParams_4062_, lean_object* v___x_4063_, lean_object* v_numParams_4064_, lean_object* v___x_4065_, lean_object* v_heq_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; uint8_t v___x_4080_; uint8_t v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___f_4085_; lean_object* v___x_4086_; 
v___x_4072_ = lean_unsigned_to_nat(3u);
v___x_4073_ = lean_mk_empty_array_with_capacity(v___x_4072_);
lean_inc_ref(v___x_4046_);
v___x_4074_ = lean_array_push(v___x_4073_, v___x_4046_);
lean_inc_ref(v___x_4047_);
v___x_4075_ = lean_array_push(v___x_4074_, v___x_4047_);
lean_inc_ref(v_heq_4066_);
v___x_4076_ = lean_array_push(v___x_4075_, v_heq_4066_);
lean_inc_ref(v_is_4048_);
v___x_4077_ = l_Array_append___redArg(v_is_4048_, v___x_4076_);
lean_dec_ref(v___x_4076_);
v___x_4078_ = l_Lean_mkSort(v_head_4049_);
v___x_4079_ = 0;
v___x_4080_ = 1;
v___x_4081_ = 1;
v___x_4082_ = lean_box(v___x_4079_);
v___x_4083_ = lean_box(v___x_4080_);
v___x_4084_ = lean_box(v___x_4081_);
lean_inc_ref(v___x_4077_);
v___f_4085_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4085_, 0, v_ctors_4050_);
lean_closure_set(v___f_4085_, 1, v_tail_4051_);
lean_closure_set(v___f_4085_, 2, v_params_4052_);
lean_closure_set(v___f_4085_, 3, v_numIndices_4053_);
lean_closure_set(v___f_4085_, 4, v___x_4054_);
lean_closure_set(v___f_4085_, 5, v___x_4077_);
lean_closure_set(v___f_4085_, 6, v___x_4082_);
lean_closure_set(v___f_4085_, 7, v___x_4083_);
lean_closure_set(v___f_4085_, 8, v___x_4084_);
lean_closure_set(v___f_4085_, 9, v_is_4048_);
lean_closure_set(v___f_4085_, 10, v___x_4047_);
lean_closure_set(v___f_4085_, 11, v___x_4046_);
lean_closure_set(v___f_4085_, 12, v___x_4055_);
lean_closure_set(v___f_4085_, 13, v___x_4056_);
lean_closure_set(v___f_4085_, 14, v___x_4057_);
lean_closure_set(v___f_4085_, 15, v___x_4058_);
lean_closure_set(v___f_4085_, 16, v_heq_4066_);
lean_closure_set(v___f_4085_, 17, v_val_4059_);
lean_closure_set(v___f_4085_, 18, v___x_4060_);
lean_closure_set(v___f_4085_, 19, v_declName_4061_);
lean_closure_set(v___f_4085_, 20, v_levelParams_4062_);
lean_closure_set(v___f_4085_, 21, v___x_4072_);
lean_closure_set(v___f_4085_, 22, v___x_4063_);
lean_closure_set(v___f_4085_, 23, v_numParams_4064_);
lean_closure_set(v___f_4085_, 24, v___x_4065_);
v___x_4086_ = l_Lean_Meta_mkForallFVars(v___x_4077_, v___x_4078_, v___x_4079_, v___x_4080_, v___x_4080_, v___x_4081_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
lean_dec_ref(v___x_4077_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4088_; uint8_t v___x_4089_; lean_object* v___x_4090_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v___x_4086_, 1);
v___x_4088_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4089_ = 0;
v___x_4090_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4088_, v___x_4081_, v_a_4087_, v___f_4085_, v___x_4089_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
return v___x_4090_;
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
lean_dec_ref(v___f_4085_);
v_a_4091_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4086_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4086_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4099_ = _args[0];
lean_object* v___x_4100_ = _args[1];
lean_object* v_is_4101_ = _args[2];
lean_object* v_head_4102_ = _args[3];
lean_object* v_ctors_4103_ = _args[4];
lean_object* v_tail_4104_ = _args[5];
lean_object* v_params_4105_ = _args[6];
lean_object* v_numIndices_4106_ = _args[7];
lean_object* v___x_4107_ = _args[8];
lean_object* v___x_4108_ = _args[9];
lean_object* v___x_4109_ = _args[10];
lean_object* v___x_4110_ = _args[11];
lean_object* v___x_4111_ = _args[12];
lean_object* v_val_4112_ = _args[13];
lean_object* v___x_4113_ = _args[14];
lean_object* v_declName_4114_ = _args[15];
lean_object* v_levelParams_4115_ = _args[16];
lean_object* v___x_4116_ = _args[17];
lean_object* v_numParams_4117_ = _args[18];
lean_object* v___x_4118_ = _args[19];
lean_object* v_heq_4119_ = _args[20];
lean_object* v___y_4120_ = _args[21];
lean_object* v___y_4121_ = _args[22];
lean_object* v___y_4122_ = _args[23];
lean_object* v___y_4123_ = _args[24];
lean_object* v___y_4124_ = _args[25];
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4099_, v___x_4100_, v_is_4101_, v_head_4102_, v_ctors_4103_, v_tail_4104_, v_params_4105_, v_numIndices_4106_, v___x_4107_, v___x_4108_, v___x_4109_, v___x_4110_, v___x_4111_, v_val_4112_, v___x_4113_, v_declName_4114_, v_levelParams_4115_, v___x_4116_, v_numParams_4117_, v___x_4118_, v_heq_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4126_, lean_object* v_x1_4127_, lean_object* v_indName_4128_, lean_object* v_tail_4129_, lean_object* v_params_4130_, lean_object* v_is_4131_, lean_object* v___x_4132_, lean_object* v_head_4133_, lean_object* v_ctors_4134_, lean_object* v_numIndices_4135_, lean_object* v___x_4136_, lean_object* v___x_4137_, lean_object* v_val_4138_, lean_object* v_declName_4139_, lean_object* v_levelParams_4140_, lean_object* v_numParams_4141_, lean_object* v___x_4142_, lean_object* v_x2_4143_, lean_object* v_x_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___f_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4150_ = lean_unsigned_to_nat(0u);
v___x_4151_ = lean_array_get_borrowed(v___x_4126_, v_x1_4127_, v___x_4150_);
v___x_4152_ = lean_array_get_borrowed(v___x_4126_, v_x2_4143_, v___x_4150_);
v___x_4153_ = l_Lean_mkCtorIdxName(v_indName_4128_);
lean_inc(v_tail_4129_);
v___x_4154_ = l_Lean_mkConst(v___x_4153_, v_tail_4129_);
lean_inc_ref(v_params_4130_);
v___x_4155_ = l_Array_append___redArg(v_params_4130_, v_is_4131_);
v___x_4156_ = lean_mk_empty_array_with_capacity(v___x_4132_);
lean_inc_n(v___x_4151_, 2);
lean_inc_ref_n(v___x_4156_, 2);
v___x_4157_ = lean_array_push(v___x_4156_, v___x_4151_);
lean_inc_ref(v___x_4155_);
v___x_4158_ = l_Array_append___redArg(v___x_4155_, v___x_4157_);
lean_inc_ref(v___x_4154_);
v___x_4159_ = l_Lean_mkAppN(v___x_4154_, v___x_4158_);
lean_dec_ref(v___x_4158_);
lean_inc_n(v___x_4152_, 2);
v___x_4160_ = lean_array_push(v___x_4156_, v___x_4152_);
lean_inc_ref(v___x_4160_);
v___f_4161_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4161_, 0, v___x_4151_);
lean_closure_set(v___f_4161_, 1, v___x_4152_);
lean_closure_set(v___f_4161_, 2, v_is_4131_);
lean_closure_set(v___f_4161_, 3, v_head_4133_);
lean_closure_set(v___f_4161_, 4, v_ctors_4134_);
lean_closure_set(v___f_4161_, 5, v_tail_4129_);
lean_closure_set(v___f_4161_, 6, v_params_4130_);
lean_closure_set(v___f_4161_, 7, v_numIndices_4135_);
lean_closure_set(v___f_4161_, 8, v___x_4132_);
lean_closure_set(v___f_4161_, 9, v___x_4136_);
lean_closure_set(v___f_4161_, 10, v___x_4137_);
lean_closure_set(v___f_4161_, 11, v___x_4157_);
lean_closure_set(v___f_4161_, 12, v___x_4160_);
lean_closure_set(v___f_4161_, 13, v_val_4138_);
lean_closure_set(v___f_4161_, 14, v___x_4156_);
lean_closure_set(v___f_4161_, 15, v_declName_4139_);
lean_closure_set(v___f_4161_, 16, v_levelParams_4140_);
lean_closure_set(v___f_4161_, 17, v___x_4150_);
lean_closure_set(v___f_4161_, 18, v_numParams_4141_);
lean_closure_set(v___f_4161_, 19, v___x_4142_);
v___x_4162_ = l_Array_append___redArg(v___x_4155_, v___x_4160_);
lean_dec_ref(v___x_4160_);
v___x_4163_ = l_Lean_mkAppN(v___x_4154_, v___x_4162_);
lean_dec_ref(v___x_4162_);
v___x_4164_ = l_Lean_Meta_mkEq(v___x_4159_, v___x_4163_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v___x_4166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4167_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4166_, v_a_4165_, v___f_4161_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_);
return v___x_4167_;
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec_ref(v___f_4161_);
v_a_4168_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4164_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4164_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4176_ = _args[0];
lean_object* v_x1_4177_ = _args[1];
lean_object* v_indName_4178_ = _args[2];
lean_object* v_tail_4179_ = _args[3];
lean_object* v_params_4180_ = _args[4];
lean_object* v_is_4181_ = _args[5];
lean_object* v___x_4182_ = _args[6];
lean_object* v_head_4183_ = _args[7];
lean_object* v_ctors_4184_ = _args[8];
lean_object* v_numIndices_4185_ = _args[9];
lean_object* v___x_4186_ = _args[10];
lean_object* v___x_4187_ = _args[11];
lean_object* v_val_4188_ = _args[12];
lean_object* v_declName_4189_ = _args[13];
lean_object* v_levelParams_4190_ = _args[14];
lean_object* v_numParams_4191_ = _args[15];
lean_object* v___x_4192_ = _args[16];
lean_object* v_x2_4193_ = _args[17];
lean_object* v_x_4194_ = _args[18];
lean_object* v___y_4195_ = _args[19];
lean_object* v___y_4196_ = _args[20];
lean_object* v___y_4197_ = _args[21];
lean_object* v___y_4198_ = _args[22];
lean_object* v___y_4199_ = _args[23];
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4176_, v_x1_4177_, v_indName_4178_, v_tail_4179_, v_params_4180_, v_is_4181_, v___x_4182_, v_head_4183_, v_ctors_4184_, v_numIndices_4185_, v___x_4186_, v___x_4187_, v_val_4188_, v_declName_4189_, v_levelParams_4190_, v_numParams_4191_, v___x_4192_, v_x2_4193_, v_x_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec_ref(v_x_4194_);
lean_dec_ref(v_x2_4193_);
lean_dec_ref(v_x1_4177_);
lean_dec_ref(v___x_4176_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4201_, lean_object* v_indName_4202_, lean_object* v_tail_4203_, lean_object* v_params_4204_, lean_object* v_is_4205_, lean_object* v___x_4206_, lean_object* v_head_4207_, lean_object* v_ctors_4208_, lean_object* v_numIndices_4209_, lean_object* v___x_4210_, lean_object* v___x_4211_, lean_object* v_val_4212_, lean_object* v_declName_4213_, lean_object* v_levelParams_4214_, lean_object* v_numParams_4215_, lean_object* v___x_4216_, lean_object* v_t_4217_, lean_object* v___x_4218_, lean_object* v_x1_4219_, lean_object* v_x_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v___f_4226_; uint8_t v___x_4227_; lean_object* v___x_4228_; 
v___f_4226_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4226_, 0, v___x_4201_);
lean_closure_set(v___f_4226_, 1, v_x1_4219_);
lean_closure_set(v___f_4226_, 2, v_indName_4202_);
lean_closure_set(v___f_4226_, 3, v_tail_4203_);
lean_closure_set(v___f_4226_, 4, v_params_4204_);
lean_closure_set(v___f_4226_, 5, v_is_4205_);
lean_closure_set(v___f_4226_, 6, v___x_4206_);
lean_closure_set(v___f_4226_, 7, v_head_4207_);
lean_closure_set(v___f_4226_, 8, v_ctors_4208_);
lean_closure_set(v___f_4226_, 9, v_numIndices_4209_);
lean_closure_set(v___f_4226_, 10, v___x_4210_);
lean_closure_set(v___f_4226_, 11, v___x_4211_);
lean_closure_set(v___f_4226_, 12, v_val_4212_);
lean_closure_set(v___f_4226_, 13, v_declName_4213_);
lean_closure_set(v___f_4226_, 14, v_levelParams_4214_);
lean_closure_set(v___f_4226_, 15, v_numParams_4215_);
lean_closure_set(v___f_4226_, 16, v___x_4216_);
v___x_4227_ = 0;
v___x_4228_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4217_, v___x_4218_, v___f_4226_, v___x_4227_, v___x_4227_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4229_ = _args[0];
lean_object* v_indName_4230_ = _args[1];
lean_object* v_tail_4231_ = _args[2];
lean_object* v_params_4232_ = _args[3];
lean_object* v_is_4233_ = _args[4];
lean_object* v___x_4234_ = _args[5];
lean_object* v_head_4235_ = _args[6];
lean_object* v_ctors_4236_ = _args[7];
lean_object* v_numIndices_4237_ = _args[8];
lean_object* v___x_4238_ = _args[9];
lean_object* v___x_4239_ = _args[10];
lean_object* v_val_4240_ = _args[11];
lean_object* v_declName_4241_ = _args[12];
lean_object* v_levelParams_4242_ = _args[13];
lean_object* v_numParams_4243_ = _args[14];
lean_object* v___x_4244_ = _args[15];
lean_object* v_t_4245_ = _args[16];
lean_object* v___x_4246_ = _args[17];
lean_object* v_x1_4247_ = _args[18];
lean_object* v_x_4248_ = _args[19];
lean_object* v___y_4249_ = _args[20];
lean_object* v___y_4250_ = _args[21];
lean_object* v___y_4251_ = _args[22];
lean_object* v___y_4252_ = _args[23];
lean_object* v___y_4253_ = _args[24];
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4229_, v_indName_4230_, v_tail_4231_, v_params_4232_, v_is_4233_, v___x_4234_, v_head_4235_, v_ctors_4236_, v_numIndices_4237_, v___x_4238_, v___x_4239_, v_val_4240_, v_declName_4241_, v_levelParams_4242_, v_numParams_4243_, v___x_4244_, v_t_4245_, v___x_4246_, v_x1_4247_, v_x_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec_ref(v_x_4248_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4255_, lean_object* v_indName_4256_, lean_object* v_tail_4257_, lean_object* v_params_4258_, lean_object* v_head_4259_, lean_object* v_ctors_4260_, lean_object* v_numIndices_4261_, lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v_val_4264_, lean_object* v_declName_4265_, lean_object* v_levelParams_4266_, lean_object* v_numParams_4267_, lean_object* v___x_4268_, lean_object* v_is_4269_, lean_object* v_t_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___f_4278_; uint8_t v___x_4279_; lean_object* v___x_4280_; 
v___x_4276_ = lean_unsigned_to_nat(1u);
v___x_4277_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4270_);
v___f_4278_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4278_, 0, v___x_4255_);
lean_closure_set(v___f_4278_, 1, v_indName_4256_);
lean_closure_set(v___f_4278_, 2, v_tail_4257_);
lean_closure_set(v___f_4278_, 3, v_params_4258_);
lean_closure_set(v___f_4278_, 4, v_is_4269_);
lean_closure_set(v___f_4278_, 5, v___x_4276_);
lean_closure_set(v___f_4278_, 6, v_head_4259_);
lean_closure_set(v___f_4278_, 7, v_ctors_4260_);
lean_closure_set(v___f_4278_, 8, v_numIndices_4261_);
lean_closure_set(v___f_4278_, 9, v___x_4262_);
lean_closure_set(v___f_4278_, 10, v___x_4263_);
lean_closure_set(v___f_4278_, 11, v_val_4264_);
lean_closure_set(v___f_4278_, 12, v_declName_4265_);
lean_closure_set(v___f_4278_, 13, v_levelParams_4266_);
lean_closure_set(v___f_4278_, 14, v_numParams_4267_);
lean_closure_set(v___f_4278_, 15, v___x_4268_);
lean_closure_set(v___f_4278_, 16, v_t_4270_);
lean_closure_set(v___f_4278_, 17, v___x_4277_);
v___x_4279_ = 0;
v___x_4280_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4270_, v___x_4277_, v___f_4278_, v___x_4279_, v___x_4279_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4281_ = _args[0];
lean_object* v_indName_4282_ = _args[1];
lean_object* v_tail_4283_ = _args[2];
lean_object* v_params_4284_ = _args[3];
lean_object* v_head_4285_ = _args[4];
lean_object* v_ctors_4286_ = _args[5];
lean_object* v_numIndices_4287_ = _args[6];
lean_object* v___x_4288_ = _args[7];
lean_object* v___x_4289_ = _args[8];
lean_object* v_val_4290_ = _args[9];
lean_object* v_declName_4291_ = _args[10];
lean_object* v_levelParams_4292_ = _args[11];
lean_object* v_numParams_4293_ = _args[12];
lean_object* v___x_4294_ = _args[13];
lean_object* v_is_4295_ = _args[14];
lean_object* v_t_4296_ = _args[15];
lean_object* v___y_4297_ = _args[16];
lean_object* v___y_4298_ = _args[17];
lean_object* v___y_4299_ = _args[18];
lean_object* v___y_4300_ = _args[19];
lean_object* v___y_4301_ = _args[20];
_start:
{
lean_object* v_res_4302_; 
v_res_4302_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4281_, v_indName_4282_, v_tail_4283_, v_params_4284_, v_head_4285_, v_ctors_4286_, v_numIndices_4287_, v___x_4288_, v___x_4289_, v_val_4290_, v_declName_4291_, v_levelParams_4292_, v_numParams_4293_, v___x_4294_, v_is_4295_, v_t_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
lean_dec(v___y_4300_);
lean_dec_ref(v___y_4299_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
return v_res_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4303_, lean_object* v_indName_4304_, lean_object* v_tail_4305_, lean_object* v_head_4306_, lean_object* v_ctors_4307_, lean_object* v_numIndices_4308_, lean_object* v___x_4309_, lean_object* v___x_4310_, lean_object* v_val_4311_, lean_object* v_declName_4312_, lean_object* v_levelParams_4313_, lean_object* v_numParams_4314_, lean_object* v_params_4315_, lean_object* v_t_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v___x_4322_; lean_object* v___f_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; lean_object* v___x_4326_; 
v___x_4322_ = l_Lean_Expr_bindingBody_x21(v_t_4316_);
lean_inc_ref(v___x_4322_);
lean_inc(v_numIndices_4308_);
v___f_4323_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4323_, 0, v___x_4303_);
lean_closure_set(v___f_4323_, 1, v_indName_4304_);
lean_closure_set(v___f_4323_, 2, v_tail_4305_);
lean_closure_set(v___f_4323_, 3, v_params_4315_);
lean_closure_set(v___f_4323_, 4, v_head_4306_);
lean_closure_set(v___f_4323_, 5, v_ctors_4307_);
lean_closure_set(v___f_4323_, 6, v_numIndices_4308_);
lean_closure_set(v___f_4323_, 7, v___x_4309_);
lean_closure_set(v___f_4323_, 8, v___x_4310_);
lean_closure_set(v___f_4323_, 9, v_val_4311_);
lean_closure_set(v___f_4323_, 10, v_declName_4312_);
lean_closure_set(v___f_4323_, 11, v_levelParams_4313_);
lean_closure_set(v___f_4323_, 12, v_numParams_4314_);
lean_closure_set(v___f_4323_, 13, v___x_4322_);
v___x_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4324_, 0, v_numIndices_4308_);
v___x_4325_ = 0;
v___x_4326_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4322_, v___x_4324_, v___f_4323_, v___x_4325_, v___x_4325_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4327_ = _args[0];
lean_object* v_indName_4328_ = _args[1];
lean_object* v_tail_4329_ = _args[2];
lean_object* v_head_4330_ = _args[3];
lean_object* v_ctors_4331_ = _args[4];
lean_object* v_numIndices_4332_ = _args[5];
lean_object* v___x_4333_ = _args[6];
lean_object* v___x_4334_ = _args[7];
lean_object* v_val_4335_ = _args[8];
lean_object* v_declName_4336_ = _args[9];
lean_object* v_levelParams_4337_ = _args[10];
lean_object* v_numParams_4338_ = _args[11];
lean_object* v_params_4339_ = _args[12];
lean_object* v_t_4340_ = _args[13];
lean_object* v___y_4341_ = _args[14];
lean_object* v___y_4342_ = _args[15];
lean_object* v___y_4343_ = _args[16];
lean_object* v___y_4344_ = _args[17];
lean_object* v___y_4345_ = _args[18];
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4327_, v_indName_4328_, v_tail_4329_, v_head_4330_, v_ctors_4331_, v_numIndices_4332_, v___x_4333_, v___x_4334_, v_val_4335_, v_declName_4336_, v_levelParams_4337_, v_numParams_4338_, v_params_4339_, v_t_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec_ref(v_t_4340_);
return v_res_4346_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4351_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4352_ = lean_unsigned_to_nat(58u);
v___x_4353_ = lean_unsigned_to_nat(142u);
v___x_4354_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4355_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4356_ = l_mkPanicMessageWithDecl(v___x_4355_, v___x_4354_, v___x_4353_, v___x_4352_, v___x_4351_);
return v___x_4356_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4357_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4358_ = lean_unsigned_to_nat(60u);
v___x_4359_ = lean_unsigned_to_nat(136u);
v___x_4360_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4361_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4362_ = l_mkPanicMessageWithDecl(v___x_4361_, v___x_4360_, v___x_4359_, v___x_4358_, v___x_4357_);
return v___x_4362_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4363_, lean_object* v_indName_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_){
_start:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
v___x_4370_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_4364_);
v___x_4371_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4371_, 1);
if (lean_obj_tag(v_a_4372_) == 5)
{
lean_object* v_val_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v_val_4373_ = lean_ctor_get(v_a_4372_, 0);
lean_inc_ref(v_val_4373_);
lean_dec_ref_known(v_a_4372_, 1);
v___x_4374_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4363_);
v___x_4375_ = l_Lean_Name_append(v_declName_4363_, v___x_4374_);
lean_inc(v_indName_4364_);
lean_inc(v___x_4375_);
v___x_4376_ = l_Lean_mkCasesOnSameCtorHet(v___x_4375_, v_indName_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4408_; 
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; 
v_unused_4409_ = lean_ctor_get(v___x_4376_, 0);
lean_dec(v_unused_4409_);
v___x_4378_ = v___x_4376_;
v_isShared_4379_ = v_isSharedCheck_4408_;
goto v_resetjp_4377_;
}
else
{
lean_dec(v___x_4376_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4408_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; 
lean_inc(v_indName_4364_);
v___x_4380_ = l_Lean_mkCasesOnName(v_indName_4364_);
v___x_4381_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4380_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
if (lean_obj_tag(v___x_4381_) == 0)
{
lean_object* v_a_4382_; lean_object* v_levelParams_4383_; lean_object* v_type_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v_a_4382_ = lean_ctor_get(v___x_4381_, 0);
lean_inc(v_a_4382_);
lean_dec_ref_known(v___x_4381_, 1);
v_levelParams_4383_ = lean_ctor_get(v_a_4382_, 1);
lean_inc_n(v_levelParams_4383_, 2);
v_type_4384_ = lean_ctor_get(v_a_4382_, 2);
lean_inc_ref(v_type_4384_);
lean_dec(v_a_4382_);
v___x_4385_ = lean_box(0);
v___x_4386_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4383_, v___x_4385_);
if (lean_obj_tag(v___x_4386_) == 1)
{
lean_object* v_head_4387_; lean_object* v_tail_4388_; lean_object* v_numParams_4389_; lean_object* v_numIndices_4390_; lean_object* v_ctors_4391_; lean_object* v___f_4392_; lean_object* v___x_4394_; 
v_head_4387_ = lean_ctor_get(v___x_4386_, 0);
lean_inc(v_head_4387_);
v_tail_4388_ = lean_ctor_get(v___x_4386_, 1);
lean_inc(v_tail_4388_);
v_numParams_4389_ = lean_ctor_get(v_val_4373_, 1);
lean_inc_n(v_numParams_4389_, 2);
v_numIndices_4390_ = lean_ctor_get(v_val_4373_, 2);
lean_inc(v_numIndices_4390_);
v_ctors_4391_ = lean_ctor_get(v_val_4373_, 4);
lean_inc(v_ctors_4391_);
v___f_4392_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4392_, 0, v___x_4370_);
lean_closure_set(v___f_4392_, 1, v_indName_4364_);
lean_closure_set(v___f_4392_, 2, v_tail_4388_);
lean_closure_set(v___f_4392_, 3, v_head_4387_);
lean_closure_set(v___f_4392_, 4, v_ctors_4391_);
lean_closure_set(v___f_4392_, 5, v_numIndices_4390_);
lean_closure_set(v___f_4392_, 6, v___x_4375_);
lean_closure_set(v___f_4392_, 7, v___x_4386_);
lean_closure_set(v___f_4392_, 8, v_val_4373_);
lean_closure_set(v___f_4392_, 9, v_declName_4363_);
lean_closure_set(v___f_4392_, 10, v_levelParams_4383_);
lean_closure_set(v___f_4392_, 11, v_numParams_4389_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set_tag(v___x_4378_, 1);
lean_ctor_set(v___x_4378_, 0, v_numParams_4389_);
v___x_4394_ = v___x_4378_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_numParams_4389_);
v___x_4394_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
uint8_t v___x_4395_; lean_object* v___x_4396_; 
v___x_4395_ = 0;
v___x_4396_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4384_, v___x_4394_, v___f_4392_, v___x_4395_, v___x_4395_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
return v___x_4396_;
}
}
else
{
lean_object* v___x_4398_; lean_object* v___x_4399_; 
lean_dec(v___x_4386_);
lean_dec_ref(v_type_4384_);
lean_dec(v_levelParams_4383_);
lean_del_object(v___x_4378_);
lean_dec(v___x_4375_);
lean_dec_ref(v_val_4373_);
lean_dec(v_indName_4364_);
lean_dec(v_declName_4363_);
v___x_4398_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4399_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4398_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
return v___x_4399_;
}
}
else
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4407_; 
lean_del_object(v___x_4378_);
lean_dec(v___x_4375_);
lean_dec_ref(v_val_4373_);
lean_dec(v_indName_4364_);
lean_dec(v_declName_4363_);
v_a_4400_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4402_ = v___x_4381_;
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4381_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4407_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
lean_object* v___x_4405_; 
if (v_isShared_4403_ == 0)
{
v___x_4405_ = v___x_4402_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
}
}
else
{
lean_dec(v___x_4375_);
lean_dec_ref(v_val_4373_);
lean_dec(v_indName_4364_);
lean_dec(v_declName_4363_);
return v___x_4376_;
}
}
else
{
lean_object* v___x_4410_; lean_object* v___x_4411_; 
lean_dec(v_a_4372_);
lean_dec(v_indName_4364_);
lean_dec(v_declName_4363_);
v___x_4410_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4411_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4410_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
return v___x_4411_;
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; uint8_t v_isShared_4415_; uint8_t v_isSharedCheck_4419_; 
lean_dec(v_indName_4364_);
lean_dec(v_declName_4363_);
v_a_4412_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4414_ = v___x_4371_;
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
else
{
lean_inc(v_a_4412_);
lean_dec(v___x_4371_);
v___x_4414_ = lean_box(0);
v_isShared_4415_ = v_isSharedCheck_4419_;
goto v_resetjp_4413_;
}
v_resetjp_4413_:
{
lean_object* v___x_4417_; 
if (v_isShared_4415_ == 0)
{
v___x_4417_ = v___x_4414_;
goto v_reusejp_4416_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_a_4412_);
v___x_4417_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4416_;
}
v_reusejp_4416_:
{
return v___x_4417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4420_, lean_object* v_indName_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l_Lean_mkCasesOnSameCtor(v_declName_4420_, v_indName_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
lean_dec(v_a_4425_);
lean_dec_ref(v_a_4424_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4428_, lean_object* v_params_4429_, lean_object* v_motive_4430_, lean_object* v_as_4431_, size_t v_sz_4432_, size_t v_i_4433_, lean_object* v_bs_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v___x_4440_; 
v___x_4440_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4428_, v_params_4429_, v_motive_4430_, v_sz_4432_, v_i_4433_, v_bs_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4441_, lean_object* v_params_4442_, lean_object* v_motive_4443_, lean_object* v_as_4444_, lean_object* v_sz_4445_, lean_object* v_i_4446_, lean_object* v_bs_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
size_t v_sz_boxed_4453_; size_t v_i_boxed_4454_; lean_object* v_res_4455_; 
v_sz_boxed_4453_ = lean_unbox_usize(v_sz_4445_);
lean_dec(v_sz_4445_);
v_i_boxed_4454_ = lean_unbox_usize(v_i_4446_);
lean_dec(v_i_4446_);
v_res_4455_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4441_, v_params_4442_, v_motive_4443_, v_as_4444_, v_sz_boxed_4453_, v_i_boxed_4454_, v_bs_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec_ref(v_as_4444_);
lean_dec_ref(v_params_4442_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4456_, lean_object* v_params_4457_, lean_object* v_a_4458_, lean_object* v_snd_4459_, lean_object* v_alts_4460_, lean_object* v_as_4461_, size_t v_sz_4462_, size_t v_i_4463_, lean_object* v_bs_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v___x_4470_; 
v___x_4470_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4456_, v_params_4457_, v_a_4458_, v_snd_4459_, v_alts_4460_, v_sz_4462_, v_i_4463_, v_bs_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4471_, lean_object* v_params_4472_, lean_object* v_a_4473_, lean_object* v_snd_4474_, lean_object* v_alts_4475_, lean_object* v_as_4476_, lean_object* v_sz_4477_, lean_object* v_i_4478_, lean_object* v_bs_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
size_t v_sz_boxed_4485_; size_t v_i_boxed_4486_; lean_object* v_res_4487_; 
v_sz_boxed_4485_ = lean_unbox_usize(v_sz_4477_);
lean_dec(v_sz_4477_);
v_i_boxed_4486_ = lean_unbox_usize(v_i_4478_);
lean_dec(v_i_4478_);
v_res_4487_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4471_, v_params_4472_, v_a_4473_, v_snd_4474_, v_alts_4475_, v_as_4476_, v_sz_boxed_4485_, v_i_boxed_4486_, v_bs_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec_ref(v_as_4476_);
lean_dec_ref(v_params_4472_);
return v_res_4487_;
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
