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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v_nextMacroScope_289_; lean_object* v_ngen_290_; lean_object* v_auxDeclNGen_291_; lean_object* v_traceState_292_; lean_object* v_messages_293_; lean_object* v_infoState_294_; lean_object* v_snapshotTasks_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_320_; 
v___x_287_ = lean_st_ref_take(v___y_280_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
v_nextMacroScope_289_ = lean_ctor_get(v___x_287_, 1);
v_ngen_290_ = lean_ctor_get(v___x_287_, 2);
v_auxDeclNGen_291_ = lean_ctor_get(v___x_287_, 3);
v_traceState_292_ = lean_ctor_get(v___x_287_, 4);
v_messages_293_ = lean_ctor_get(v___x_287_, 6);
v_infoState_294_ = lean_ctor_get(v___x_287_, 7);
v_snapshotTasks_295_ = lean_ctor_get(v___x_287_, 8);
v_isSharedCheck_320_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v___x_287_, 5);
lean_dec(v_unused_321_);
v___x_297_ = v___x_287_;
v_isShared_298_ = v_isSharedCheck_320_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_snapshotTasks_295_);
lean_inc(v_infoState_294_);
lean_inc(v_messages_293_);
lean_inc(v_traceState_292_);
lean_inc(v_auxDeclNGen_291_);
lean_inc(v_ngen_290_);
lean_inc(v_nextMacroScope_289_);
lean_inc(v_env_288_);
lean_dec(v___x_287_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_320_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_Environment_setExporting(v_env_288_, v_isExporting_281_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 5, v___x_282_);
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_nextMacroScope_289_);
lean_ctor_set(v_reuseFailAlloc_319_, 2, v_ngen_290_);
lean_ctor_set(v_reuseFailAlloc_319_, 3, v_auxDeclNGen_291_);
lean_ctor_set(v_reuseFailAlloc_319_, 4, v_traceState_292_);
lean_ctor_set(v_reuseFailAlloc_319_, 5, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_319_, 6, v_messages_293_);
lean_ctor_set(v_reuseFailAlloc_319_, 7, v_infoState_294_);
lean_ctor_set(v_reuseFailAlloc_319_, 8, v_snapshotTasks_295_);
v___x_301_ = v_reuseFailAlloc_319_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v_mctx_304_; lean_object* v_zetaDeltaFVarIds_305_; lean_object* v_postponed_306_; lean_object* v_diag_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_317_; 
v___x_302_ = lean_st_ref_set(v___y_280_, v___x_301_);
v___x_303_ = lean_st_ref_take(v___y_283_);
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
lean_object* v___x_312_; 
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v___x_284_);
v___x_312_ = v___x_309_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_mctx_304_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_zetaDeltaFVarIds_305_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_postponed_306_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_diag_307_);
v___x_312_ = v_reuseFailAlloc_316_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_st_ref_set(v___y_283_, v___x_312_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
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
v___x_331_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_345_; lean_object* v_env_346_; uint8_t v_isExporting_347_; lean_object* v___x_348_; lean_object* v_env_349_; lean_object* v_nextMacroScope_350_; lean_object* v_ngen_351_; lean_object* v_auxDeclNGen_352_; lean_object* v_traceState_353_; lean_object* v_messages_354_; lean_object* v_infoState_355_; lean_object* v_snapshotTasks_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_410_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_346_);
lean_dec(v___x_345_);
v_isExporting_347_ = lean_ctor_get_uint8(v_env_346_, sizeof(void*)*8);
lean_dec_ref(v_env_346_);
v___x_348_ = lean_st_ref_take(v___y_343_);
v_env_349_ = lean_ctor_get(v___x_348_, 0);
v_nextMacroScope_350_ = lean_ctor_get(v___x_348_, 1);
v_ngen_351_ = lean_ctor_get(v___x_348_, 2);
v_auxDeclNGen_352_ = lean_ctor_get(v___x_348_, 3);
v_traceState_353_ = lean_ctor_get(v___x_348_, 4);
v_messages_354_ = lean_ctor_get(v___x_348_, 6);
v_infoState_355_ = lean_ctor_get(v___x_348_, 7);
v_snapshotTasks_356_ = lean_ctor_get(v___x_348_, 8);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_410_ == 0)
{
lean_object* v_unused_411_; 
v_unused_411_ = lean_ctor_get(v___x_348_, 5);
lean_dec(v_unused_411_);
v___x_358_ = v___x_348_;
v_isShared_359_ = v_isSharedCheck_410_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_snapshotTasks_356_);
lean_inc(v_infoState_355_);
lean_inc(v_messages_354_);
lean_inc(v_traceState_353_);
lean_inc(v_auxDeclNGen_352_);
lean_inc(v_ngen_351_);
lean_inc(v_nextMacroScope_350_);
lean_inc(v_env_349_);
lean_dec(v___x_348_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_410_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_360_ = l_Lean_Environment_setExporting(v_env_349_, v_isExporting_339_);
v___x_361_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 5, v___x_361_);
lean_ctor_set(v___x_358_, 0, v___x_360_);
v___x_363_ = v___x_358_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_nextMacroScope_350_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_ngen_351_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_auxDeclNGen_352_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_traceState_353_);
lean_ctor_set(v_reuseFailAlloc_409_, 5, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_409_, 6, v_messages_354_);
lean_ctor_set(v_reuseFailAlloc_409_, 7, v_infoState_355_);
lean_ctor_set(v_reuseFailAlloc_409_, 8, v_snapshotTasks_356_);
v___x_363_ = v_reuseFailAlloc_409_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_mctx_366_; lean_object* v_zetaDeltaFVarIds_367_; lean_object* v_postponed_368_; lean_object* v_diag_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_407_; 
v___x_364_ = lean_st_ref_set(v___y_343_, v___x_363_);
v___x_365_ = lean_st_ref_take(v___y_341_);
v_mctx_366_ = lean_ctor_get(v___x_365_, 0);
v_zetaDeltaFVarIds_367_ = lean_ctor_get(v___x_365_, 2);
v_postponed_368_ = lean_ctor_get(v___x_365_, 3);
v_diag_369_ = lean_ctor_get(v___x_365_, 4);
v_isSharedCheck_407_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_407_ == 0)
{
lean_object* v_unused_408_; 
v_unused_408_ = lean_ctor_get(v___x_365_, 1);
lean_dec(v_unused_408_);
v___x_371_ = v___x_365_;
v_isShared_372_ = v_isSharedCheck_407_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_diag_369_);
lean_inc(v_postponed_368_);
lean_inc(v_zetaDeltaFVarIds_367_);
lean_inc(v_mctx_366_);
lean_dec(v___x_365_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_407_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_373_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_mctx_366_);
lean_ctor_set(v_reuseFailAlloc_406_, 1, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_406_, 2, v_zetaDeltaFVarIds_367_);
lean_ctor_set(v_reuseFailAlloc_406_, 3, v_postponed_368_);
lean_ctor_set(v_reuseFailAlloc_406_, 4, v_diag_369_);
v___x_375_ = v_reuseFailAlloc_406_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
lean_object* v___x_376_; lean_object* v_r_377_; 
v___x_376_ = lean_st_ref_set(v___y_341_, v___x_375_);
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v_r_377_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
if (lean_obj_tag(v_r_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_394_; 
v_a_378_ = lean_ctor_get(v_r_377_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v_r_377_);
if (v_isSharedCheck_394_ == 0)
{
v___x_380_ = v_r_377_;
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v_r_377_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_394_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
lean_inc(v_a_378_);
if (v_isShared_381_ == 0)
{
lean_ctor_set_tag(v___x_380_, 1);
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_393_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
lean_object* v___x_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v___x_384_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_347_, v___x_361_, v___y_341_, v___x_373_, v___x_383_);
lean_dec_ref(v___x_383_);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v___x_384_, 0);
lean_dec(v_unused_392_);
v___x_386_ = v___x_384_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_dec(v___x_384_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 0, v_a_378_);
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_378_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
v_a_395_ = lean_ctor_get(v_r_377_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v_r_377_, 1);
v___x_396_ = lean_box(0);
v___x_397_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_347_, v___x_361_, v___y_341_, v___x_373_, v___x_396_);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_404_ == 0)
{
lean_object* v_unused_405_; 
v_unused_405_ = lean_ctor_get(v___x_397_, 0);
lean_dec(v_unused_405_);
v___x_399_ = v___x_397_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_dec(v___x_397_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
lean_ctor_set_tag(v___x_399_, 1);
lean_ctor_set(v___x_399_, 0, v_a_395_);
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_395_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_412_, lean_object* v_isExporting_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
uint8_t v_isExporting_boxed_419_; lean_object* v_res_420_; 
v_isExporting_boxed_419_ = lean_unbox(v_isExporting_413_);
v_res_420_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_412_, v_isExporting_boxed_419_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_421_, lean_object* v_x_422_, uint8_t v_isExporting_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_422_, v_isExporting_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_430_, lean_object* v_x_431_, lean_object* v_isExporting_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
uint8_t v_isExporting_boxed_438_; lean_object* v_res_439_; 
v_isExporting_boxed_438_ = lean_unbox(v_isExporting_432_);
v_res_439_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_430_, v_x_431_, v_isExporting_boxed_438_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_msg_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v___f_447_; lean_object* v___x_15649__overap_448_; lean_object* v___x_449_; 
v___f_447_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15649__overap_448_ = lean_panic_fn_borrowed(v___f_447_, v_msg_441_);
lean_inc(v___y_445_);
lean_inc_ref(v___y_444_);
lean_inc(v___y_443_);
lean_inc_ref(v___y_442_);
v___x_449_ = lean_apply_5(v___x_15649__overap_448_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, lean_box(0));
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_msg_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_msg_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object* v_name_457_, lean_object* v_type_458_, lean_object* v_k_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_){
_start:
{
uint8_t v___x_465_; uint8_t v___x_466_; lean_object* v___x_467_; 
v___x_465_ = 0;
v___x_466_ = 0;
v___x_467_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_457_, v___x_465_, v_type_458_, v_k_459_, v___x_466_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object* v_name_468_, lean_object* v_type_469_, lean_object* v_k_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_468_, v_type_469_, v_k_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object* v___x_477_, lean_object* v_ism2_478_, lean_object* v_motive_479_, uint8_t v___x_480_, uint8_t v___x_481_, uint8_t v___x_482_, lean_object* v_a_483_, lean_object* v___f_484_, lean_object* v_zs1_485_, lean_object* v_val_486_, lean_object* v___x_487_, lean_object* v_indName_488_, lean_object* v_v_489_, lean_object* v___x_490_, lean_object* v_params_491_, lean_object* v___x_492_, lean_object* v_h_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = l_Array_append___redArg(v___x_477_, v_ism2_478_);
v___x_500_ = l_Lean_mkAppN(v_motive_479_, v___x_499_);
lean_dec_ref(v___x_499_);
v___x_501_ = l_Lean_Meta_mkLambdaFVars(v_ism2_478_, v___x_500_, v___x_480_, v___x_481_, v___x_480_, v___x_481_, v___x_482_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v___x_503_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_483_, v___f_484_, v___x_480_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___y_506_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_509_ = l_Lean_InductiveVal_numCtors(v_val_486_);
v___x_510_ = lean_nat_dec_eq(v___x_509_, v___x_487_);
lean_dec(v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v___x_492_);
v___x_511_ = l_Lean_mkConstructorElimName(v_indName_488_, v_v_489_);
v___x_512_ = l_Lean_mkConst(v___x_511_, v___x_490_);
v___x_513_ = lean_mk_empty_array_with_capacity(v___x_487_);
v___x_514_ = lean_array_push(v___x_513_, v_a_502_);
v___x_515_ = l_Array_append___redArg(v_params_491_, v___x_514_);
lean_dec_ref(v___x_514_);
v___x_516_ = l_Array_append___redArg(v___x_515_, v_ism2_478_);
v___x_517_ = lean_unsigned_to_nat(2u);
v___x_518_ = lean_mk_empty_array_with_capacity(v___x_517_);
lean_inc_ref(v_h_493_);
v___x_519_ = lean_array_push(v___x_518_, v_h_493_);
v___x_520_ = lean_array_push(v___x_519_, v_a_504_);
v___x_521_ = l_Array_append___redArg(v___x_516_, v___x_520_);
lean_dec_ref(v___x_520_);
v___x_522_ = l_Lean_mkAppN(v___x_512_, v___x_521_);
lean_dec_ref(v___x_521_);
v___y_506_ = v___x_522_;
goto v___jp_505_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_v_489_);
lean_dec(v_indName_488_);
v___x_523_ = l_Lean_mkConst(v___x_492_, v___x_490_);
v___x_524_ = lean_mk_empty_array_with_capacity(v___x_487_);
lean_inc_ref(v___x_524_);
v___x_525_ = lean_array_push(v___x_524_, v_a_502_);
v___x_526_ = l_Array_append___redArg(v_params_491_, v___x_525_);
lean_dec_ref(v___x_525_);
v___x_527_ = l_Array_append___redArg(v___x_526_, v_ism2_478_);
v___x_528_ = lean_array_push(v___x_524_, v_a_504_);
v___x_529_ = l_Array_append___redArg(v___x_527_, v___x_528_);
lean_dec_ref(v___x_528_);
v___x_530_ = l_Lean_mkAppN(v___x_523_, v___x_529_);
lean_dec_ref(v___x_529_);
v___y_506_ = v___x_530_;
goto v___jp_505_;
}
v___jp_505_:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = lean_array_push(v_zs1_485_, v_h_493_);
v___x_508_ = l_Lean_Meta_mkLambdaFVars(v___x_507_, v___y_506_, v___x_480_, v___x_481_, v___x_480_, v___x_481_, v___x_482_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec_ref(v___x_507_);
return v___x_508_;
}
}
else
{
lean_dec(v_a_502_);
lean_dec_ref(v_h_493_);
lean_dec(v___x_492_);
lean_dec_ref(v_params_491_);
lean_dec(v___x_490_);
lean_dec(v_v_489_);
lean_dec(v_indName_488_);
lean_dec_ref(v_zs1_485_);
return v___x_503_;
}
}
else
{
lean_dec_ref(v_h_493_);
lean_dec(v___x_492_);
lean_dec_ref(v_params_491_);
lean_dec(v___x_490_);
lean_dec(v_v_489_);
lean_dec(v_indName_488_);
lean_dec_ref(v_zs1_485_);
lean_dec_ref(v___f_484_);
lean_dec_ref(v_a_483_);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_531_ = _args[0];
lean_object* v_ism2_532_ = _args[1];
lean_object* v_motive_533_ = _args[2];
lean_object* v___x_534_ = _args[3];
lean_object* v___x_535_ = _args[4];
lean_object* v___x_536_ = _args[5];
lean_object* v_a_537_ = _args[6];
lean_object* v___f_538_ = _args[7];
lean_object* v_zs1_539_ = _args[8];
lean_object* v_val_540_ = _args[9];
lean_object* v___x_541_ = _args[10];
lean_object* v_indName_542_ = _args[11];
lean_object* v_v_543_ = _args[12];
lean_object* v___x_544_ = _args[13];
lean_object* v_params_545_ = _args[14];
lean_object* v___x_546_ = _args[15];
lean_object* v_h_547_ = _args[16];
lean_object* v___y_548_ = _args[17];
lean_object* v___y_549_ = _args[18];
lean_object* v___y_550_ = _args[19];
lean_object* v___y_551_ = _args[20];
lean_object* v___y_552_ = _args[21];
_start:
{
uint8_t v___x_20742__boxed_553_; uint8_t v___x_20743__boxed_554_; uint8_t v___x_20744__boxed_555_; lean_object* v_res_556_; 
v___x_20742__boxed_553_ = lean_unbox(v___x_534_);
v___x_20743__boxed_554_ = lean_unbox(v___x_535_);
v___x_20744__boxed_555_ = lean_unbox(v___x_536_);
v_res_556_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_531_, v_ism2_532_, v_motive_533_, v___x_20742__boxed_553_, v___x_20743__boxed_554_, v___x_20744__boxed_555_, v_a_537_, v___f_538_, v_zs1_539_, v_val_540_, v___x_541_, v_indName_542_, v_v_543_, v___x_544_, v_params_545_, v___x_546_, v_h_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___x_541_);
lean_dec_ref(v_val_540_);
lean_dec_ref(v_ism2_532_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object* v___x_557_, lean_object* v_alts_558_, lean_object* v___x_559_, lean_object* v_zs1_560_, uint8_t v___x_561_, uint8_t v___x_562_, uint8_t v___x_563_, lean_object* v_zs2_564_, lean_object* v_x_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_571_ = lean_array_get_borrowed(v___x_557_, v_alts_558_, v___x_559_);
v___x_572_ = l_Array_append___redArg(v_zs1_560_, v_zs2_564_);
lean_inc(v___x_571_);
v___x_573_ = l_Lean_mkAppN(v___x_571_, v___x_572_);
lean_dec_ref(v___x_572_);
v___x_574_ = l_Lean_Meta_mkLambdaFVars(v_zs2_564_, v___x_573_, v___x_561_, v___x_562_, v___x_561_, v___x_562_, v___x_563_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object* v___x_575_, lean_object* v_alts_576_, lean_object* v___x_577_, lean_object* v_zs1_578_, lean_object* v___x_579_, lean_object* v___x_580_, lean_object* v___x_581_, lean_object* v_zs2_582_, lean_object* v_x_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
uint8_t v___x_20854__boxed_589_; uint8_t v___x_20855__boxed_590_; uint8_t v___x_20856__boxed_591_; lean_object* v_res_592_; 
v___x_20854__boxed_589_ = lean_unbox(v___x_579_);
v___x_20855__boxed_590_ = lean_unbox(v___x_580_);
v___x_20856__boxed_591_ = lean_unbox(v___x_581_);
v_res_592_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_575_, v_alts_576_, v___x_577_, v_zs1_578_, v___x_20854__boxed_589_, v___x_20855__boxed_590_, v___x_20856__boxed_591_, v_zs2_582_, v_x_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec_ref(v_x_583_);
lean_dec_ref(v_zs2_582_);
lean_dec(v___x_577_);
lean_dec_ref(v_alts_576_);
lean_dec_ref(v___x_575_);
return v_res_592_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_593_; lean_object* v_dummy_594_; 
v___x_593_ = lean_box(0);
v_dummy_594_ = l_Lean_Expr_sort___override(v___x_593_);
return v_dummy_594_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = lean_box(0);
v___x_602_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4));
v___x_603_ = l_Lean_mkConst(v___x_602_, v___x_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object* v___x_604_, lean_object* v_alts_605_, lean_object* v___x_606_, uint8_t v___x_607_, uint8_t v___x_608_, uint8_t v___x_609_, lean_object* v___x_610_, lean_object* v___x_611_, lean_object* v___x_612_, lean_object* v_ism2_613_, lean_object* v_motive_614_, lean_object* v_a_615_, lean_object* v_val_616_, lean_object* v_indName_617_, lean_object* v_v_618_, lean_object* v___x_619_, lean_object* v_params_620_, lean_object* v___x_621_, lean_object* v___x_622_, lean_object* v___x_623_, lean_object* v_zs1_624_, lean_object* v_ctorRet1_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
v___x_631_ = lean_whnf(v_ctorRet1_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___f_636_; lean_object* v___x_637_; lean_object* v_dummy_638_; lean_object* v_nargs_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___f_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___x_631_, 1);
v___x_633_ = lean_box(v___x_607_);
v___x_634_ = lean_box(v___x_608_);
v___x_635_ = lean_box(v___x_609_);
lean_inc_ref(v_zs1_624_);
lean_inc(v___x_606_);
v___f_636_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_636_, 0, v___x_604_);
lean_closure_set(v___f_636_, 1, v_alts_605_);
lean_closure_set(v___f_636_, 2, v___x_606_);
lean_closure_set(v___f_636_, 3, v_zs1_624_);
lean_closure_set(v___f_636_, 4, v___x_633_);
lean_closure_set(v___f_636_, 5, v___x_634_);
lean_closure_set(v___f_636_, 6, v___x_635_);
v___x_637_ = l_Lean_mkAppN(v___x_610_, v_zs1_624_);
v_dummy_638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_639_ = l_Lean_Expr_getAppNumArgs(v_a_632_);
lean_inc(v_nargs_639_);
v___x_640_ = lean_mk_array(v_nargs_639_, v_dummy_638_);
v___x_641_ = lean_nat_sub(v_nargs_639_, v___x_611_);
lean_dec(v_nargs_639_);
v___x_642_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_632_, v___x_640_, v___x_641_);
v___x_643_ = lean_array_get_size(v___x_642_);
v___x_644_ = l_Array_toSubarray___redArg(v___x_642_, v___x_612_, v___x_643_);
v___x_645_ = l_Subarray_copy___redArg(v___x_644_);
v___x_646_ = lean_array_push(v___x_645_, v___x_637_);
v___x_647_ = lean_box(v___x_607_);
v___x_648_ = lean_box(v___x_608_);
v___x_649_ = lean_box(v___x_609_);
lean_inc(v___x_611_);
v___f_650_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed), 22, 16);
lean_closure_set(v___f_650_, 0, v___x_646_);
lean_closure_set(v___f_650_, 1, v_ism2_613_);
lean_closure_set(v___f_650_, 2, v_motive_614_);
lean_closure_set(v___f_650_, 3, v___x_647_);
lean_closure_set(v___f_650_, 4, v___x_648_);
lean_closure_set(v___f_650_, 5, v___x_649_);
lean_closure_set(v___f_650_, 6, v_a_615_);
lean_closure_set(v___f_650_, 7, v___f_636_);
lean_closure_set(v___f_650_, 8, v_zs1_624_);
lean_closure_set(v___f_650_, 9, v_val_616_);
lean_closure_set(v___f_650_, 10, v___x_611_);
lean_closure_set(v___f_650_, 11, v_indName_617_);
lean_closure_set(v___f_650_, 12, v_v_618_);
lean_closure_set(v___f_650_, 13, v___x_619_);
lean_closure_set(v___f_650_, 14, v_params_620_);
lean_closure_set(v___f_650_, 15, v___x_621_);
v___x_651_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2));
v___x_652_ = l_Lean_Level_ofNat(v___x_611_);
lean_dec(v___x_611_);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = l_Lean_mkConst(v___x_651_, v___x_654_);
v___x_656_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
v___x_657_ = l_Lean_mkRawNatLit(v___x_606_);
v___x_658_ = l_Lean_mkApp3(v___x_655_, v___x_656_, v___x_622_, v___x_657_);
v___x_659_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_623_, v___x_658_, v___f_650_, v___y_626_, v___y_627_, v___y_628_, v___y_629_);
return v___x_659_;
}
else
{
lean_dec_ref(v_zs1_624_);
lean_dec(v___x_623_);
lean_dec_ref(v___x_622_);
lean_dec(v___x_621_);
lean_dec_ref(v_params_620_);
lean_dec(v___x_619_);
lean_dec(v_v_618_);
lean_dec(v_indName_617_);
lean_dec_ref(v_val_616_);
lean_dec_ref(v_a_615_);
lean_dec_ref(v_motive_614_);
lean_dec_ref(v_ism2_613_);
lean_dec(v___x_612_);
lean_dec(v___x_611_);
lean_dec_ref(v___x_610_);
lean_dec(v___x_606_);
lean_dec_ref(v_alts_605_);
lean_dec_ref(v___x_604_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_660_ = _args[0];
lean_object* v_alts_661_ = _args[1];
lean_object* v___x_662_ = _args[2];
lean_object* v___x_663_ = _args[3];
lean_object* v___x_664_ = _args[4];
lean_object* v___x_665_ = _args[5];
lean_object* v___x_666_ = _args[6];
lean_object* v___x_667_ = _args[7];
lean_object* v___x_668_ = _args[8];
lean_object* v_ism2_669_ = _args[9];
lean_object* v_motive_670_ = _args[10];
lean_object* v_a_671_ = _args[11];
lean_object* v_val_672_ = _args[12];
lean_object* v_indName_673_ = _args[13];
lean_object* v_v_674_ = _args[14];
lean_object* v___x_675_ = _args[15];
lean_object* v_params_676_ = _args[16];
lean_object* v___x_677_ = _args[17];
lean_object* v___x_678_ = _args[18];
lean_object* v___x_679_ = _args[19];
lean_object* v_zs1_680_ = _args[20];
lean_object* v_ctorRet1_681_ = _args[21];
lean_object* v___y_682_ = _args[22];
lean_object* v___y_683_ = _args[23];
lean_object* v___y_684_ = _args[24];
lean_object* v___y_685_ = _args[25];
lean_object* v___y_686_ = _args[26];
_start:
{
uint8_t v___x_20915__boxed_687_; uint8_t v___x_20916__boxed_688_; uint8_t v___x_20917__boxed_689_; lean_object* v_res_690_; 
v___x_20915__boxed_687_ = lean_unbox(v___x_663_);
v___x_20916__boxed_688_ = lean_unbox(v___x_664_);
v___x_20917__boxed_689_ = lean_unbox(v___x_665_);
v_res_690_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_660_, v_alts_661_, v___x_662_, v___x_20915__boxed_687_, v___x_20916__boxed_688_, v___x_20917__boxed_689_, v___x_666_, v___x_667_, v___x_668_, v_ism2_669_, v_motive_670_, v_a_671_, v_val_672_, v_indName_673_, v_v_674_, v___x_675_, v_params_676_, v___x_677_, v___x_678_, v___x_679_, v_zs1_680_, v_ctorRet1_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object* v_tail_694_, lean_object* v_params_695_, lean_object* v_alts_696_, lean_object* v___x_697_, lean_object* v_ism2_698_, lean_object* v_motive_699_, lean_object* v_val_700_, lean_object* v_indName_701_, lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v___x_704_, size_t v_sz_705_, size_t v_i_706_, lean_object* v_bs_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
uint8_t v___x_713_; 
v___x_713_ = lean_usize_dec_lt(v_i_706_, v_sz_705_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; 
lean_dec_ref(v___x_704_);
lean_dec(v___x_703_);
lean_dec(v___x_702_);
lean_dec(v_indName_701_);
lean_dec_ref(v_val_700_);
lean_dec_ref(v_motive_699_);
lean_dec_ref(v_ism2_698_);
lean_dec(v___x_697_);
lean_dec_ref(v_alts_696_);
lean_dec_ref(v_params_695_);
lean_dec(v_tail_694_);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v_bs_707_);
return v___x_714_;
}
else
{
lean_object* v_v_715_; lean_object* v___x_716_; lean_object* v_bs_x27_717_; lean_object* v___y_719_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v_v_715_ = lean_array_uget(v_bs_707_, v_i_706_);
v___x_716_ = lean_unsigned_to_nat(0u);
v_bs_x27_717_ = lean_array_uset(v_bs_707_, v_i_706_, v___x_716_);
lean_inc(v_tail_694_);
lean_inc(v_v_715_);
v___x_733_ = l_Lean_mkConst(v_v_715_, v_tail_694_);
v___x_734_ = l_Lean_mkAppN(v___x_733_, v_params_695_);
lean_inc(v___y_711_);
lean_inc_ref(v___y_710_);
lean_inc(v___y_709_);
lean_inc_ref(v___y_708_);
lean_inc_ref(v___x_734_);
v___x_735_ = lean_infer_type(v___x_734_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; uint8_t v___x_738_; uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___f_746_; lean_object* v___x_747_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc_n(v_a_736_, 2);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_Lean_instInhabitedExpr;
v___x_738_ = 0;
v___x_739_ = 1;
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_742_ = lean_usize_to_nat(v_i_706_);
v___x_743_ = lean_box(v___x_738_);
v___x_744_ = lean_box(v___x_713_);
v___x_745_ = lean_box(v___x_739_);
lean_inc_ref(v___x_704_);
lean_inc(v___x_703_);
lean_inc_ref(v_params_695_);
lean_inc(v___x_702_);
lean_inc(v_indName_701_);
lean_inc_ref(v_val_700_);
lean_inc_ref(v_motive_699_);
lean_inc_ref(v_ism2_698_);
lean_inc(v___x_697_);
lean_inc_ref(v_alts_696_);
v___f_746_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed), 27, 20);
lean_closure_set(v___f_746_, 0, v___x_737_);
lean_closure_set(v___f_746_, 1, v_alts_696_);
lean_closure_set(v___f_746_, 2, v___x_742_);
lean_closure_set(v___f_746_, 3, v___x_743_);
lean_closure_set(v___f_746_, 4, v___x_744_);
lean_closure_set(v___f_746_, 5, v___x_745_);
lean_closure_set(v___f_746_, 6, v___x_734_);
lean_closure_set(v___f_746_, 7, v___x_740_);
lean_closure_set(v___f_746_, 8, v___x_697_);
lean_closure_set(v___f_746_, 9, v_ism2_698_);
lean_closure_set(v___f_746_, 10, v_motive_699_);
lean_closure_set(v___f_746_, 11, v_a_736_);
lean_closure_set(v___f_746_, 12, v_val_700_);
lean_closure_set(v___f_746_, 13, v_indName_701_);
lean_closure_set(v___f_746_, 14, v_v_715_);
lean_closure_set(v___f_746_, 15, v___x_702_);
lean_closure_set(v___f_746_, 16, v_params_695_);
lean_closure_set(v___f_746_, 17, v___x_703_);
lean_closure_set(v___f_746_, 18, v___x_704_);
lean_closure_set(v___f_746_, 19, v___x_741_);
v___x_747_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_736_, v___f_746_, v___x_738_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
v___y_719_ = v___x_747_;
goto v___jp_718_;
}
else
{
lean_dec_ref(v___x_734_);
lean_dec(v_v_715_);
v___y_719_ = v___x_735_;
goto v___jp_718_;
}
v___jp_718_:
{
if (lean_obj_tag(v___y_719_) == 0)
{
lean_object* v_a_720_; size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v_a_720_ = lean_ctor_get(v___y_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref_known(v___y_719_, 1);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_706_, v___x_721_);
v___x_723_ = lean_array_uset(v_bs_x27_717_, v_i_706_, v_a_720_);
v_i_706_ = v___x_722_;
v_bs_707_ = v___x_723_;
goto _start;
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_bs_x27_717_);
lean_dec_ref(v___x_704_);
lean_dec(v___x_703_);
lean_dec(v___x_702_);
lean_dec(v_indName_701_);
lean_dec_ref(v_val_700_);
lean_dec_ref(v_motive_699_);
lean_dec_ref(v_ism2_698_);
lean_dec(v___x_697_);
lean_dec_ref(v_alts_696_);
lean_dec_ref(v_params_695_);
lean_dec(v_tail_694_);
v_a_725_ = lean_ctor_get(v___y_719_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___y_719_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___y_719_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___y_719_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_tail_748_ = _args[0];
lean_object* v_params_749_ = _args[1];
lean_object* v_alts_750_ = _args[2];
lean_object* v___x_751_ = _args[3];
lean_object* v_ism2_752_ = _args[4];
lean_object* v_motive_753_ = _args[5];
lean_object* v_val_754_ = _args[6];
lean_object* v_indName_755_ = _args[7];
lean_object* v___x_756_ = _args[8];
lean_object* v___x_757_ = _args[9];
lean_object* v___x_758_ = _args[10];
lean_object* v_sz_759_ = _args[11];
lean_object* v_i_760_ = _args[12];
lean_object* v_bs_761_ = _args[13];
lean_object* v___y_762_ = _args[14];
lean_object* v___y_763_ = _args[15];
lean_object* v___y_764_ = _args[16];
lean_object* v___y_765_ = _args[17];
lean_object* v___y_766_ = _args[18];
_start:
{
size_t v_sz_boxed_767_; size_t v_i_boxed_768_; lean_object* v_res_769_; 
v_sz_boxed_767_ = lean_unbox_usize(v_sz_759_);
lean_dec(v_sz_759_);
v_i_boxed_768_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_res_769_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_748_, v_params_749_, v_alts_750_, v___x_751_, v_ism2_752_, v_motive_753_, v_val_754_, v_indName_755_, v___x_756_, v___x_757_, v___x_758_, v_sz_boxed_767_, v_i_boxed_768_, v_bs_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_770_, lean_object* v___x_771_, lean_object* v_a_772_, lean_object* v_ism1_773_, uint8_t v___x_774_, uint8_t v___x_775_, uint8_t v___x_776_, lean_object* v___x_777_, lean_object* v_tail_778_, lean_object* v_params_779_, lean_object* v_alts_780_, lean_object* v_numParams_781_, lean_object* v_ism2_782_, lean_object* v_val_783_, lean_object* v_indName_784_, lean_object* v___x_785_, lean_object* v___x_786_, lean_object* v___x_787_, lean_object* v_name_788_, lean_object* v___x_789_, lean_object* v_heq_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
lean_inc_ref(v_motive_770_);
v___x_796_ = l_Lean_mkAppN(v_motive_770_, v___x_771_);
v___x_797_ = l_Lean_mkArrow(v_a_772_, v___x_796_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = l_Lean_Meta_mkLambdaFVars(v_ism1_773_, v_a_798_, v___x_774_, v___x_775_, v___x_774_, v___x_775_, v___x_776_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; size_t v_sz_801_; size_t v___x_802_; lean_object* v___x_803_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref_known(v___x_799_, 1);
v_sz_801_ = lean_array_size(v___x_777_);
v___x_802_ = ((size_t)0ULL);
lean_inc(v___x_785_);
lean_inc_ref(v_motive_770_);
lean_inc_ref(v_ism2_782_);
lean_inc_ref(v_alts_780_);
lean_inc_ref(v_params_779_);
v___x_803_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_778_, v_params_779_, v_alts_780_, v_numParams_781_, v_ism2_782_, v_motive_770_, v_val_783_, v_indName_784_, v___x_785_, v___x_786_, v___x_787_, v_sz_801_, v___x_802_, v___x_777_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
lean_inc_ref(v_heq_790_);
v___x_805_ = l_Lean_Meta_mkEqSymm(v_heq_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v___x_807_ = l_Lean_mkConst(v_name_788_, v___x_785_);
v___x_808_ = l_Lean_mkAppN(v___x_807_, v_params_779_);
v___x_809_ = l_Lean_Expr_app___override(v___x_808_, v_a_800_);
v___x_810_ = l_Lean_mkAppN(v___x_809_, v_ism1_773_);
v___x_811_ = l_Lean_mkAppN(v___x_810_, v_a_804_);
lean_dec(v_a_804_);
v___x_812_ = l_Lean_Expr_app___override(v___x_811_, v_a_806_);
v___x_813_ = lean_mk_empty_array_with_capacity(v___x_789_);
lean_inc_ref(v___x_813_);
v___x_814_ = lean_array_push(v___x_813_, v_motive_770_);
v___x_815_ = l_Array_append___redArg(v_params_779_, v___x_814_);
lean_dec_ref(v___x_814_);
v___x_816_ = l_Array_append___redArg(v___x_815_, v_ism1_773_);
v___x_817_ = l_Array_append___redArg(v___x_816_, v_ism2_782_);
lean_dec_ref(v_ism2_782_);
v___x_818_ = lean_array_push(v___x_813_, v_heq_790_);
v___x_819_ = l_Array_append___redArg(v___x_817_, v___x_818_);
lean_dec_ref(v___x_818_);
v___x_820_ = l_Array_append___redArg(v___x_819_, v_alts_780_);
lean_dec_ref(v_alts_780_);
v___x_821_ = l_Lean_Meta_mkLambdaFVars(v___x_820_, v___x_812_, v___x_774_, v___x_775_, v___x_774_, v___x_775_, v___x_776_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec_ref(v___x_820_);
return v___x_821_;
}
else
{
lean_dec(v_a_804_);
lean_dec(v_a_800_);
lean_dec_ref(v_heq_790_);
lean_dec(v_name_788_);
lean_dec(v___x_785_);
lean_dec_ref(v_ism2_782_);
lean_dec_ref(v_alts_780_);
lean_dec_ref(v_params_779_);
lean_dec_ref(v_motive_770_);
return v___x_805_;
}
}
else
{
lean_object* v_a_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_829_; 
lean_dec(v_a_800_);
lean_dec_ref(v_heq_790_);
lean_dec(v_name_788_);
lean_dec(v___x_785_);
lean_dec_ref(v_ism2_782_);
lean_dec_ref(v_alts_780_);
lean_dec_ref(v_params_779_);
lean_dec_ref(v_motive_770_);
v_a_822_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_829_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_829_ == 0)
{
v___x_824_ = v___x_803_;
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_a_822_);
lean_dec(v___x_803_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_829_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_827_; 
if (v_isShared_825_ == 0)
{
v___x_827_ = v___x_824_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_828_; 
v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
v___x_827_ = v_reuseFailAlloc_828_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
return v___x_827_;
}
}
}
}
else
{
lean_dec_ref(v_heq_790_);
lean_dec(v_name_788_);
lean_dec_ref(v___x_787_);
lean_dec(v___x_786_);
lean_dec(v___x_785_);
lean_dec(v_indName_784_);
lean_dec_ref(v_val_783_);
lean_dec_ref(v_ism2_782_);
lean_dec(v_numParams_781_);
lean_dec_ref(v_alts_780_);
lean_dec_ref(v_params_779_);
lean_dec(v_tail_778_);
lean_dec_ref(v___x_777_);
lean_dec_ref(v_motive_770_);
return v___x_799_;
}
}
else
{
lean_dec_ref(v_heq_790_);
lean_dec(v_name_788_);
lean_dec_ref(v___x_787_);
lean_dec(v___x_786_);
lean_dec(v___x_785_);
lean_dec(v_indName_784_);
lean_dec_ref(v_val_783_);
lean_dec_ref(v_ism2_782_);
lean_dec(v_numParams_781_);
lean_dec_ref(v_alts_780_);
lean_dec_ref(v_params_779_);
lean_dec(v_tail_778_);
lean_dec_ref(v___x_777_);
lean_dec_ref(v_motive_770_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object** _args){
lean_object* v_motive_830_ = _args[0];
lean_object* v___x_831_ = _args[1];
lean_object* v_a_832_ = _args[2];
lean_object* v_ism1_833_ = _args[3];
lean_object* v___x_834_ = _args[4];
lean_object* v___x_835_ = _args[5];
lean_object* v___x_836_ = _args[6];
lean_object* v___x_837_ = _args[7];
lean_object* v_tail_838_ = _args[8];
lean_object* v_params_839_ = _args[9];
lean_object* v_alts_840_ = _args[10];
lean_object* v_numParams_841_ = _args[11];
lean_object* v_ism2_842_ = _args[12];
lean_object* v_val_843_ = _args[13];
lean_object* v_indName_844_ = _args[14];
lean_object* v___x_845_ = _args[15];
lean_object* v___x_846_ = _args[16];
lean_object* v___x_847_ = _args[17];
lean_object* v_name_848_ = _args[18];
lean_object* v___x_849_ = _args[19];
lean_object* v_heq_850_ = _args[20];
lean_object* v___y_851_ = _args[21];
lean_object* v___y_852_ = _args[22];
lean_object* v___y_853_ = _args[23];
lean_object* v___y_854_ = _args[24];
lean_object* v___y_855_ = _args[25];
_start:
{
uint8_t v___x_21146__boxed_856_; uint8_t v___x_21147__boxed_857_; uint8_t v___x_21148__boxed_858_; lean_object* v_res_859_; 
v___x_21146__boxed_856_ = lean_unbox(v___x_834_);
v___x_21147__boxed_857_ = lean_unbox(v___x_835_);
v___x_21148__boxed_858_ = lean_unbox(v___x_836_);
v_res_859_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_830_, v___x_831_, v_a_832_, v_ism1_833_, v___x_21146__boxed_856_, v___x_21147__boxed_857_, v___x_21148__boxed_858_, v___x_837_, v_tail_838_, v_params_839_, v_alts_840_, v_numParams_841_, v_ism2_842_, v_val_843_, v_indName_844_, v___x_845_, v___x_846_, v___x_847_, v_name_848_, v___x_849_, v_heq_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v___x_849_);
lean_dec_ref(v_ism1_833_);
lean_dec_ref(v___x_831_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_860_, lean_object* v_tail_861_, lean_object* v_params_862_, lean_object* v_ism1_863_, lean_object* v_ism2_864_, lean_object* v_motive_865_, lean_object* v___x_866_, uint8_t v___x_867_, uint8_t v___x_868_, uint8_t v___x_869_, lean_object* v___x_870_, lean_object* v_numParams_871_, lean_object* v_val_872_, lean_object* v___x_873_, lean_object* v___x_874_, lean_object* v_name_875_, lean_object* v___x_876_, lean_object* v_alts_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_inc(v_indName_860_);
v___x_883_ = l_Lean_mkCtorIdxName(v_indName_860_);
lean_inc(v_tail_861_);
v___x_884_ = l_Lean_mkConst(v___x_883_, v_tail_861_);
lean_inc_ref_n(v_params_862_, 2);
v___x_885_ = l_Array_append___redArg(v_params_862_, v_ism1_863_);
lean_inc_ref(v___x_884_);
v___x_886_ = l_Lean_mkAppN(v___x_884_, v___x_885_);
lean_dec_ref(v___x_885_);
v___x_887_ = l_Array_append___redArg(v_params_862_, v_ism2_864_);
v___x_888_ = l_Lean_mkAppN(v___x_884_, v___x_887_);
lean_dec_ref(v___x_887_);
lean_inc_ref(v___x_888_);
lean_inc_ref(v___x_886_);
v___x_889_ = l_Lean_Meta_mkEq(v___x_886_, v___x_888_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_891_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
lean_inc_ref(v___x_888_);
v___x_891_ = l_Lean_Meta_mkEq(v___x_888_, v___x_886_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v___x_893_ = lean_box(v___x_867_);
v___x_894_ = lean_box(v___x_868_);
v___x_895_ = lean_box(v___x_869_);
v___f_896_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__0___boxed), 26, 20);
lean_closure_set(v___f_896_, 0, v_motive_865_);
lean_closure_set(v___f_896_, 1, v___x_866_);
lean_closure_set(v___f_896_, 2, v_a_892_);
lean_closure_set(v___f_896_, 3, v_ism1_863_);
lean_closure_set(v___f_896_, 4, v___x_893_);
lean_closure_set(v___f_896_, 5, v___x_894_);
lean_closure_set(v___f_896_, 6, v___x_895_);
lean_closure_set(v___f_896_, 7, v___x_870_);
lean_closure_set(v___f_896_, 8, v_tail_861_);
lean_closure_set(v___f_896_, 9, v_params_862_);
lean_closure_set(v___f_896_, 10, v_alts_877_);
lean_closure_set(v___f_896_, 11, v_numParams_871_);
lean_closure_set(v___f_896_, 12, v_ism2_864_);
lean_closure_set(v___f_896_, 13, v_val_872_);
lean_closure_set(v___f_896_, 14, v_indName_860_);
lean_closure_set(v___f_896_, 15, v___x_873_);
lean_closure_set(v___f_896_, 16, v___x_874_);
lean_closure_set(v___f_896_, 17, v___x_888_);
lean_closure_set(v___f_896_, 18, v_name_875_);
lean_closure_set(v___f_896_, 19, v___x_876_);
v___x_897_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_898_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_897_, v_a_890_, v___f_896_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
return v___x_898_;
}
else
{
lean_dec(v_a_890_);
lean_dec_ref(v___x_888_);
lean_dec_ref(v_alts_877_);
lean_dec(v___x_876_);
lean_dec(v_name_875_);
lean_dec(v___x_874_);
lean_dec(v___x_873_);
lean_dec_ref(v_val_872_);
lean_dec(v_numParams_871_);
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_866_);
lean_dec_ref(v_motive_865_);
lean_dec_ref(v_ism2_864_);
lean_dec_ref(v_ism1_863_);
lean_dec_ref(v_params_862_);
lean_dec(v_tail_861_);
lean_dec(v_indName_860_);
return v___x_891_;
}
}
else
{
lean_dec_ref(v___x_888_);
lean_dec_ref(v___x_886_);
lean_dec_ref(v_alts_877_);
lean_dec(v___x_876_);
lean_dec(v_name_875_);
lean_dec(v___x_874_);
lean_dec(v___x_873_);
lean_dec_ref(v_val_872_);
lean_dec(v_numParams_871_);
lean_dec_ref(v___x_870_);
lean_dec_ref(v___x_866_);
lean_dec_ref(v_motive_865_);
lean_dec_ref(v_ism2_864_);
lean_dec_ref(v_ism1_863_);
lean_dec_ref(v_params_862_);
lean_dec(v_tail_861_);
lean_dec(v_indName_860_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object** _args){
lean_object* v_indName_899_ = _args[0];
lean_object* v_tail_900_ = _args[1];
lean_object* v_params_901_ = _args[2];
lean_object* v_ism1_902_ = _args[3];
lean_object* v_ism2_903_ = _args[4];
lean_object* v_motive_904_ = _args[5];
lean_object* v___x_905_ = _args[6];
lean_object* v___x_906_ = _args[7];
lean_object* v___x_907_ = _args[8];
lean_object* v___x_908_ = _args[9];
lean_object* v___x_909_ = _args[10];
lean_object* v_numParams_910_ = _args[11];
lean_object* v_val_911_ = _args[12];
lean_object* v___x_912_ = _args[13];
lean_object* v___x_913_ = _args[14];
lean_object* v_name_914_ = _args[15];
lean_object* v___x_915_ = _args[16];
lean_object* v_alts_916_ = _args[17];
lean_object* v___y_917_ = _args[18];
lean_object* v___y_918_ = _args[19];
lean_object* v___y_919_ = _args[20];
lean_object* v___y_920_ = _args[21];
lean_object* v___y_921_ = _args[22];
_start:
{
uint8_t v___x_21269__boxed_922_; uint8_t v___x_21270__boxed_923_; uint8_t v___x_21271__boxed_924_; lean_object* v_res_925_; 
v___x_21269__boxed_922_ = lean_unbox(v___x_906_);
v___x_21270__boxed_923_ = lean_unbox(v___x_907_);
v___x_21271__boxed_924_ = lean_unbox(v___x_908_);
v_res_925_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_899_, v_tail_900_, v_params_901_, v_ism1_902_, v_ism2_903_, v_motive_904_, v___x_905_, v___x_21269__boxed_922_, v___x_21270__boxed_923_, v___x_21271__boxed_924_, v___x_909_, v_numParams_910_, v_val_911_, v___x_912_, v___x_913_, v_name_914_, v___x_915_, v_alts_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_926_, lean_object* v_x_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v_snd_926_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_934_, lean_object* v_x_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_934_, v_x_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec_ref(v_x_935_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_942_, size_t v_i_943_, lean_object* v_bs_944_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_lt(v_i_943_, v_sz_942_);
if (v___x_945_ == 0)
{
return v_bs_944_;
}
else
{
lean_object* v_v_946_; lean_object* v_fst_947_; lean_object* v_snd_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_962_; 
v_v_946_ = lean_array_uget(v_bs_944_, v_i_943_);
v_fst_947_ = lean_ctor_get(v_v_946_, 0);
v_snd_948_ = lean_ctor_get(v_v_946_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_v_946_);
if (v_isSharedCheck_962_ == 0)
{
v___x_950_ = v_v_946_;
v_isShared_951_ = v_isSharedCheck_962_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_snd_948_);
lean_inc(v_fst_947_);
lean_dec(v_v_946_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_962_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v___x_952_; lean_object* v_bs_x27_953_; lean_object* v___f_954_; lean_object* v___x_956_; 
v___x_952_ = lean_unsigned_to_nat(0u);
v_bs_x27_953_ = lean_array_uset(v_bs_944_, v_i_943_, v___x_952_);
v___f_954_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_954_, 0, v_snd_948_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v___f_954_);
v___x_956_ = v___x_950_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_fst_947_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v___f_954_);
v___x_956_ = v_reuseFailAlloc_961_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
size_t v___x_957_; size_t v___x_958_; lean_object* v___x_959_; 
v___x_957_ = ((size_t)1ULL);
v___x_958_ = lean_usize_add(v_i_943_, v___x_957_);
v___x_959_ = lean_array_uset(v_bs_x27_953_, v_i_943_, v___x_956_);
v_i_943_ = v___x_958_;
v_bs_944_ = v___x_959_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_963_, lean_object* v_i_964_, lean_object* v_bs_965_){
_start:
{
size_t v_sz_boxed_966_; size_t v_i_boxed_967_; lean_object* v_res_968_; 
v_sz_boxed_966_ = lean_unbox_usize(v_sz_963_);
lean_dec(v_sz_963_);
v_i_boxed_967_ = lean_unbox_usize(v_i_964_);
lean_dec(v_i_964_);
v_res_968_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_966_, v_i_boxed_967_, v_bs_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object* v___x_969_, lean_object* v_a_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_20163__overap_977_; lean_object* v___x_978_; 
v___x_976_ = l_Lean_instInhabitedExpr;
v___x_20163__overap_977_ = l_instInhabitedOfMonad___redArg(v___x_969_, v___x_976_);
lean_inc(v___y_974_);
lean_inc_ref(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
v___x_978_ = lean_apply_5(v___x_20163__overap_977_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, lean_box(0));
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object* v___x_979_, lean_object* v_a_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_979_, v_a_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec_ref(v_a_980_);
return v_res_986_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_instMonadEIO(lean_box(0));
return v___x_987_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0);
v___x_989_ = l_StateRefT_x27_instMonad___redArg(v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object* v_acc_994_, lean_object* v_declInfos_995_, lean_object* v_k_996_, lean_object* v_kind_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
uint8_t v_kind_boxed_1004_; lean_object* v_res_1005_; 
v_kind_boxed_1004_ = lean_unbox(v_kind_997_);
v_res_1005_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_994_, v_declInfos_995_, v_k_996_, v_kind_boxed_1004_, v_x_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_declInfos_1006_, lean_object* v_k_1007_, uint8_t v_kind_1008_, lean_object* v_acc_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; lean_object* v_toApplicative_1016_; lean_object* v_toFunctor_1017_; lean_object* v_toSeq_1018_; lean_object* v_toSeqLeft_1019_; lean_object* v_toSeqRight_1020_; lean_object* v___f_1021_; lean_object* v___f_1022_; lean_object* v___f_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; lean_object* v___f_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_toApplicative_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1081_; 
v___x_1015_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_1016_ = lean_ctor_get(v___x_1015_, 0);
v_toFunctor_1017_ = lean_ctor_get(v_toApplicative_1016_, 0);
v_toSeq_1018_ = lean_ctor_get(v_toApplicative_1016_, 2);
v_toSeqLeft_1019_ = lean_ctor_get(v_toApplicative_1016_, 3);
v_toSeqRight_1020_ = lean_ctor_get(v_toApplicative_1016_, 4);
v___f_1021_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_1022_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_1017_, 2);
v___f_1023_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1023_, 0, v_toFunctor_1017_);
v___f_1024_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1024_, 0, v_toFunctor_1017_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___f_1023_);
lean_ctor_set(v___x_1025_, 1, v___f_1024_);
lean_inc(v_toSeqRight_1020_);
v___f_1026_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1026_, 0, v_toSeqRight_1020_);
lean_inc(v_toSeqLeft_1019_);
v___f_1027_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1027_, 0, v_toSeqLeft_1019_);
lean_inc(v_toSeq_1018_);
v___f_1028_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1028_, 0, v_toSeq_1018_);
v___x_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1025_);
lean_ctor_set(v___x_1029_, 1, v___f_1021_);
lean_ctor_set(v___x_1029_, 2, v___f_1028_);
lean_ctor_set(v___x_1029_, 3, v___f_1027_);
lean_ctor_set(v___x_1029_, 4, v___f_1026_);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___f_1022_);
v___x_1031_ = l_StateRefT_x27_instMonad___redArg(v___x_1030_);
v_toApplicative_1032_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v___x_1031_, 1);
lean_dec(v_unused_1082_);
v___x_1034_ = v___x_1031_;
v_isShared_1035_ = v_isSharedCheck_1081_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_toApplicative_1032_);
lean_dec(v___x_1031_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1081_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_toFunctor_1036_; lean_object* v_toSeq_1037_; lean_object* v_toSeqLeft_1038_; lean_object* v_toSeqRight_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1079_; 
v_toFunctor_1036_ = lean_ctor_get(v_toApplicative_1032_, 0);
v_toSeq_1037_ = lean_ctor_get(v_toApplicative_1032_, 2);
v_toSeqLeft_1038_ = lean_ctor_get(v_toApplicative_1032_, 3);
v_toSeqRight_1039_ = lean_ctor_get(v_toApplicative_1032_, 4);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_toApplicative_1032_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v_toApplicative_1032_, 1);
lean_dec(v_unused_1080_);
v___x_1041_ = v_toApplicative_1032_;
v_isShared_1042_ = v_isSharedCheck_1079_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_toSeqRight_1039_);
lean_inc(v_toSeqLeft_1038_);
lean_inc(v_toSeq_1037_);
lean_inc(v_toFunctor_1036_);
lean_dec(v_toApplicative_1032_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1079_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___f_1043_; lean_object* v___f_1044_; lean_object* v___f_1045_; lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___f_1048_; lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___x_1052_; 
v___f_1043_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_1044_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_1036_);
v___f_1045_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1045_, 0, v_toFunctor_1036_);
v___f_1046_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1046_, 0, v_toFunctor_1036_);
v___x_1047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___f_1045_);
lean_ctor_set(v___x_1047_, 1, v___f_1046_);
v___f_1048_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1048_, 0, v_toSeqRight_1039_);
v___f_1049_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1049_, 0, v_toSeqLeft_1038_);
v___f_1050_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1050_, 0, v_toSeq_1037_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 4, v___f_1048_);
lean_ctor_set(v___x_1041_, 3, v___f_1049_);
lean_ctor_set(v___x_1041_, 2, v___f_1050_);
lean_ctor_set(v___x_1041_, 1, v___f_1043_);
lean_ctor_set(v___x_1041_, 0, v___x_1047_);
v___x_1052_ = v___x_1041_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v___f_1043_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v___f_1050_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v___f_1049_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v___f_1048_);
v___x_1052_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
lean_object* v___x_1054_; 
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v___f_1044_);
lean_ctor_set(v___x_1034_, 0, v___x_1052_);
v___x_1054_ = v___x_1034_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1052_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v___f_1044_);
v___x_1054_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v___x_1055_ = lean_array_get_size(v_acc_1009_);
v___x_1056_ = lean_array_get_size(v_declInfos_1006_);
v___x_1057_ = lean_nat_dec_lt(v___x_1055_, v___x_1056_);
if (v___x_1057_ == 0)
{
lean_object* v___x_1058_; 
lean_dec_ref(v___x_1054_);
lean_dec_ref(v_declInfos_1006_);
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
v___x_1058_ = lean_apply_6(v_k_1007_, v_acc_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, lean_box(0));
return v___x_1058_;
}
else
{
lean_object* v___f_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v_snd_1067_; lean_object* v_fst_1068_; lean_object* v_fst_1069_; lean_object* v_snd_1070_; lean_object* v___x_1071_; 
v___f_1059_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1059_, 0, v___x_1054_);
v___x_1060_ = lean_box(0);
v___x_1061_ = 0;
v___f_1062_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1062_, 0, v___f_1059_);
v___x_1063_ = lean_box(v___x_1061_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v___f_1062_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1060_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_array_get(v___x_1065_, v_declInfos_1006_, v___x_1055_);
lean_dec_ref_known(v___x_1065_, 2);
v_snd_1067_ = lean_ctor_get(v___x_1066_, 1);
lean_inc(v_snd_1067_);
v_fst_1068_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_fst_1068_);
lean_dec(v___x_1066_);
v_fst_1069_ = lean_ctor_get(v_snd_1067_, 0);
lean_inc(v_fst_1069_);
v_snd_1070_ = lean_ctor_get(v_snd_1067_, 1);
lean_inc(v_snd_1070_);
lean_dec(v_snd_1067_);
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
lean_inc_ref(v_acc_1009_);
v___x_1071_ = lean_apply_6(v_snd_1070_, v_acc_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, lean_box(0));
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___f_1074_; uint8_t v___x_1075_; lean_object* v___x_1076_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = lean_box(v_kind_1008_);
v___f_1074_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1074_, 0, v_acc_1009_);
lean_closure_set(v___f_1074_, 1, v_declInfos_1006_);
lean_closure_set(v___f_1074_, 2, v_k_1007_);
lean_closure_set(v___f_1074_, 3, v___x_1073_);
v___x_1075_ = lean_unbox(v_fst_1069_);
lean_dec(v_fst_1069_);
v___x_1076_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1068_, v___x_1075_, v_a_1072_, v___f_1074_, v_kind_1008_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1076_;
}
else
{
lean_dec(v_fst_1069_);
lean_dec(v_fst_1068_);
lean_dec_ref(v_acc_1009_);
lean_dec_ref(v_k_1007_);
lean_dec_ref(v_declInfos_1006_);
return v___x_1071_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(lean_object* v_acc_1083_, lean_object* v_declInfos_1084_, lean_object* v_k_1085_, uint8_t v_kind_1086_, lean_object* v_x_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_array_push(v_acc_1083_, v_x_1087_);
v___x_1094_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1084_, v_k_1085_, v_kind_1086_, v___x_1093_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object* v_declInfos_1095_, lean_object* v_k_1096_, lean_object* v_kind_1097_, lean_object* v_acc_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
uint8_t v_kind_boxed_1104_; lean_object* v_res_1105_; 
v_kind_boxed_1104_ = lean_unbox(v_kind_1097_);
v_res_1105_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1095_, v_k_1096_, v_kind_boxed_1104_, v_acc_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object* v_declInfos_1108_, lean_object* v_k_1109_, uint8_t v_kind_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_1117_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1108_, v_k_1109_, v_kind_1110_, v___x_1116_, v___y_1111_, v___y_1112_, v___y_1113_, v___y_1114_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object* v_declInfos_1118_, lean_object* v_k_1119_, lean_object* v_kind_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
uint8_t v_kind_boxed_1126_; lean_object* v_res_1127_; 
v_kind_boxed_1126_ = lean_unbox(v_kind_1120_);
v_res_1127_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_declInfos_1118_, v_k_1119_, v_kind_boxed_1126_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t v_sz_1128_, size_t v_i_1129_, lean_object* v_bs_1130_){
_start:
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_usize_dec_lt(v_i_1129_, v_sz_1128_);
if (v___x_1131_ == 0)
{
return v_bs_1130_;
}
else
{
lean_object* v_v_1132_; lean_object* v_fst_1133_; lean_object* v_snd_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1150_; 
v_v_1132_ = lean_array_uget(v_bs_1130_, v_i_1129_);
v_fst_1133_ = lean_ctor_get(v_v_1132_, 0);
v_snd_1134_ = lean_ctor_get(v_v_1132_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_v_1132_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1136_ = v_v_1132_;
v_isShared_1137_ = v_isSharedCheck_1150_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_snd_1134_);
lean_inc(v_fst_1133_);
lean_dec(v_v_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1150_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v_bs_x27_1139_; uint8_t v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v_bs_x27_1139_ = lean_array_uset(v_bs_1130_, v_i_1129_, v___x_1138_);
v___x_1140_ = 0;
v___x_1141_ = lean_box(v___x_1140_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1141_);
v___x_1143_ = v___x_1136_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_snd_1134_);
v___x_1143_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
lean_object* v___x_1144_; size_t v___x_1145_; size_t v___x_1146_; lean_object* v___x_1147_; 
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_fst_1133_);
lean_ctor_set(v___x_1144_, 1, v___x_1143_);
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_add(v_i_1129_, v___x_1145_);
v___x_1147_ = lean_array_uset(v_bs_x27_1139_, v_i_1129_, v___x_1144_);
v_i_1129_ = v___x_1146_;
v_bs_1130_ = v___x_1147_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_sz_1151_, lean_object* v_i_1152_, lean_object* v_bs_1153_){
_start:
{
size_t v_sz_boxed_1154_; size_t v_i_boxed_1155_; lean_object* v_res_1156_; 
v_sz_boxed_1154_ = lean_unbox_usize(v_sz_1151_);
lean_dec(v_sz_1151_);
v_i_boxed_1155_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_res_1156_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_1154_, v_i_boxed_1155_, v_bs_1153_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_declInfos_1157_, lean_object* v_k_1158_, uint8_t v_kind_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
size_t v_sz_1165_; size_t v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_sz_1165_ = lean_array_size(v_declInfos_1157_);
v___x_1166_ = ((size_t)0ULL);
v___x_1167_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1165_, v___x_1166_, v_declInfos_1157_);
v___x_1168_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v___x_1167_, v_k_1158_, v_kind_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_declInfos_1169_, lean_object* v_k_1170_, lean_object* v_kind_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
uint8_t v_kind_boxed_1177_; lean_object* v_res_1178_; 
v_kind_boxed_1177_ = lean_unbox(v_kind_1171_);
v_res_1178_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1169_, v_k_1170_, v_kind_boxed_1177_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_declInfos_1179_, lean_object* v_k_1180_, uint8_t v_kind_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_){
_start:
{
size_t v_sz_1187_; size_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v_sz_1187_ = lean_array_size(v_declInfos_1179_);
v___x_1188_ = ((size_t)0ULL);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1187_, v___x_1188_, v_declInfos_1179_);
v___x_1190_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_1189_, v_k_1180_, v_kind_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_declInfos_1191_, lean_object* v_k_1192_, lean_object* v_kind_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
uint8_t v_kind_boxed_1199_; lean_object* v_res_1200_; 
v_kind_boxed_1199_ = lean_unbox(v_kind_1193_);
v_res_1200_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1191_, v_k_1192_, v_kind_boxed_1199_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_1202_, lean_object* v_dummy_1203_, lean_object* v___x_1204_, lean_object* v___x_1205_, lean_object* v___x_1206_, lean_object* v_motive_1207_, lean_object* v_zs1_1208_, uint8_t v___x_1209_, uint8_t v___x_1210_, uint8_t v___x_1211_, lean_object* v_v_1212_, lean_object* v___x_1213_, lean_object* v_zs2_1214_, lean_object* v_ctorRet2_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
lean_inc(v___y_1219_);
lean_inc_ref(v___y_1218_);
lean_inc(v___y_1217_);
lean_inc_ref(v___y_1216_);
v___x_1221_ = lean_whnf(v_ctorRet2_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
if (lean_obj_tag(v___x_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1223_; lean_object* v_nargs_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_a_1222_ = lean_ctor_get(v___x_1221_, 0);
lean_inc(v_a_1222_);
lean_dec_ref_known(v___x_1221_, 1);
v___x_1223_ = l_Lean_mkAppN(v___x_1202_, v_zs2_1214_);
v_nargs_1224_ = l_Lean_Expr_getAppNumArgs(v_a_1222_);
lean_inc(v_nargs_1224_);
v___x_1225_ = lean_mk_array(v_nargs_1224_, v_dummy_1203_);
v___x_1226_ = lean_nat_sub(v_nargs_1224_, v___x_1204_);
lean_dec(v_nargs_1224_);
v___x_1227_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1222_, v___x_1225_, v___x_1226_);
v___x_1228_ = lean_array_get_size(v___x_1227_);
v___x_1229_ = l_Array_toSubarray___redArg(v___x_1227_, v___x_1205_, v___x_1228_);
v___x_1230_ = l_Subarray_copy___redArg(v___x_1229_);
v___x_1231_ = lean_array_push(v___x_1230_, v___x_1223_);
v___x_1232_ = l_Array_append___redArg(v___x_1206_, v___x_1231_);
lean_dec_ref(v___x_1231_);
v___x_1233_ = l_Lean_mkAppN(v_motive_1207_, v___x_1232_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = l_Array_append___redArg(v_zs1_1208_, v_zs2_1214_);
v___x_1235_ = l_Lean_Meta_mkForallFVars(v___x_1234_, v___x_1233_, v___x_1209_, v___x_1210_, v___x_1210_, v___x_1211_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec_ref(v___x_1234_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1255_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1255_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1255_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___y_1241_; 
if (lean_obj_tag(v_v_1212_) == 1)
{
lean_object* v_str_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_str_1246_ = lean_ctor_get(v_v_1212_, 1);
lean_inc_ref(v_str_1246_);
lean_dec_ref_known(v_v_1212_, 2);
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Lean_Name_str___override(v___x_1247_, v_str_1246_);
v___y_1241_ = v___x_1248_;
goto v___jp_1240_;
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec(v_v_1212_);
v___x_1249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_1250_ = lean_nat_add(v___x_1213_, v___x_1204_);
v___x_1251_ = l_Nat_reprFast(v___x_1250_);
v___x_1252_ = lean_string_append(v___x_1249_, v___x_1251_);
lean_dec_ref(v___x_1251_);
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Lean_Name_str___override(v___x_1253_, v___x_1252_);
v___y_1241_ = v___x_1254_;
goto v___jp_1240_;
}
v___jp_1240_:
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___y_1241_);
lean_ctor_set(v___x_1242_, 1, v_a_1236_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1242_);
v___x_1244_ = v___x_1238_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec(v_v_1212_);
v_a_1256_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1235_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1235_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_v_1212_);
lean_dec_ref(v_zs1_1208_);
lean_dec_ref(v_motive_1207_);
lean_dec_ref(v___x_1206_);
lean_dec(v___x_1205_);
lean_dec_ref(v_dummy_1203_);
lean_dec_ref(v___x_1202_);
v_a_1264_ = lean_ctor_get(v___x_1221_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1221_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1221_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1272_ = _args[0];
lean_object* v_dummy_1273_ = _args[1];
lean_object* v___x_1274_ = _args[2];
lean_object* v___x_1275_ = _args[3];
lean_object* v___x_1276_ = _args[4];
lean_object* v_motive_1277_ = _args[5];
lean_object* v_zs1_1278_ = _args[6];
lean_object* v___x_1279_ = _args[7];
lean_object* v___x_1280_ = _args[8];
lean_object* v___x_1281_ = _args[9];
lean_object* v_v_1282_ = _args[10];
lean_object* v___x_1283_ = _args[11];
lean_object* v_zs2_1284_ = _args[12];
lean_object* v_ctorRet2_1285_ = _args[13];
lean_object* v___y_1286_ = _args[14];
lean_object* v___y_1287_ = _args[15];
lean_object* v___y_1288_ = _args[16];
lean_object* v___y_1289_ = _args[17];
lean_object* v___y_1290_ = _args[18];
_start:
{
uint8_t v___x_21705__boxed_1291_; uint8_t v___x_21706__boxed_1292_; uint8_t v___x_21707__boxed_1293_; lean_object* v_res_1294_; 
v___x_21705__boxed_1291_ = lean_unbox(v___x_1279_);
v___x_21706__boxed_1292_ = lean_unbox(v___x_1280_);
v___x_21707__boxed_1293_ = lean_unbox(v___x_1281_);
v_res_1294_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1272_, v_dummy_1273_, v___x_1274_, v___x_1275_, v___x_1276_, v_motive_1277_, v_zs1_1278_, v___x_21705__boxed_1291_, v___x_21706__boxed_1292_, v___x_21707__boxed_1293_, v_v_1282_, v___x_1283_, v_zs2_1284_, v_ctorRet2_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec_ref(v_zs2_1284_);
lean_dec(v___x_1283_);
lean_dec(v___x_1274_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1295_, lean_object* v___x_1296_, lean_object* v___x_1297_, lean_object* v_motive_1298_, uint8_t v___x_1299_, uint8_t v___x_1300_, uint8_t v___x_1301_, lean_object* v_v_1302_, lean_object* v___x_1303_, lean_object* v_a_1304_, lean_object* v_zs1_1305_, lean_object* v_ctorRet1_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; 
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
v___x_1312_ = lean_whnf(v_ctorRet1_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v_dummy_1315_; lean_object* v_nargs_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___f_1327_; lean_object* v___x_1328_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
lean_inc_ref(v___x_1295_);
v___x_1314_ = l_Lean_mkAppN(v___x_1295_, v_zs1_1305_);
v_dummy_1315_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1316_ = l_Lean_Expr_getAppNumArgs(v_a_1313_);
lean_inc(v_nargs_1316_);
v___x_1317_ = lean_mk_array(v_nargs_1316_, v_dummy_1315_);
v___x_1318_ = lean_nat_sub(v_nargs_1316_, v___x_1296_);
lean_dec(v_nargs_1316_);
v___x_1319_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1313_, v___x_1317_, v___x_1318_);
v___x_1320_ = lean_array_get_size(v___x_1319_);
lean_inc(v___x_1297_);
v___x_1321_ = l_Array_toSubarray___redArg(v___x_1319_, v___x_1297_, v___x_1320_);
v___x_1322_ = l_Subarray_copy___redArg(v___x_1321_);
v___x_1323_ = lean_array_push(v___x_1322_, v___x_1314_);
v___x_1324_ = lean_box(v___x_1299_);
v___x_1325_ = lean_box(v___x_1300_);
v___x_1326_ = lean_box(v___x_1301_);
v___f_1327_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1327_, 0, v___x_1295_);
lean_closure_set(v___f_1327_, 1, v_dummy_1315_);
lean_closure_set(v___f_1327_, 2, v___x_1296_);
lean_closure_set(v___f_1327_, 3, v___x_1297_);
lean_closure_set(v___f_1327_, 4, v___x_1323_);
lean_closure_set(v___f_1327_, 5, v_motive_1298_);
lean_closure_set(v___f_1327_, 6, v_zs1_1305_);
lean_closure_set(v___f_1327_, 7, v___x_1324_);
lean_closure_set(v___f_1327_, 8, v___x_1325_);
lean_closure_set(v___f_1327_, 9, v___x_1326_);
lean_closure_set(v___f_1327_, 10, v_v_1302_);
lean_closure_set(v___f_1327_, 11, v___x_1303_);
v___x_1328_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1304_, v___f_1327_, v___x_1299_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1328_;
}
else
{
lean_object* v_a_1329_; lean_object* v___x_1331_; uint8_t v_isShared_1332_; uint8_t v_isSharedCheck_1336_; 
lean_dec_ref(v_zs1_1305_);
lean_dec_ref(v_a_1304_);
lean_dec(v___x_1303_);
lean_dec(v_v_1302_);
lean_dec_ref(v_motive_1298_);
lean_dec(v___x_1297_);
lean_dec(v___x_1296_);
lean_dec_ref(v___x_1295_);
v_a_1329_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1331_ = v___x_1312_;
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
else
{
lean_inc(v_a_1329_);
lean_dec(v___x_1312_);
v___x_1331_ = lean_box(0);
v_isShared_1332_ = v_isSharedCheck_1336_;
goto v_resetjp_1330_;
}
v_resetjp_1330_:
{
lean_object* v___x_1334_; 
if (v_isShared_1332_ == 0)
{
v___x_1334_ = v___x_1331_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1337_ = _args[0];
lean_object* v___x_1338_ = _args[1];
lean_object* v___x_1339_ = _args[2];
lean_object* v_motive_1340_ = _args[3];
lean_object* v___x_1341_ = _args[4];
lean_object* v___x_1342_ = _args[5];
lean_object* v___x_1343_ = _args[6];
lean_object* v_v_1344_ = _args[7];
lean_object* v___x_1345_ = _args[8];
lean_object* v_a_1346_ = _args[9];
lean_object* v_zs1_1347_ = _args[10];
lean_object* v_ctorRet1_1348_ = _args[11];
lean_object* v___y_1349_ = _args[12];
lean_object* v___y_1350_ = _args[13];
lean_object* v___y_1351_ = _args[14];
lean_object* v___y_1352_ = _args[15];
lean_object* v___y_1353_ = _args[16];
_start:
{
uint8_t v___x_21846__boxed_1354_; uint8_t v___x_21847__boxed_1355_; uint8_t v___x_21848__boxed_1356_; lean_object* v_res_1357_; 
v___x_21846__boxed_1354_ = lean_unbox(v___x_1341_);
v___x_21847__boxed_1355_ = lean_unbox(v___x_1342_);
v___x_21848__boxed_1356_ = lean_unbox(v___x_1343_);
v_res_1357_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1337_, v___x_1338_, v___x_1339_, v_motive_1340_, v___x_21846__boxed_1354_, v___x_21847__boxed_1355_, v___x_21848__boxed_1356_, v_v_1344_, v___x_1345_, v_a_1346_, v_zs1_1347_, v_ctorRet1_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v___y_1349_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1358_, lean_object* v_params_1359_, lean_object* v___x_1360_, lean_object* v_motive_1361_, size_t v_sz_1362_, size_t v_i_1363_, lean_object* v_bs_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_usize_dec_lt(v_i_1363_, v_sz_1362_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; 
lean_dec_ref(v_motive_1361_);
lean_dec(v___x_1360_);
lean_dec(v_tail_1358_);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_bs_1364_);
return v___x_1371_;
}
else
{
lean_object* v_v_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v_v_1372_ = lean_array_uget(v_bs_1364_, v_i_1363_);
lean_inc(v_tail_1358_);
lean_inc(v_v_1372_);
v___x_1373_ = l_Lean_mkConst(v_v_1372_, v_tail_1358_);
v___x_1374_ = l_Lean_mkAppN(v___x_1373_, v_params_1359_);
lean_inc(v___y_1368_);
lean_inc_ref(v___y_1367_);
lean_inc(v___y_1366_);
lean_inc_ref(v___y_1365_);
lean_inc_ref(v___x_1374_);
v___x_1375_ = lean_infer_type(v___x_1374_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1377_; lean_object* v_bs_x27_1378_; uint8_t v___x_1379_; uint8_t v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___f_1386_; lean_object* v___x_1387_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc_n(v_a_1376_, 2);
lean_dec_ref_known(v___x_1375_, 1);
v___x_1377_ = lean_unsigned_to_nat(0u);
v_bs_x27_1378_ = lean_array_uset(v_bs_1364_, v_i_1363_, v___x_1377_);
v___x_1379_ = 0;
v___x_1380_ = 1;
v___x_1381_ = lean_unsigned_to_nat(1u);
v___x_1382_ = lean_usize_to_nat(v_i_1363_);
v___x_1383_ = lean_box(v___x_1379_);
v___x_1384_ = lean_box(v___x_1370_);
v___x_1385_ = lean_box(v___x_1380_);
lean_inc_ref(v_motive_1361_);
lean_inc(v___x_1360_);
v___f_1386_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1386_, 0, v___x_1374_);
lean_closure_set(v___f_1386_, 1, v___x_1381_);
lean_closure_set(v___f_1386_, 2, v___x_1360_);
lean_closure_set(v___f_1386_, 3, v_motive_1361_);
lean_closure_set(v___f_1386_, 4, v___x_1383_);
lean_closure_set(v___f_1386_, 5, v___x_1384_);
lean_closure_set(v___f_1386_, 6, v___x_1385_);
lean_closure_set(v___f_1386_, 7, v_v_1372_);
lean_closure_set(v___f_1386_, 8, v___x_1382_);
lean_closure_set(v___f_1386_, 9, v_a_1376_);
v___x_1387_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1376_, v___f_1386_, v___x_1379_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; size_t v___x_1389_; size_t v___x_1390_; lean_object* v___x_1391_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1387_, 1);
v___x_1389_ = ((size_t)1ULL);
v___x_1390_ = lean_usize_add(v_i_1363_, v___x_1389_);
v___x_1391_ = lean_array_uset(v_bs_x27_1378_, v_i_1363_, v_a_1388_);
v_i_1363_ = v___x_1390_;
v_bs_1364_ = v___x_1391_;
goto _start;
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
lean_dec_ref(v_bs_x27_1378_);
lean_dec_ref(v_motive_1361_);
lean_dec(v___x_1360_);
lean_dec(v_tail_1358_);
v_a_1393_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1395_ = v___x_1387_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1387_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_a_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v___x_1374_);
lean_dec(v_v_1372_);
lean_dec_ref(v_bs_1364_);
lean_dec_ref(v_motive_1361_);
lean_dec(v___x_1360_);
lean_dec(v_tail_1358_);
v_a_1401_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1375_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1375_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1406_; 
if (v_isShared_1404_ == 0)
{
v___x_1406_ = v___x_1403_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_a_1401_);
v___x_1406_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
return v___x_1406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1409_, lean_object* v_params_1410_, lean_object* v___x_1411_, lean_object* v_motive_1412_, lean_object* v_sz_1413_, lean_object* v_i_1414_, lean_object* v_bs_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
size_t v_sz_boxed_1421_; size_t v_i_boxed_1422_; lean_object* v_res_1423_; 
v_sz_boxed_1421_ = lean_unbox_usize(v_sz_1413_);
lean_dec(v_sz_1413_);
v_i_boxed_1422_ = lean_unbox_usize(v_i_1414_);
lean_dec(v_i_1414_);
v_res_1423_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1409_, v_params_1410_, v___x_1411_, v_motive_1412_, v_sz_boxed_1421_, v_i_boxed_1422_, v_bs_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec_ref(v_params_1410_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1424_, lean_object* v_tail_1425_, lean_object* v_params_1426_, lean_object* v_numParams_1427_, lean_object* v_indName_1428_, lean_object* v_ism1_1429_, lean_object* v_ism2_1430_, lean_object* v___x_1431_, uint8_t v___x_1432_, uint8_t v___x_1433_, uint8_t v___x_1434_, lean_object* v_val_1435_, lean_object* v___x_1436_, lean_object* v___x_1437_, lean_object* v_name_1438_, lean_object* v___x_1439_, lean_object* v_motive_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v___x_1446_; size_t v_sz_1447_; size_t v___x_1448_; lean_object* v___x_1449_; 
v___x_1446_ = lean_array_mk(v_ctors_1424_);
v_sz_1447_ = lean_array_size(v___x_1446_);
v___x_1448_ = ((size_t)0ULL);
lean_inc_ref(v___x_1446_);
lean_inc_ref(v_motive_1440_);
lean_inc(v_numParams_1427_);
lean_inc(v_tail_1425_);
v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1425_, v_params_1426_, v_numParams_1427_, v_motive_1440_, v_sz_1447_, v___x_1448_, v___x_1446_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v_a_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___f_1454_; uint8_t v___x_1455_; lean_object* v___x_1456_; 
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref_known(v___x_1449_, 1);
v___x_1451_ = lean_box(v___x_1432_);
v___x_1452_ = lean_box(v___x_1433_);
v___x_1453_ = lean_box(v___x_1434_);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1454_, 0, v_indName_1428_);
lean_closure_set(v___f_1454_, 1, v_tail_1425_);
lean_closure_set(v___f_1454_, 2, v_params_1426_);
lean_closure_set(v___f_1454_, 3, v_ism1_1429_);
lean_closure_set(v___f_1454_, 4, v_ism2_1430_);
lean_closure_set(v___f_1454_, 5, v_motive_1440_);
lean_closure_set(v___f_1454_, 6, v___x_1431_);
lean_closure_set(v___f_1454_, 7, v___x_1451_);
lean_closure_set(v___f_1454_, 8, v___x_1452_);
lean_closure_set(v___f_1454_, 9, v___x_1453_);
lean_closure_set(v___f_1454_, 10, v___x_1446_);
lean_closure_set(v___f_1454_, 11, v_numParams_1427_);
lean_closure_set(v___f_1454_, 12, v_val_1435_);
lean_closure_set(v___f_1454_, 13, v___x_1436_);
lean_closure_set(v___f_1454_, 14, v___x_1437_);
lean_closure_set(v___f_1454_, 15, v_name_1438_);
lean_closure_set(v___f_1454_, 16, v___x_1439_);
v___x_1455_ = 0;
v___x_1456_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_a_1450_, v___f_1454_, v___x_1455_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_);
return v___x_1456_;
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_dec_ref(v___x_1446_);
lean_dec_ref(v_motive_1440_);
lean_dec(v___x_1439_);
lean_dec(v_name_1438_);
lean_dec(v___x_1437_);
lean_dec(v___x_1436_);
lean_dec_ref(v_val_1435_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_ism2_1430_);
lean_dec_ref(v_ism1_1429_);
lean_dec(v_indName_1428_);
lean_dec(v_numParams_1427_);
lean_dec_ref(v_params_1426_);
lean_dec(v_tail_1425_);
v_a_1457_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1449_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1449_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1465_ = _args[0];
lean_object* v_tail_1466_ = _args[1];
lean_object* v_params_1467_ = _args[2];
lean_object* v_numParams_1468_ = _args[3];
lean_object* v_indName_1469_ = _args[4];
lean_object* v_ism1_1470_ = _args[5];
lean_object* v_ism2_1471_ = _args[6];
lean_object* v___x_1472_ = _args[7];
lean_object* v___x_1473_ = _args[8];
lean_object* v___x_1474_ = _args[9];
lean_object* v___x_1475_ = _args[10];
lean_object* v_val_1476_ = _args[11];
lean_object* v___x_1477_ = _args[12];
lean_object* v___x_1478_ = _args[13];
lean_object* v_name_1479_ = _args[14];
lean_object* v___x_1480_ = _args[15];
lean_object* v_motive_1481_ = _args[16];
lean_object* v___y_1482_ = _args[17];
lean_object* v___y_1483_ = _args[18];
lean_object* v___y_1484_ = _args[19];
lean_object* v___y_1485_ = _args[20];
lean_object* v___y_1486_ = _args[21];
_start:
{
uint8_t v___x_22026__boxed_1487_; uint8_t v___x_22027__boxed_1488_; uint8_t v___x_22028__boxed_1489_; lean_object* v_res_1490_; 
v___x_22026__boxed_1487_ = lean_unbox(v___x_1473_);
v___x_22027__boxed_1488_ = lean_unbox(v___x_1474_);
v___x_22028__boxed_1489_ = lean_unbox(v___x_1475_);
v_res_1490_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1465_, v_tail_1466_, v_params_1467_, v_numParams_1468_, v_indName_1469_, v_ism1_1470_, v_ism2_1471_, v___x_1472_, v___x_22026__boxed_1487_, v___x_22027__boxed_1488_, v___x_22028__boxed_1489_, v_val_1476_, v___x_1477_, v___x_1478_, v_name_1479_, v___x_1480_, v_motive_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
lean_dec_ref(v___y_1484_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1494_, lean_object* v_head_1495_, lean_object* v_ctors_1496_, lean_object* v_tail_1497_, lean_object* v_params_1498_, lean_object* v_numParams_1499_, lean_object* v_indName_1500_, lean_object* v_val_1501_, lean_object* v___x_1502_, lean_object* v___x_1503_, lean_object* v_name_1504_, lean_object* v___x_1505_, lean_object* v_ism2_1506_, lean_object* v_x_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; uint8_t v___x_1515_; uint8_t v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; 
lean_inc_ref(v_ism1_1494_);
v___x_1513_ = l_Array_append___redArg(v_ism1_1494_, v_ism2_1506_);
v___x_1514_ = l_Lean_mkSort(v_head_1495_);
v___x_1515_ = 0;
v___x_1516_ = 1;
v___x_1517_ = 1;
v___x_1518_ = l_Lean_Meta_mkForallFVars(v___x_1513_, v___x_1514_, v___x_1515_, v___x_1516_, v___x_1516_, v___x_1517_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___x_1520_ = lean_box(v___x_1515_);
v___x_1521_ = lean_box(v___x_1516_);
v___x_1522_ = lean_box(v___x_1517_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 22, 16);
lean_closure_set(v___f_1523_, 0, v_ctors_1496_);
lean_closure_set(v___f_1523_, 1, v_tail_1497_);
lean_closure_set(v___f_1523_, 2, v_params_1498_);
lean_closure_set(v___f_1523_, 3, v_numParams_1499_);
lean_closure_set(v___f_1523_, 4, v_indName_1500_);
lean_closure_set(v___f_1523_, 5, v_ism1_1494_);
lean_closure_set(v___f_1523_, 6, v_ism2_1506_);
lean_closure_set(v___f_1523_, 7, v___x_1513_);
lean_closure_set(v___f_1523_, 8, v___x_1520_);
lean_closure_set(v___f_1523_, 9, v___x_1521_);
lean_closure_set(v___f_1523_, 10, v___x_1522_);
lean_closure_set(v___f_1523_, 11, v_val_1501_);
lean_closure_set(v___f_1523_, 12, v___x_1502_);
lean_closure_set(v___f_1523_, 13, v___x_1503_);
lean_closure_set(v___f_1523_, 14, v_name_1504_);
lean_closure_set(v___f_1523_, 15, v___x_1505_);
v___x_1524_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1525_ = 0;
v___x_1526_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1524_, v___x_1517_, v_a_1519_, v___f_1523_, v___x_1525_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
return v___x_1526_;
}
else
{
lean_dec_ref(v___x_1513_);
lean_dec_ref(v_ism2_1506_);
lean_dec(v___x_1505_);
lean_dec(v_name_1504_);
lean_dec(v___x_1503_);
lean_dec(v___x_1502_);
lean_dec_ref(v_val_1501_);
lean_dec(v_indName_1500_);
lean_dec(v_numParams_1499_);
lean_dec_ref(v_params_1498_);
lean_dec(v_tail_1497_);
lean_dec(v_ctors_1496_);
lean_dec_ref(v_ism1_1494_);
return v___x_1518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1527_ = _args[0];
lean_object* v_head_1528_ = _args[1];
lean_object* v_ctors_1529_ = _args[2];
lean_object* v_tail_1530_ = _args[3];
lean_object* v_params_1531_ = _args[4];
lean_object* v_numParams_1532_ = _args[5];
lean_object* v_indName_1533_ = _args[6];
lean_object* v_val_1534_ = _args[7];
lean_object* v___x_1535_ = _args[8];
lean_object* v___x_1536_ = _args[9];
lean_object* v_name_1537_ = _args[10];
lean_object* v___x_1538_ = _args[11];
lean_object* v_ism2_1539_ = _args[12];
lean_object* v_x_1540_ = _args[13];
lean_object* v___y_1541_ = _args[14];
lean_object* v___y_1542_ = _args[15];
lean_object* v___y_1543_ = _args[16];
lean_object* v___y_1544_ = _args[17];
lean_object* v___y_1545_ = _args[18];
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1527_, v_head_1528_, v_ctors_1529_, v_tail_1530_, v_params_1531_, v_numParams_1532_, v_indName_1533_, v_val_1534_, v___x_1535_, v___x_1536_, v_name_1537_, v___x_1538_, v_ism2_1539_, v_x_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec_ref(v_x_1540_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1547_, lean_object* v_ctors_1548_, lean_object* v_tail_1549_, lean_object* v_params_1550_, lean_object* v_numParams_1551_, lean_object* v_indName_1552_, lean_object* v_val_1553_, lean_object* v___x_1554_, lean_object* v___x_1555_, lean_object* v_name_1556_, lean_object* v___x_1557_, lean_object* v_t_1558_, lean_object* v___x_1559_, lean_object* v_ism1_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___f_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; 
v___f_1567_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 19, 12);
lean_closure_set(v___f_1567_, 0, v_ism1_1560_);
lean_closure_set(v___f_1567_, 1, v_head_1547_);
lean_closure_set(v___f_1567_, 2, v_ctors_1548_);
lean_closure_set(v___f_1567_, 3, v_tail_1549_);
lean_closure_set(v___f_1567_, 4, v_params_1550_);
lean_closure_set(v___f_1567_, 5, v_numParams_1551_);
lean_closure_set(v___f_1567_, 6, v_indName_1552_);
lean_closure_set(v___f_1567_, 7, v_val_1553_);
lean_closure_set(v___f_1567_, 8, v___x_1554_);
lean_closure_set(v___f_1567_, 9, v___x_1555_);
lean_closure_set(v___f_1567_, 10, v_name_1556_);
lean_closure_set(v___f_1567_, 11, v___x_1557_);
v___x_1568_ = 0;
v___x_1569_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1558_, v___x_1559_, v___f_1567_, v___x_1568_, v___x_1568_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1570_ = _args[0];
lean_object* v_ctors_1571_ = _args[1];
lean_object* v_tail_1572_ = _args[2];
lean_object* v_params_1573_ = _args[3];
lean_object* v_numParams_1574_ = _args[4];
lean_object* v_indName_1575_ = _args[5];
lean_object* v_val_1576_ = _args[6];
lean_object* v___x_1577_ = _args[7];
lean_object* v___x_1578_ = _args[8];
lean_object* v_name_1579_ = _args[9];
lean_object* v___x_1580_ = _args[10];
lean_object* v_t_1581_ = _args[11];
lean_object* v___x_1582_ = _args[12];
lean_object* v_ism1_1583_ = _args[13];
lean_object* v_x_1584_ = _args[14];
lean_object* v___y_1585_ = _args[15];
lean_object* v___y_1586_ = _args[16];
lean_object* v___y_1587_ = _args[17];
lean_object* v___y_1588_ = _args[18];
lean_object* v___y_1589_ = _args[19];
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1570_, v_ctors_1571_, v_tail_1572_, v_params_1573_, v_numParams_1574_, v_indName_1575_, v_val_1576_, v___x_1577_, v___x_1578_, v_name_1579_, v___x_1580_, v_t_1581_, v___x_1582_, v_ism1_1583_, v_x_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v___y_1585_);
lean_dec_ref(v_x_1584_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1591_, lean_object* v___x_1592_, lean_object* v_head_1593_, lean_object* v_ctors_1594_, lean_object* v_tail_1595_, lean_object* v_params_1596_, lean_object* v_numParams_1597_, lean_object* v_indName_1598_, lean_object* v_val_1599_, lean_object* v___x_1600_, lean_object* v___x_1601_, lean_object* v_name_1602_, lean_object* v_x_1603_, lean_object* v_t_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___f_1612_; uint8_t v___x_1613_; lean_object* v___x_1614_; 
v___x_1610_ = lean_nat_add(v_numIndices_1591_, v___x_1592_);
v___x_1611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1610_);
lean_inc_ref(v___x_1611_);
lean_inc_ref(v_t_1604_);
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 20, 13);
lean_closure_set(v___f_1612_, 0, v_head_1593_);
lean_closure_set(v___f_1612_, 1, v_ctors_1594_);
lean_closure_set(v___f_1612_, 2, v_tail_1595_);
lean_closure_set(v___f_1612_, 3, v_params_1596_);
lean_closure_set(v___f_1612_, 4, v_numParams_1597_);
lean_closure_set(v___f_1612_, 5, v_indName_1598_);
lean_closure_set(v___f_1612_, 6, v_val_1599_);
lean_closure_set(v___f_1612_, 7, v___x_1600_);
lean_closure_set(v___f_1612_, 8, v___x_1601_);
lean_closure_set(v___f_1612_, 9, v_name_1602_);
lean_closure_set(v___f_1612_, 10, v___x_1592_);
lean_closure_set(v___f_1612_, 11, v_t_1604_);
lean_closure_set(v___f_1612_, 12, v___x_1611_);
v___x_1613_ = 0;
v___x_1614_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1604_, v___x_1611_, v___f_1612_, v___x_1613_, v___x_1613_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1615_ = _args[0];
lean_object* v___x_1616_ = _args[1];
lean_object* v_head_1617_ = _args[2];
lean_object* v_ctors_1618_ = _args[3];
lean_object* v_tail_1619_ = _args[4];
lean_object* v_params_1620_ = _args[5];
lean_object* v_numParams_1621_ = _args[6];
lean_object* v_indName_1622_ = _args[7];
lean_object* v_val_1623_ = _args[8];
lean_object* v___x_1624_ = _args[9];
lean_object* v___x_1625_ = _args[10];
lean_object* v_name_1626_ = _args[11];
lean_object* v_x_1627_ = _args[12];
lean_object* v_t_1628_ = _args[13];
lean_object* v___y_1629_ = _args[14];
lean_object* v___y_1630_ = _args[15];
lean_object* v___y_1631_ = _args[16];
lean_object* v___y_1632_ = _args[17];
lean_object* v___y_1633_ = _args[18];
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1615_, v___x_1616_, v_head_1617_, v_ctors_1618_, v_tail_1619_, v_params_1620_, v_numParams_1621_, v_indName_1622_, v_val_1623_, v___x_1624_, v___x_1625_, v_name_1626_, v_x_1627_, v_t_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec(v___y_1630_);
lean_dec_ref(v___y_1629_);
lean_dec_ref(v_x_1627_);
lean_dec(v_numIndices_1615_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1637_, lean_object* v_head_1638_, lean_object* v_ctors_1639_, lean_object* v_tail_1640_, lean_object* v_numParams_1641_, lean_object* v_indName_1642_, lean_object* v_val_1643_, lean_object* v___x_1644_, lean_object* v___x_1645_, lean_object* v_name_1646_, lean_object* v_params_1647_, lean_object* v_t_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; lean_object* v___f_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; lean_object* v___x_1658_; 
v___x_1654_ = lean_unsigned_to_nat(1u);
v___f_1655_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 19, 12);
lean_closure_set(v___f_1655_, 0, v_numIndices_1637_);
lean_closure_set(v___f_1655_, 1, v___x_1654_);
lean_closure_set(v___f_1655_, 2, v_head_1638_);
lean_closure_set(v___f_1655_, 3, v_ctors_1639_);
lean_closure_set(v___f_1655_, 4, v_tail_1640_);
lean_closure_set(v___f_1655_, 5, v_params_1647_);
lean_closure_set(v___f_1655_, 6, v_numParams_1641_);
lean_closure_set(v___f_1655_, 7, v_indName_1642_);
lean_closure_set(v___f_1655_, 8, v_val_1643_);
lean_closure_set(v___f_1655_, 9, v___x_1644_);
lean_closure_set(v___f_1655_, 10, v___x_1645_);
lean_closure_set(v___f_1655_, 11, v_name_1646_);
v___x_1656_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1657_ = 0;
v___x_1658_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1648_, v___x_1656_, v___f_1655_, v___x_1657_, v___x_1657_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1659_ = _args[0];
lean_object* v_head_1660_ = _args[1];
lean_object* v_ctors_1661_ = _args[2];
lean_object* v_tail_1662_ = _args[3];
lean_object* v_numParams_1663_ = _args[4];
lean_object* v_indName_1664_ = _args[5];
lean_object* v_val_1665_ = _args[6];
lean_object* v___x_1666_ = _args[7];
lean_object* v___x_1667_ = _args[8];
lean_object* v_name_1668_ = _args[9];
lean_object* v_params_1669_ = _args[10];
lean_object* v_t_1670_ = _args[11];
lean_object* v___y_1671_ = _args[12];
lean_object* v___y_1672_ = _args[13];
lean_object* v___y_1673_ = _args[14];
lean_object* v___y_1674_ = _args[15];
lean_object* v___y_1675_ = _args[16];
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1659_, v_head_1660_, v_ctors_1661_, v_tail_1662_, v_numParams_1663_, v_indName_1664_, v_val_1665_, v___x_1666_, v___x_1667_, v_name_1668_, v_params_1669_, v_t_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec(v___y_1672_);
lean_dec_ref(v___y_1671_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1677_, lean_object* v_declName_1678_, lean_object* v_levelParams_1679_, uint8_t v___x_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; 
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
lean_inc_ref(v_a_1677_);
v___x_1686_ = lean_infer_type(v_a_1677_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1698_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v___x_1688_ = lean_box(1);
v___x_1689_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1678_, v_levelParams_1679_, v_a_1687_, v_a_1677_, v___x_1688_, v___y_1684_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
lean_ctor_set_tag(v___x_1692_, 1);
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1690_);
v___x_1695_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_addDecl(v___x_1695_, v___x_1680_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v___x_1696_;
}
}
}
else
{
lean_object* v_a_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1706_; 
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_levelParams_1679_);
lean_dec(v_declName_1678_);
lean_dec_ref(v_a_1677_);
v_a_1699_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1701_ = v___x_1686_;
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_a_1699_);
lean_dec(v___x_1686_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1706_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1704_; 
if (v_isShared_1702_ == 0)
{
v___x_1704_ = v___x_1701_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1699_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1707_, lean_object* v_declName_1708_, lean_object* v_levelParams_1709_, lean_object* v___x_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
uint8_t v___x_22314__boxed_1716_; lean_object* v_res_1717_; 
v___x_22314__boxed_1716_ = lean_unbox(v___x_1710_);
v_res_1717_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1707_, v_declName_1708_, v_levelParams_1709_, v___x_22314__boxed_1716_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1718_, lean_object* v_a_1719_){
_start:
{
if (lean_obj_tag(v_a_1718_) == 0)
{
lean_object* v___x_1720_; 
v___x_1720_ = l_List_reverse___redArg(v_a_1719_);
return v___x_1720_;
}
else
{
lean_object* v_head_1721_; lean_object* v_tail_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1731_; 
v_head_1721_ = lean_ctor_get(v_a_1718_, 0);
v_tail_1722_ = lean_ctor_get(v_a_1718_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_a_1718_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1724_ = v_a_1718_;
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_tail_1722_);
lean_inc(v_head_1721_);
lean_dec(v_a_1718_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1731_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = l_Lean_mkLevelParam(v_head_1721_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 1, v_a_1719_);
lean_ctor_set(v___x_1724_, 0, v___x_1726_);
v___x_1728_ = v___x_1724_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_a_1719_);
v___x_1728_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
v_a_1718_ = v_tail_1722_;
v_a_1719_ = v___x_1728_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object* v_msgData_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v_env_1739_; lean_object* v___x_1740_; lean_object* v_mctx_1741_; lean_object* v_lctx_1742_; lean_object* v_options_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1738_ = lean_st_ref_get(v___y_1736_);
v_env_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc_ref(v_env_1739_);
lean_dec(v___x_1738_);
v___x_1740_ = lean_st_ref_get(v___y_1734_);
v_mctx_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc_ref(v_mctx_1741_);
lean_dec(v___x_1740_);
v_lctx_1742_ = lean_ctor_get(v___y_1733_, 2);
v_options_1743_ = lean_ctor_get(v___y_1735_, 2);
lean_inc_ref(v_options_1743_);
lean_inc_ref(v_lctx_1742_);
v___x_1744_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1744_, 0, v_env_1739_);
lean_ctor_set(v___x_1744_, 1, v_mctx_1741_);
lean_ctor_set(v___x_1744_, 2, v_lctx_1742_);
lean_ctor_set(v___x_1744_, 3, v_options_1743_);
v___x_1745_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
lean_ctor_set(v___x_1745_, 1, v_msgData_1732_);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_ref_1760_; lean_object* v___x_1761_; lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1770_; 
v_ref_1760_ = lean_ctor_get(v___y_1757_, 5);
v___x_1761_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1764_ = v___x_1761_;
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1770_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_inc(v_ref_1760_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v_ref_1760_);
lean_ctor_set(v___x_1766_, 1, v_a_1762_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set_tag(v___x_1764_, 1);
lean_ctor_set(v___x_1764_, 0, v___x_1766_);
v___x_1768_ = v___x_1764_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1778_, lean_object* v_msg_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_fileName_1785_; lean_object* v_fileMap_1786_; lean_object* v_options_1787_; lean_object* v_currRecDepth_1788_; lean_object* v_maxRecDepth_1789_; lean_object* v_ref_1790_; lean_object* v_currNamespace_1791_; lean_object* v_openDecls_1792_; lean_object* v_initHeartbeats_1793_; lean_object* v_maxHeartbeats_1794_; lean_object* v_quotContext_1795_; lean_object* v_currMacroScope_1796_; uint8_t v_diag_1797_; lean_object* v_cancelTk_x3f_1798_; uint8_t v_suppressElabErrors_1799_; lean_object* v_inheritedTraceOptions_1800_; lean_object* v_ref_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_fileName_1785_ = lean_ctor_get(v___y_1782_, 0);
v_fileMap_1786_ = lean_ctor_get(v___y_1782_, 1);
v_options_1787_ = lean_ctor_get(v___y_1782_, 2);
v_currRecDepth_1788_ = lean_ctor_get(v___y_1782_, 3);
v_maxRecDepth_1789_ = lean_ctor_get(v___y_1782_, 4);
v_ref_1790_ = lean_ctor_get(v___y_1782_, 5);
v_currNamespace_1791_ = lean_ctor_get(v___y_1782_, 6);
v_openDecls_1792_ = lean_ctor_get(v___y_1782_, 7);
v_initHeartbeats_1793_ = lean_ctor_get(v___y_1782_, 8);
v_maxHeartbeats_1794_ = lean_ctor_get(v___y_1782_, 9);
v_quotContext_1795_ = lean_ctor_get(v___y_1782_, 10);
v_currMacroScope_1796_ = lean_ctor_get(v___y_1782_, 11);
v_diag_1797_ = lean_ctor_get_uint8(v___y_1782_, sizeof(void*)*14);
v_cancelTk_x3f_1798_ = lean_ctor_get(v___y_1782_, 12);
v_suppressElabErrors_1799_ = lean_ctor_get_uint8(v___y_1782_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1800_ = lean_ctor_get(v___y_1782_, 13);
v_ref_1801_ = l_Lean_replaceRef(v_ref_1778_, v_ref_1790_);
lean_inc_ref(v_inheritedTraceOptions_1800_);
lean_inc(v_cancelTk_x3f_1798_);
lean_inc(v_currMacroScope_1796_);
lean_inc(v_quotContext_1795_);
lean_inc(v_maxHeartbeats_1794_);
lean_inc(v_initHeartbeats_1793_);
lean_inc(v_openDecls_1792_);
lean_inc(v_currNamespace_1791_);
lean_inc(v_maxRecDepth_1789_);
lean_inc(v_currRecDepth_1788_);
lean_inc_ref(v_options_1787_);
lean_inc_ref(v_fileMap_1786_);
lean_inc_ref(v_fileName_1785_);
v___x_1802_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1802_, 0, v_fileName_1785_);
lean_ctor_set(v___x_1802_, 1, v_fileMap_1786_);
lean_ctor_set(v___x_1802_, 2, v_options_1787_);
lean_ctor_set(v___x_1802_, 3, v_currRecDepth_1788_);
lean_ctor_set(v___x_1802_, 4, v_maxRecDepth_1789_);
lean_ctor_set(v___x_1802_, 5, v_ref_1801_);
lean_ctor_set(v___x_1802_, 6, v_currNamespace_1791_);
lean_ctor_set(v___x_1802_, 7, v_openDecls_1792_);
lean_ctor_set(v___x_1802_, 8, v_initHeartbeats_1793_);
lean_ctor_set(v___x_1802_, 9, v_maxHeartbeats_1794_);
lean_ctor_set(v___x_1802_, 10, v_quotContext_1795_);
lean_ctor_set(v___x_1802_, 11, v_currMacroScope_1796_);
lean_ctor_set(v___x_1802_, 12, v_cancelTk_x3f_1798_);
lean_ctor_set(v___x_1802_, 13, v_inheritedTraceOptions_1800_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*14, v_diag_1797_);
lean_ctor_set_uint8(v___x_1802_, sizeof(void*)*14 + 1, v_suppressElabErrors_1799_);
v___x_1803_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1779_, v___y_1780_, v___y_1781_, v___x_1802_, v___y_1783_);
lean_dec_ref_known(v___x_1802_, 14);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1804_, lean_object* v_msg_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1804_, v_msg_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v_ref_1804_);
return v_res_1811_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
return v___x_1814_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_alloc_ctor(0, 10, 0);
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
return v___x_1817_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1821_ = ((size_t)5ULL);
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = lean_unsigned_to_nat(32u);
v___x_1824_ = lean_mk_empty_array_with_capacity(v___x_1823_);
v___x_1825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1826_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1824_);
lean_ctor_set(v___x_1826_, 2, v___x_1822_);
lean_ctor_set(v___x_1826_, 3, v___x_1822_);
lean_ctor_set_usize(v___x_1826_, 4, v___x_1821_);
return v___x_1826_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1827_ = lean_box(1);
v___x_1828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v___x_1828_);
lean_ctor_set(v___x_1830_, 2, v___x_1827_);
return v___x_1830_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6));
v___x_1833_ = l_Lean_stringToMessageData(v___x_1832_);
return v___x_1833_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8));
v___x_1836_ = l_Lean_stringToMessageData(v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10));
v___x_1839_ = l_Lean_stringToMessageData(v___x_1838_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12));
v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16));
v___x_1848_ = l_Lean_stringToMessageData(v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18));
v___x_1851_ = l_Lean_stringToMessageData(v___x_1850_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1852_, lean_object* v_declHint_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; lean_object* v_env_1857_; uint8_t v___x_1858_; 
v___x_1856_ = lean_st_ref_get(v___y_1854_);
v_env_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc_ref(v_env_1857_);
lean_dec(v___x_1856_);
v___x_1858_ = l_Lean_Name_isAnonymous(v_declHint_1853_);
if (v___x_1858_ == 0)
{
uint8_t v_isExporting_1859_; 
v_isExporting_1859_ = lean_ctor_get_uint8(v_env_1857_, sizeof(void*)*8);
if (v_isExporting_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref(v_env_1857_);
lean_dec(v_declHint_1853_);
v___x_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1860_, 0, v_msg_1852_);
return v___x_1860_;
}
else
{
lean_object* v___x_1861_; uint8_t v___x_1862_; 
lean_inc_ref(v_env_1857_);
v___x_1861_ = l_Lean_Environment_setExporting(v_env_1857_, v___x_1858_);
lean_inc(v_declHint_1853_);
lean_inc_ref(v___x_1861_);
v___x_1862_ = l_Lean_Environment_contains(v___x_1861_, v_declHint_1853_, v_isExporting_1859_);
if (v___x_1862_ == 0)
{
lean_object* v___x_1863_; 
lean_dec_ref(v___x_1861_);
lean_dec_ref(v_env_1857_);
lean_dec(v_declHint_1853_);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v_msg_1852_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v_c_1869_; lean_object* v___x_1870_; 
v___x_1864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1865_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5);
v___x_1866_ = l_Lean_Options_empty;
v___x_1867_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1861_);
lean_ctor_set(v___x_1867_, 1, v___x_1864_);
lean_ctor_set(v___x_1867_, 2, v___x_1865_);
lean_ctor_set(v___x_1867_, 3, v___x_1866_);
lean_inc(v_declHint_1853_);
v___x_1868_ = l_Lean_MessageData_ofConstName(v_declHint_1853_, v___x_1858_);
v_c_1869_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1869_, 0, v___x_1867_);
lean_ctor_set(v_c_1869_, 1, v___x_1868_);
v___x_1870_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1857_, v_declHint_1853_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref(v_env_1857_);
lean_dec(v_declHint_1853_);
v___x_1871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v_c_1869_);
v___x_1873_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = l_Lean_MessageData_note(v___x_1874_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_msg_1852_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
else
{
lean_object* v_val_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1913_; 
v_val_1878_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1880_ = v___x_1870_;
v_isShared_1881_ = v_isSharedCheck_1913_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_val_1878_);
lean_dec(v___x_1870_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1913_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v_mod_1885_; uint8_t v___x_1886_; 
v___x_1882_ = lean_box(0);
v___x_1883_ = l_Lean_Environment_header(v_env_1857_);
lean_dec_ref(v_env_1857_);
v___x_1884_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1883_);
v_mod_1885_ = lean_array_get(v___x_1882_, v___x_1884_, v_val_1878_);
lean_dec(v_val_1878_);
lean_dec_ref(v___x_1884_);
v___x_1886_ = l_Lean_isPrivateName(v_declHint_1853_);
lean_dec(v_declHint_1853_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1887_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v_c_1869_);
v___x_1889_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_MessageData_ofName(v_mod_1885_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = l_Lean_MessageData_note(v___x_1894_);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v_msg_1852_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1896_);
v___x_1898_ = v___x_1880_;
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
v___x_1900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v_c_1869_);
v___x_1902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_MessageData_ofName(v_mod_1885_);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Lean_MessageData_note(v___x_1907_);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v_msg_1852_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set_tag(v___x_1880_, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1909_);
v___x_1911_ = v___x_1880_;
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
lean_dec_ref(v_env_1857_);
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
v_ref_2000_ = lean_ctor_get(v___y_1997_, 5);
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
lean_object* v___x_2040_; lean_object* v_env_2041_; lean_object* v_nextMacroScope_2042_; lean_object* v_ngen_2043_; lean_object* v_auxDeclNGen_2044_; lean_object* v_traceState_2045_; lean_object* v_messages_2046_; lean_object* v_infoState_2047_; lean_object* v_snapshotTasks_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2077_; 
v___x_2040_ = lean_st_ref_take(v___y_2038_);
v_env_2041_ = lean_ctor_get(v___x_2040_, 0);
v_nextMacroScope_2042_ = lean_ctor_get(v___x_2040_, 1);
v_ngen_2043_ = lean_ctor_get(v___x_2040_, 2);
v_auxDeclNGen_2044_ = lean_ctor_get(v___x_2040_, 3);
v_traceState_2045_ = lean_ctor_get(v___x_2040_, 4);
v_messages_2046_ = lean_ctor_get(v___x_2040_, 6);
v_infoState_2047_ = lean_ctor_get(v___x_2040_, 7);
v_snapshotTasks_2048_ = lean_ctor_get(v___x_2040_, 8);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; 
v_unused_2078_ = lean_ctor_get(v___x_2040_, 5);
lean_dec(v_unused_2078_);
v___x_2050_ = v___x_2040_;
v_isShared_2051_ = v_isSharedCheck_2077_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_snapshotTasks_2048_);
lean_inc(v_infoState_2047_);
lean_inc(v_messages_2046_);
lean_inc(v_traceState_2045_);
lean_inc(v_auxDeclNGen_2044_);
lean_inc(v_ngen_2043_);
lean_inc(v_nextMacroScope_2042_);
lean_inc(v_env_2041_);
lean_dec(v___x_2040_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2077_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
uint8_t v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2052_ = 0;
v___x_2053_ = lean_box(0);
v___x_2054_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2041_, v_declName_2035_, v_s_2036_, v___x_2052_, v___x_2053_);
v___x_2055_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 5, v___x_2055_);
lean_ctor_set(v___x_2050_, 0, v___x_2054_);
v___x_2057_ = v___x_2050_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_nextMacroScope_2042_);
lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_ngen_2043_);
lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_auxDeclNGen_2044_);
lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_traceState_2045_);
lean_ctor_set(v_reuseFailAlloc_2076_, 5, v___x_2055_);
lean_ctor_set(v_reuseFailAlloc_2076_, 6, v_messages_2046_);
lean_ctor_set(v_reuseFailAlloc_2076_, 7, v_infoState_2047_);
lean_ctor_set(v_reuseFailAlloc_2076_, 8, v_snapshotTasks_2048_);
v___x_2057_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v_mctx_2060_; lean_object* v_zetaDeltaFVarIds_2061_; lean_object* v_postponed_2062_; lean_object* v_diag_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2074_; 
v___x_2058_ = lean_st_ref_set(v___y_2038_, v___x_2057_);
v___x_2059_ = lean_st_ref_take(v___y_2037_);
v_mctx_2060_ = lean_ctor_get(v___x_2059_, 0);
v_zetaDeltaFVarIds_2061_ = lean_ctor_get(v___x_2059_, 2);
v_postponed_2062_ = lean_ctor_get(v___x_2059_, 3);
v_diag_2063_ = lean_ctor_get(v___x_2059_, 4);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v___x_2059_, 1);
lean_dec(v_unused_2075_);
v___x_2065_ = v___x_2059_;
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_diag_2063_);
lean_inc(v_postponed_2062_);
lean_inc(v_zetaDeltaFVarIds_2061_);
lean_inc(v_mctx_2060_);
lean_dec(v___x_2059_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2074_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 1, v___x_2067_);
v___x_2069_ = v___x_2065_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_mctx_2060_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_zetaDeltaFVarIds_2061_);
lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_postponed_2062_);
lean_ctor_set(v_reuseFailAlloc_2073_, 4, v_diag_2063_);
v___x_2069_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_st_ref_set(v___y_2037_, v___x_2069_);
v___x_2071_ = lean_box(0);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2071_);
return v___x_2072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2079_, lean_object* v_s_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
uint8_t v_s_boxed_2084_; lean_object* v_res_2085_; 
v_s_boxed_2084_ = lean_unbox(v_s_2080_);
v_res_2085_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2079_, v_s_boxed_2084_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec(v___y_2081_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = 0;
v___x_2093_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2086_, v___x_2092_, v___y_2088_, v___y_2090_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
return v_res_2100_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2103_ = l_Lean_stringToMessageData(v___x_2102_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2106_ = l_Lean_stringToMessageData(v___x_2105_);
return v___x_2106_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2109_ = l_Lean_stringToMessageData(v___x_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2110_, lean_object* v_declName_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2117_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2118_ = l_Lean_MessageData_ofName(v_attrName_2110_);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___x_2122_ = 0;
v___x_2123_ = l_Lean_MessageData_ofConstName(v_declName_2111_, v___x_2122_);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2121_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2126_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2128_, lean_object* v_declName_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2128_, v_declName_2129_, v___y_2130_, v___y_2131_, v___y_2132_, v___y_2133_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
return v_res_2135_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2137_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2138_ = l_Lean_stringToMessageData(v___x_2137_);
return v___x_2138_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2141_ = l_Lean_stringToMessageData(v___x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2142_, lean_object* v_declName_2143_, lean_object* v_asyncPrefix_x3f_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___y_2151_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2144_) == 0)
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_MessageData_nil;
v___y_2151_ = v___x_2164_;
goto v___jp_2150_;
}
else
{
lean_object* v_val_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v_val_2165_ = lean_ctor_get(v_asyncPrefix_x3f_2144_, 0);
lean_inc(v_val_2165_);
lean_dec_ref_known(v_asyncPrefix_x3f_2144_, 1);
v___x_2166_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2167_ = l_Lean_MessageData_ofName(v_val_2165_);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2168_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___y_2151_ = v___x_2170_;
goto v___jp_2150_;
}
v___jp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2152_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2153_ = l_Lean_MessageData_ofName(v_attrName_2142_);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2154_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = 0;
v___x_2158_ = l_Lean_MessageData_ofConstName(v_declName_2143_, v___x_2157_);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2156_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2159_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___y_2151_);
v___x_2163_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2162_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2171_, lean_object* v_declName_2172_, lean_object* v_asyncPrefix_x3f_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2171_, v_declName_2172_, v_asyncPrefix_x3f_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2180_, lean_object* v_decl_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v___y_2188_; lean_object* v___y_2189_; lean_object* v___x_2230_; lean_object* v_env_2231_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; lean_object* v___y_2236_; lean_object* v___x_2246_; 
v___x_2230_ = lean_st_ref_get(v___y_2185_);
v_env_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc_ref(v_env_2231_);
lean_dec(v___x_2230_);
v___x_2246_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2231_, v_decl_2181_);
if (lean_obj_tag(v___x_2246_) == 0)
{
v___y_2233_ = v___y_2182_;
v___y_2234_ = v___y_2183_;
v___y_2235_ = v___y_2184_;
v___y_2236_ = v___y_2185_;
goto v___jp_2232_;
}
else
{
lean_object* v_attr_2247_; lean_object* v_toAttributeImplCore_2248_; lean_object* v_name_2249_; lean_object* v___x_2250_; 
lean_dec_ref_known(v___x_2246_, 1);
lean_dec_ref(v_env_2231_);
v_attr_2247_ = lean_ctor_get(v_attr_2180_, 0);
lean_inc_ref(v_attr_2247_);
lean_dec_ref(v_attr_2180_);
v_toAttributeImplCore_2248_ = lean_ctor_get(v_attr_2247_, 0);
lean_inc_ref(v_toAttributeImplCore_2248_);
lean_dec_ref(v_attr_2247_);
v_name_2249_ = lean_ctor_get(v_toAttributeImplCore_2248_, 1);
lean_inc(v_name_2249_);
lean_dec_ref(v_toAttributeImplCore_2248_);
v___x_2250_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2249_, v_decl_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
return v___x_2250_;
}
v___jp_2187_:
{
lean_object* v___x_2190_; lean_object* v_ext_2191_; lean_object* v_toEnvExtension_2192_; lean_object* v_env_2193_; lean_object* v_nextMacroScope_2194_; lean_object* v_ngen_2195_; lean_object* v_auxDeclNGen_2196_; lean_object* v_traceState_2197_; lean_object* v_messages_2198_; lean_object* v_infoState_2199_; lean_object* v_snapshotTasks_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2228_; 
v___x_2190_ = lean_st_ref_take(v___y_2189_);
v_ext_2191_ = lean_ctor_get(v_attr_2180_, 1);
lean_inc_ref(v_ext_2191_);
lean_dec_ref(v_attr_2180_);
v_toEnvExtension_2192_ = lean_ctor_get(v_ext_2191_, 0);
v_env_2193_ = lean_ctor_get(v___x_2190_, 0);
v_nextMacroScope_2194_ = lean_ctor_get(v___x_2190_, 1);
v_ngen_2195_ = lean_ctor_get(v___x_2190_, 2);
v_auxDeclNGen_2196_ = lean_ctor_get(v___x_2190_, 3);
v_traceState_2197_ = lean_ctor_get(v___x_2190_, 4);
v_messages_2198_ = lean_ctor_get(v___x_2190_, 6);
v_infoState_2199_ = lean_ctor_get(v___x_2190_, 7);
v_snapshotTasks_2200_ = lean_ctor_get(v___x_2190_, 8);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v___x_2190_, 5);
lean_dec(v_unused_2229_);
v___x_2202_ = v___x_2190_;
v_isShared_2203_ = v_isSharedCheck_2228_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_snapshotTasks_2200_);
lean_inc(v_infoState_2199_);
lean_inc(v_messages_2198_);
lean_inc(v_traceState_2197_);
lean_inc(v_auxDeclNGen_2196_);
lean_inc(v_ngen_2195_);
lean_inc(v_nextMacroScope_2194_);
lean_inc(v_env_2193_);
lean_dec(v___x_2190_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2228_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v_asyncMode_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v_asyncMode_2204_ = lean_ctor_get(v_toEnvExtension_2192_, 2);
lean_inc(v_asyncMode_2204_);
lean_inc(v_decl_2181_);
v___x_2205_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2191_, v_env_2193_, v_decl_2181_, v_asyncMode_2204_, v_decl_2181_);
lean_dec(v_asyncMode_2204_);
v___x_2206_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 5, v___x_2206_);
lean_ctor_set(v___x_2202_, 0, v___x_2205_);
v___x_2208_ = v___x_2202_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2205_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_nextMacroScope_2194_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v_ngen_2195_);
lean_ctor_set(v_reuseFailAlloc_2227_, 3, v_auxDeclNGen_2196_);
lean_ctor_set(v_reuseFailAlloc_2227_, 4, v_traceState_2197_);
lean_ctor_set(v_reuseFailAlloc_2227_, 5, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2227_, 6, v_messages_2198_);
lean_ctor_set(v_reuseFailAlloc_2227_, 7, v_infoState_2199_);
lean_ctor_set(v_reuseFailAlloc_2227_, 8, v_snapshotTasks_2200_);
v___x_2208_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v_mctx_2211_; lean_object* v_zetaDeltaFVarIds_2212_; lean_object* v_postponed_2213_; lean_object* v_diag_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2225_; 
v___x_2209_ = lean_st_ref_set(v___y_2189_, v___x_2208_);
v___x_2210_ = lean_st_ref_take(v___y_2188_);
v_mctx_2211_ = lean_ctor_get(v___x_2210_, 0);
v_zetaDeltaFVarIds_2212_ = lean_ctor_get(v___x_2210_, 2);
v_postponed_2213_ = lean_ctor_get(v___x_2210_, 3);
v_diag_2214_ = lean_ctor_get(v___x_2210_, 4);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v___x_2210_, 1);
lean_dec(v_unused_2226_);
v___x_2216_ = v___x_2210_;
v_isShared_2217_ = v_isSharedCheck_2225_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_diag_2214_);
lean_inc(v_postponed_2213_);
lean_inc(v_zetaDeltaFVarIds_2212_);
lean_inc(v_mctx_2211_);
lean_dec(v___x_2210_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2225_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2218_; lean_object* v___x_2220_; 
v___x_2218_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 1, v___x_2218_);
v___x_2220_ = v___x_2216_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_mctx_2211_);
lean_ctor_set(v_reuseFailAlloc_2224_, 1, v___x_2218_);
lean_ctor_set(v_reuseFailAlloc_2224_, 2, v_zetaDeltaFVarIds_2212_);
lean_ctor_set(v_reuseFailAlloc_2224_, 3, v_postponed_2213_);
lean_ctor_set(v_reuseFailAlloc_2224_, 4, v_diag_2214_);
v___x_2220_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = lean_st_ref_set(v___y_2188_, v___x_2220_);
v___x_2222_ = lean_box(0);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
return v___x_2223_;
}
}
}
}
}
v___jp_2232_:
{
lean_object* v_ext_2237_; lean_object* v_toEnvExtension_2238_; lean_object* v_attr_2239_; lean_object* v_asyncMode_2240_; uint8_t v___x_2241_; 
v_ext_2237_ = lean_ctor_get(v_attr_2180_, 1);
v_toEnvExtension_2238_ = lean_ctor_get(v_ext_2237_, 0);
v_attr_2239_ = lean_ctor_get(v_attr_2180_, 0);
v_asyncMode_2240_ = lean_ctor_get(v_toEnvExtension_2238_, 2);
lean_inc(v_decl_2181_);
lean_inc_ref(v_env_2231_);
v___x_2241_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2231_, v_decl_2181_, v_asyncMode_2240_);
if (v___x_2241_ == 0)
{
lean_object* v_toAttributeImplCore_2242_; lean_object* v_name_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
lean_inc_ref(v_attr_2239_);
lean_dec_ref(v_attr_2180_);
v_toAttributeImplCore_2242_ = lean_ctor_get(v_attr_2239_, 0);
lean_inc_ref(v_toAttributeImplCore_2242_);
lean_dec_ref(v_attr_2239_);
v_name_2243_ = lean_ctor_get(v_toAttributeImplCore_2242_, 1);
lean_inc(v_name_2243_);
lean_dec_ref(v_toAttributeImplCore_2242_);
v___x_2244_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2231_);
v___x_2245_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2243_, v_decl_2181_, v___x_2244_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
return v___x_2245_;
}
else
{
lean_dec_ref(v_env_2231_);
v___y_2188_ = v___y_2234_;
v___y_2189_ = v___y_2236_;
goto v___jp_2187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2251_, lean_object* v_decl_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2251_, v_decl_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; lean_object* v_env_2266_; uint8_t v___x_2267_; lean_object* v___x_2268_; 
v___x_2265_ = lean_st_ref_get(v___y_2263_);
v_env_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc_ref(v_env_2266_);
lean_dec(v___x_2265_);
v___x_2267_ = 0;
lean_inc(v_constName_2259_);
v___x_2268_ = l_Lean_Environment_find_x3f(v_env_2266_, v_constName_2259_, v___x_2267_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v___x_2269_; 
v___x_2269_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
return v___x_2269_;
}
else
{
lean_object* v_val_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_constName_2259_);
v_val_2270_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2268_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_val_2270_);
lean_dec(v___x_2268_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
lean_ctor_set_tag(v___x_2272_, 0);
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_val_2270_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
return v_res_2284_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2288_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2289_ = lean_unsigned_to_nat(58u);
v___x_2290_ = lean_unsigned_to_nat(33u);
v___x_2291_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2292_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2293_ = l_mkPanicMessageWithDecl(v___x_2292_, v___x_2291_, v___x_2290_, v___x_2289_, v___x_2288_);
return v___x_2293_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2295_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2296_ = lean_unsigned_to_nat(60u);
v___x_2297_ = lean_unsigned_to_nat(30u);
v___x_2298_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2299_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2300_ = l_mkPanicMessageWithDecl(v___x_2299_, v___x_2298_, v___x_2297_, v___x_2296_, v___x_2295_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2301_, lean_object* v_indName_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; 
lean_inc(v_indName_2302_);
v___x_2308_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2302_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v_a_2309_; 
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_a_2309_);
lean_dec_ref_known(v___x_2308_, 1);
if (lean_obj_tag(v_a_2309_) == 5)
{
lean_object* v_val_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2496_; 
v_val_2310_ = lean_ctor_get(v_a_2309_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v_a_2309_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2312_ = v_a_2309_;
v_isShared_2313_ = v_isSharedCheck_2496_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_val_2310_);
lean_dec(v_a_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2496_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_inc(v_indName_2302_);
v___x_2314_ = l_Lean_mkCasesOnName(v_indName_2302_);
lean_inc(v___x_2314_);
v___x_2315_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2314_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v_name_2317_; lean_object* v_levelParams_2318_; lean_object* v_type_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v_name_2317_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_name_2317_);
v_levelParams_2318_ = lean_ctor_get(v_a_2316_, 1);
lean_inc_n(v_levelParams_2318_, 2);
v_type_2319_ = lean_ctor_get(v_a_2316_, 2);
lean_inc_ref(v_type_2319_);
lean_dec(v_a_2316_);
v___x_2320_ = lean_box(0);
v___x_2321_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2318_, v___x_2320_);
if (lean_obj_tag(v___x_2321_) == 1)
{
lean_object* v_head_2322_; lean_object* v_tail_2323_; lean_object* v_numParams_2324_; lean_object* v_numIndices_2325_; lean_object* v_ctors_2326_; lean_object* v___f_2327_; lean_object* v___x_2329_; 
v_head_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_head_2322_);
v_tail_2323_ = lean_ctor_get(v___x_2321_, 1);
lean_inc(v_tail_2323_);
v_numParams_2324_ = lean_ctor_get(v_val_2310_, 1);
lean_inc_n(v_numParams_2324_, 2);
v_numIndices_2325_ = lean_ctor_get(v_val_2310_, 2);
lean_inc(v_numIndices_2325_);
v_ctors_2326_ = lean_ctor_get(v_val_2310_, 4);
lean_inc(v_ctors_2326_);
v___f_2327_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2327_, 0, v_numIndices_2325_);
lean_closure_set(v___f_2327_, 1, v_head_2322_);
lean_closure_set(v___f_2327_, 2, v_ctors_2326_);
lean_closure_set(v___f_2327_, 3, v_tail_2323_);
lean_closure_set(v___f_2327_, 4, v_numParams_2324_);
lean_closure_set(v___f_2327_, 5, v_indName_2302_);
lean_closure_set(v___f_2327_, 6, v_val_2310_);
lean_closure_set(v___f_2327_, 7, v___x_2321_);
lean_closure_set(v___f_2327_, 8, v___x_2314_);
lean_closure_set(v___f_2327_, 9, v_name_2317_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set_tag(v___x_2312_, 1);
lean_ctor_set(v___x_2312_, 0, v_numParams_2324_);
v___x_2329_ = v___x_2312_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_numParams_2324_);
v___x_2329_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
uint8_t v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = 0;
v___x_2331_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2319_, v___x_2329_, v___f_2327_, v___x_2330_, v___x_2330_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2333_; lean_object* v___f_2334_; uint8_t v___y_2336_; uint8_t v___x_2475_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref_known(v___x_2331_, 1);
v___x_2333_ = lean_box(v___x_2330_);
lean_inc(v_declName_2301_);
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2334_, 0, v_a_2332_);
lean_closure_set(v___f_2334_, 1, v_declName_2301_);
lean_closure_set(v___f_2334_, 2, v_levelParams_2318_);
lean_closure_set(v___f_2334_, 3, v___x_2333_);
v___x_2475_ = l_Lean_isPrivateName(v_declName_2301_);
if (v___x_2475_ == 0)
{
uint8_t v___x_2476_; 
v___x_2476_ = 1;
v___y_2336_ = v___x_2476_;
goto v___jp_2335_;
}
else
{
v___y_2336_ = v___x_2330_;
goto v___jp_2335_;
}
v___jp_2335_:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2334_, v___y_2336_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v___x_2338_; lean_object* v_env_2339_; lean_object* v_nextMacroScope_2340_; lean_object* v_ngen_2341_; lean_object* v_auxDeclNGen_2342_; lean_object* v_traceState_2343_; lean_object* v_messages_2344_; lean_object* v_infoState_2345_; lean_object* v_snapshotTasks_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref_known(v___x_2337_, 1);
v___x_2338_ = lean_st_ref_take(v_a_2306_);
v_env_2339_ = lean_ctor_get(v___x_2338_, 0);
v_nextMacroScope_2340_ = lean_ctor_get(v___x_2338_, 1);
v_ngen_2341_ = lean_ctor_get(v___x_2338_, 2);
v_auxDeclNGen_2342_ = lean_ctor_get(v___x_2338_, 3);
v_traceState_2343_ = lean_ctor_get(v___x_2338_, 4);
v_messages_2344_ = lean_ctor_get(v___x_2338_, 6);
v_infoState_2345_ = lean_ctor_get(v___x_2338_, 7);
v_snapshotTasks_2346_ = lean_ctor_get(v___x_2338_, 8);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v___x_2338_, 5);
lean_dec(v_unused_2474_);
v___x_2348_ = v___x_2338_;
v_isShared_2349_ = v_isSharedCheck_2473_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_snapshotTasks_2346_);
lean_inc(v_infoState_2345_);
lean_inc(v_messages_2344_);
lean_inc(v_traceState_2343_);
lean_inc(v_auxDeclNGen_2342_);
lean_inc(v_ngen_2341_);
lean_inc(v_nextMacroScope_2340_);
lean_inc(v_env_2339_);
lean_dec(v___x_2338_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2473_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
lean_inc(v_declName_2301_);
v___x_2350_ = l_Lean_Meta_markMatcherLike(v_env_2339_, v_declName_2301_);
v___x_2351_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 5, v___x_2351_);
lean_ctor_set(v___x_2348_, 0, v___x_2350_);
v___x_2353_ = v___x_2348_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_nextMacroScope_2340_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_ngen_2341_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_auxDeclNGen_2342_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_traceState_2343_);
lean_ctor_set(v_reuseFailAlloc_2472_, 5, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2472_, 6, v_messages_2344_);
lean_ctor_set(v_reuseFailAlloc_2472_, 7, v_infoState_2345_);
lean_ctor_set(v_reuseFailAlloc_2472_, 8, v_snapshotTasks_2346_);
v___x_2353_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v_mctx_2356_; lean_object* v_zetaDeltaFVarIds_2357_; lean_object* v_postponed_2358_; lean_object* v_diag_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2470_; 
v___x_2354_ = lean_st_ref_set(v_a_2306_, v___x_2353_);
v___x_2355_ = lean_st_ref_take(v_a_2304_);
v_mctx_2356_ = lean_ctor_get(v___x_2355_, 0);
v_zetaDeltaFVarIds_2357_ = lean_ctor_get(v___x_2355_, 2);
v_postponed_2358_ = lean_ctor_get(v___x_2355_, 3);
v_diag_2359_ = lean_ctor_get(v___x_2355_, 4);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v___x_2355_, 1);
lean_dec(v_unused_2471_);
v___x_2361_ = v___x_2355_;
v_isShared_2362_ = v_isSharedCheck_2470_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_diag_2359_);
lean_inc(v_postponed_2358_);
lean_inc(v_zetaDeltaFVarIds_2357_);
lean_inc(v_mctx_2356_);
lean_dec(v___x_2355_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2470_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v___x_2363_; lean_object* v___x_2365_; 
v___x_2363_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 1, v___x_2363_);
v___x_2365_ = v___x_2361_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_mctx_2356_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_zetaDeltaFVarIds_2357_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_postponed_2358_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v_diag_2359_);
v___x_2365_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v_env_2368_; lean_object* v_nextMacroScope_2369_; lean_object* v_ngen_2370_; lean_object* v_auxDeclNGen_2371_; lean_object* v_traceState_2372_; lean_object* v_messages_2373_; lean_object* v_infoState_2374_; lean_object* v_snapshotTasks_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2467_; 
v___x_2366_ = lean_st_ref_set(v_a_2304_, v___x_2365_);
v___x_2367_ = lean_st_ref_take(v_a_2306_);
v_env_2368_ = lean_ctor_get(v___x_2367_, 0);
v_nextMacroScope_2369_ = lean_ctor_get(v___x_2367_, 1);
v_ngen_2370_ = lean_ctor_get(v___x_2367_, 2);
v_auxDeclNGen_2371_ = lean_ctor_get(v___x_2367_, 3);
v_traceState_2372_ = lean_ctor_get(v___x_2367_, 4);
v_messages_2373_ = lean_ctor_get(v___x_2367_, 6);
v_infoState_2374_ = lean_ctor_get(v___x_2367_, 7);
v_snapshotTasks_2375_ = lean_ctor_get(v___x_2367_, 8);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; 
v_unused_2468_ = lean_ctor_get(v___x_2367_, 5);
lean_dec(v_unused_2468_);
v___x_2377_ = v___x_2367_;
v_isShared_2378_ = v_isSharedCheck_2467_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_snapshotTasks_2375_);
lean_inc(v_infoState_2374_);
lean_inc(v_messages_2373_);
lean_inc(v_traceState_2372_);
lean_inc(v_auxDeclNGen_2371_);
lean_inc(v_ngen_2370_);
lean_inc(v_nextMacroScope_2369_);
lean_inc(v_env_2368_);
lean_dec(v___x_2367_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2467_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2381_; 
lean_inc(v_declName_2301_);
v___x_2379_ = l_Lean_markAuxRecursor(v_env_2368_, v_declName_2301_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 5, v___x_2351_);
lean_ctor_set(v___x_2377_, 0, v___x_2379_);
v___x_2381_ = v___x_2377_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2379_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_nextMacroScope_2369_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v_ngen_2370_);
lean_ctor_set(v_reuseFailAlloc_2466_, 3, v_auxDeclNGen_2371_);
lean_ctor_set(v_reuseFailAlloc_2466_, 4, v_traceState_2372_);
lean_ctor_set(v_reuseFailAlloc_2466_, 5, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2466_, 6, v_messages_2373_);
lean_ctor_set(v_reuseFailAlloc_2466_, 7, v_infoState_2374_);
lean_ctor_set(v_reuseFailAlloc_2466_, 8, v_snapshotTasks_2375_);
v___x_2381_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v_mctx_2384_; lean_object* v_zetaDeltaFVarIds_2385_; lean_object* v_postponed_2386_; lean_object* v_diag_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2464_; 
v___x_2382_ = lean_st_ref_set(v_a_2306_, v___x_2381_);
v___x_2383_ = lean_st_ref_take(v_a_2304_);
v_mctx_2384_ = lean_ctor_get(v___x_2383_, 0);
v_zetaDeltaFVarIds_2385_ = lean_ctor_get(v___x_2383_, 2);
v_postponed_2386_ = lean_ctor_get(v___x_2383_, 3);
v_diag_2387_ = lean_ctor_get(v___x_2383_, 4);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2383_, 1);
lean_dec(v_unused_2465_);
v___x_2389_ = v___x_2383_;
v_isShared_2390_ = v_isSharedCheck_2464_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_diag_2387_);
lean_inc(v_postponed_2386_);
lean_inc(v_zetaDeltaFVarIds_2385_);
lean_inc(v_mctx_2384_);
lean_dec(v___x_2383_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2464_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 1, v___x_2363_);
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_mctx_2384_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v_zetaDeltaFVarIds_2385_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v_postponed_2386_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_diag_2387_);
v___x_2392_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_env_2395_; lean_object* v_nextMacroScope_2396_; lean_object* v_ngen_2397_; lean_object* v_auxDeclNGen_2398_; lean_object* v_traceState_2399_; lean_object* v_messages_2400_; lean_object* v_infoState_2401_; lean_object* v_snapshotTasks_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2461_; 
v___x_2393_ = lean_st_ref_set(v_a_2304_, v___x_2392_);
v___x_2394_ = lean_st_ref_take(v_a_2306_);
v_env_2395_ = lean_ctor_get(v___x_2394_, 0);
v_nextMacroScope_2396_ = lean_ctor_get(v___x_2394_, 1);
v_ngen_2397_ = lean_ctor_get(v___x_2394_, 2);
v_auxDeclNGen_2398_ = lean_ctor_get(v___x_2394_, 3);
v_traceState_2399_ = lean_ctor_get(v___x_2394_, 4);
v_messages_2400_ = lean_ctor_get(v___x_2394_, 6);
v_infoState_2401_ = lean_ctor_get(v___x_2394_, 7);
v_snapshotTasks_2402_ = lean_ctor_get(v___x_2394_, 8);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v___x_2394_, 5);
lean_dec(v_unused_2462_);
v___x_2404_ = v___x_2394_;
v_isShared_2405_ = v_isSharedCheck_2461_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_snapshotTasks_2402_);
lean_inc(v_infoState_2401_);
lean_inc(v_messages_2400_);
lean_inc(v_traceState_2399_);
lean_inc(v_auxDeclNGen_2398_);
lean_inc(v_ngen_2397_);
lean_inc(v_nextMacroScope_2396_);
lean_inc(v_env_2395_);
lean_dec(v___x_2394_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2461_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
lean_inc(v_declName_2301_);
v___x_2406_ = l_Lean_Meta_addToCompletionBlackList(v_env_2395_, v_declName_2301_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 5, v___x_2351_);
lean_ctor_set(v___x_2404_, 0, v___x_2406_);
v___x_2408_ = v___x_2404_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_nextMacroScope_2396_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_ngen_2397_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v_auxDeclNGen_2398_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v_traceState_2399_);
lean_ctor_set(v_reuseFailAlloc_2460_, 5, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2460_, 6, v_messages_2400_);
lean_ctor_set(v_reuseFailAlloc_2460_, 7, v_infoState_2401_);
lean_ctor_set(v_reuseFailAlloc_2460_, 8, v_snapshotTasks_2402_);
v___x_2408_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v_mctx_2411_; lean_object* v_zetaDeltaFVarIds_2412_; lean_object* v_postponed_2413_; lean_object* v_diag_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2458_; 
v___x_2409_ = lean_st_ref_set(v_a_2306_, v___x_2408_);
v___x_2410_ = lean_st_ref_take(v_a_2304_);
v_mctx_2411_ = lean_ctor_get(v___x_2410_, 0);
v_zetaDeltaFVarIds_2412_ = lean_ctor_get(v___x_2410_, 2);
v_postponed_2413_ = lean_ctor_get(v___x_2410_, 3);
v_diag_2414_ = lean_ctor_get(v___x_2410_, 4);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v___x_2410_, 1);
lean_dec(v_unused_2459_);
v___x_2416_ = v___x_2410_;
v_isShared_2417_ = v_isSharedCheck_2458_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_diag_2414_);
lean_inc(v_postponed_2413_);
lean_inc(v_zetaDeltaFVarIds_2412_);
lean_inc(v_mctx_2411_);
lean_dec(v___x_2410_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2458_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 1, v___x_2363_);
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_mctx_2411_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_zetaDeltaFVarIds_2412_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_postponed_2413_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_diag_2414_);
v___x_2419_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v_env_2422_; lean_object* v_nextMacroScope_2423_; lean_object* v_ngen_2424_; lean_object* v_auxDeclNGen_2425_; lean_object* v_traceState_2426_; lean_object* v_messages_2427_; lean_object* v_infoState_2428_; lean_object* v_snapshotTasks_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2455_; 
v___x_2420_ = lean_st_ref_set(v_a_2304_, v___x_2419_);
v___x_2421_ = lean_st_ref_take(v_a_2306_);
v_env_2422_ = lean_ctor_get(v___x_2421_, 0);
v_nextMacroScope_2423_ = lean_ctor_get(v___x_2421_, 1);
v_ngen_2424_ = lean_ctor_get(v___x_2421_, 2);
v_auxDeclNGen_2425_ = lean_ctor_get(v___x_2421_, 3);
v_traceState_2426_ = lean_ctor_get(v___x_2421_, 4);
v_messages_2427_ = lean_ctor_get(v___x_2421_, 6);
v_infoState_2428_ = lean_ctor_get(v___x_2421_, 7);
v_snapshotTasks_2429_ = lean_ctor_get(v___x_2421_, 8);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2455_ == 0)
{
lean_object* v_unused_2456_; 
v_unused_2456_ = lean_ctor_get(v___x_2421_, 5);
lean_dec(v_unused_2456_);
v___x_2431_ = v___x_2421_;
v_isShared_2432_ = v_isSharedCheck_2455_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_snapshotTasks_2429_);
lean_inc(v_infoState_2428_);
lean_inc(v_messages_2427_);
lean_inc(v_traceState_2426_);
lean_inc(v_auxDeclNGen_2425_);
lean_inc(v_ngen_2424_);
lean_inc(v_nextMacroScope_2423_);
lean_inc(v_env_2422_);
lean_dec(v___x_2421_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2455_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
lean_inc(v_declName_2301_);
v___x_2433_ = l_Lean_addProtected(v_env_2422_, v_declName_2301_);
if (v_isShared_2432_ == 0)
{
lean_ctor_set(v___x_2431_, 5, v___x_2351_);
lean_ctor_set(v___x_2431_, 0, v___x_2433_);
v___x_2435_ = v___x_2431_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_nextMacroScope_2423_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v_ngen_2424_);
lean_ctor_set(v_reuseFailAlloc_2454_, 3, v_auxDeclNGen_2425_);
lean_ctor_set(v_reuseFailAlloc_2454_, 4, v_traceState_2426_);
lean_ctor_set(v_reuseFailAlloc_2454_, 5, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2454_, 6, v_messages_2427_);
lean_ctor_set(v_reuseFailAlloc_2454_, 7, v_infoState_2428_);
lean_ctor_set(v_reuseFailAlloc_2454_, 8, v_snapshotTasks_2429_);
v___x_2435_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v_mctx_2438_; lean_object* v_zetaDeltaFVarIds_2439_; lean_object* v_postponed_2440_; lean_object* v_diag_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2452_; 
v___x_2436_ = lean_st_ref_set(v_a_2306_, v___x_2435_);
v___x_2437_ = lean_st_ref_take(v_a_2304_);
v_mctx_2438_ = lean_ctor_get(v___x_2437_, 0);
v_zetaDeltaFVarIds_2439_ = lean_ctor_get(v___x_2437_, 2);
v_postponed_2440_ = lean_ctor_get(v___x_2437_, 3);
v_diag_2441_ = lean_ctor_get(v___x_2437_, 4);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2452_ == 0)
{
lean_object* v_unused_2453_; 
v_unused_2453_ = lean_ctor_get(v___x_2437_, 1);
lean_dec(v_unused_2453_);
v___x_2443_ = v___x_2437_;
v_isShared_2444_ = v_isSharedCheck_2452_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_diag_2441_);
lean_inc(v_postponed_2440_);
lean_inc(v_zetaDeltaFVarIds_2439_);
lean_inc(v_mctx_2438_);
lean_dec(v___x_2437_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2452_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 1, v___x_2363_);
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_mctx_2438_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v_zetaDeltaFVarIds_2439_);
lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_postponed_2440_);
lean_ctor_set(v_reuseFailAlloc_2451_, 4, v_diag_2441_);
v___x_2446_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = lean_st_ref_set(v_a_2304_, v___x_2446_);
v___x_2448_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2301_);
v___x_2449_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2448_, v_declName_2301_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v___x_2450_; 
lean_dec_ref_known(v___x_2449_, 1);
v___x_2450_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2301_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
return v___x_2450_;
}
else
{
lean_dec(v_declName_2301_);
return v___x_2449_;
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
lean_dec(v_declName_2301_);
return v___x_2337_;
}
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_levelParams_2318_);
lean_dec(v_declName_2301_);
v_a_2477_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2331_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2331_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
else
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec(v___x_2321_);
lean_dec_ref(v_type_2319_);
lean_dec(v_levelParams_2318_);
lean_dec(v_name_2317_);
lean_dec(v___x_2314_);
lean_del_object(v___x_2312_);
lean_dec_ref(v_val_2310_);
lean_dec(v_indName_2302_);
lean_dec(v_declName_2301_);
v___x_2486_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2487_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2486_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
return v___x_2487_;
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v___x_2314_);
lean_del_object(v___x_2312_);
lean_dec_ref(v_val_2310_);
lean_dec(v_indName_2302_);
lean_dec(v_declName_2301_);
v_a_2488_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2315_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2315_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_dec(v_a_2309_);
lean_dec(v_indName_2302_);
lean_dec(v_declName_2301_);
v___x_2497_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2498_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2497_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
return v___x_2498_;
}
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_indName_2302_);
lean_dec(v_declName_2301_);
v_a_2499_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2308_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2308_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2507_, lean_object* v_indName_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2507_, v_indName_2508_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2515_, lean_object* v_name_2516_, lean_object* v_type_2517_, lean_object* v_k_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2516_, v_type_2517_, v_k_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2525_, lean_object* v_name_2526_, lean_object* v_type_2527_, lean_object* v_k_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2525_, v_name_2526_, v_type_2527_, v_k_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
lean_dec(v___y_2532_);
lean_dec_ref(v___y_2531_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2535_, lean_object* v_params_2536_, lean_object* v_alts_2537_, lean_object* v___x_2538_, lean_object* v_ism2_2539_, lean_object* v_motive_2540_, lean_object* v_val_2541_, lean_object* v_indName_2542_, lean_object* v___x_2543_, lean_object* v___x_2544_, lean_object* v___x_2545_, lean_object* v_as_2546_, size_t v_sz_2547_, size_t v_i_2548_, lean_object* v_bs_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2535_, v_params_2536_, v_alts_2537_, v___x_2538_, v_ism2_2539_, v_motive_2540_, v_val_2541_, v_indName_2542_, v___x_2543_, v___x_2544_, v___x_2545_, v_sz_2547_, v_i_2548_, v_bs_2549_, v___y_2550_, v___y_2551_, v___y_2552_, v___y_2553_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2556_ = _args[0];
lean_object* v_params_2557_ = _args[1];
lean_object* v_alts_2558_ = _args[2];
lean_object* v___x_2559_ = _args[3];
lean_object* v_ism2_2560_ = _args[4];
lean_object* v_motive_2561_ = _args[5];
lean_object* v_val_2562_ = _args[6];
lean_object* v_indName_2563_ = _args[7];
lean_object* v___x_2564_ = _args[8];
lean_object* v___x_2565_ = _args[9];
lean_object* v___x_2566_ = _args[10];
lean_object* v_as_2567_ = _args[11];
lean_object* v_sz_2568_ = _args[12];
lean_object* v_i_2569_ = _args[13];
lean_object* v_bs_2570_ = _args[14];
lean_object* v___y_2571_ = _args[15];
lean_object* v___y_2572_ = _args[16];
lean_object* v___y_2573_ = _args[17];
lean_object* v___y_2574_ = _args[18];
lean_object* v___y_2575_ = _args[19];
_start:
{
size_t v_sz_boxed_2576_; size_t v_i_boxed_2577_; lean_object* v_res_2578_; 
v_sz_boxed_2576_ = lean_unbox_usize(v_sz_2568_);
lean_dec(v_sz_2568_);
v_i_boxed_2577_ = lean_unbox_usize(v_i_2569_);
lean_dec(v_i_2569_);
v_res_2578_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2556_, v_params_2557_, v_alts_2558_, v___x_2559_, v_ism2_2560_, v_motive_2561_, v_val_2562_, v_indName_2563_, v___x_2564_, v___x_2565_, v___x_2566_, v_as_2567_, v_sz_boxed_2576_, v_i_boxed_2577_, v_bs_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec_ref(v_as_2567_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2579_, lean_object* v_params_2580_, lean_object* v___x_2581_, lean_object* v_motive_2582_, lean_object* v_as_2583_, size_t v_sz_2584_, size_t v_i_2585_, lean_object* v_bs_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; 
v___x_2592_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2579_, v_params_2580_, v___x_2581_, v_motive_2582_, v_sz_2584_, v_i_2585_, v_bs_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
return v___x_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2593_, lean_object* v_params_2594_, lean_object* v___x_2595_, lean_object* v_motive_2596_, lean_object* v_as_2597_, lean_object* v_sz_2598_, lean_object* v_i_2599_, lean_object* v_bs_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
size_t v_sz_boxed_2606_; size_t v_i_boxed_2607_; lean_object* v_res_2608_; 
v_sz_boxed_2606_ = lean_unbox_usize(v_sz_2598_);
lean_dec(v_sz_2598_);
v_i_boxed_2607_ = lean_unbox_usize(v_i_2599_);
lean_dec(v_i_2599_);
v_res_2608_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2593_, v_params_2594_, v___x_2595_, v_motive_2596_, v_as_2597_, v_sz_boxed_2606_, v_i_boxed_2607_, v_bs_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_as_2597_);
lean_dec_ref(v_params_2594_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2609_, uint8_t v_s_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2609_, v_s_2610_, v___y_2612_, v___y_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2617_, lean_object* v_s_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
uint8_t v_s_boxed_2624_; lean_object* v_res_2625_; 
v_s_boxed_2624_ = lean_unbox(v_s_2618_);
v_res_2625_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2617_, v_s_boxed_2624_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_);
lean_dec(v___y_2622_);
lean_dec_ref(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2626_, lean_object* v_constName_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2634_, lean_object* v_constName_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2634_, v_constName_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2642_, lean_object* v_attrName_2643_, lean_object* v_declName_2644_, lean_object* v_asyncPrefix_x3f_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2643_, v_declName_2644_, v_asyncPrefix_x3f_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2652_, lean_object* v_attrName_2653_, lean_object* v_declName_2654_, lean_object* v_asyncPrefix_x3f_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2652_, v_attrName_2653_, v_declName_2654_, v_asyncPrefix_x3f_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2662_, lean_object* v_attrName_2663_, lean_object* v_declName_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2663_, v_declName_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2671_, lean_object* v_attrName_2672_, lean_object* v_declName_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2671_, v_attrName_2672_, v_declName_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2680_, lean_object* v_ref_2681_, lean_object* v_constName_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v___x_2688_; 
v___x_2688_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2681_, v_constName_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
return v___x_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2689_, lean_object* v_ref_2690_, lean_object* v_constName_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_){
_start:
{
lean_object* v_res_2697_; 
v_res_2697_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2689_, v_ref_2690_, v_constName_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v_ref_2690_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2698_, lean_object* v_msg_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_){
_start:
{
lean_object* v___x_2705_; 
v___x_2705_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2706_, lean_object* v_msg_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2706_, v_msg_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2714_, lean_object* v_ref_2715_, lean_object* v_msg_2716_, lean_object* v_declHint_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2715_, v_msg_2716_, v_declHint_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2724_, lean_object* v_ref_2725_, lean_object* v_msg_2726_, lean_object* v_declHint_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2724_, v_ref_2725_, v_msg_2726_, v_declHint_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v_ref_2725_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2734_, lean_object* v_declHint_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2734_, v_declHint_2735_, v___y_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2742_, lean_object* v_declHint_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2742_, v_declHint_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2750_, lean_object* v_ref_2751_, lean_object* v_msg_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2751_, v_msg_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2759_, lean_object* v_ref_2760_, lean_object* v_msg_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2759_, v_ref_2760_, v_msg_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v___y_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v_ref_2760_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2768_, lean_object* v___y_2769_){
_start:
{
uint8_t v___x_2771_; 
v___x_2771_ = l_Lean_Expr_hasMVar(v_e_2768_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_e_2768_);
return v___x_2772_;
}
else
{
lean_object* v___x_2773_; lean_object* v_mctx_2774_; lean_object* v___x_2775_; lean_object* v_fst_2776_; lean_object* v_snd_2777_; lean_object* v___x_2778_; lean_object* v_cache_2779_; lean_object* v_zetaDeltaFVarIds_2780_; lean_object* v_postponed_2781_; lean_object* v_diag_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2791_; 
v___x_2773_ = lean_st_ref_get(v___y_2769_);
v_mctx_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc_ref(v_mctx_2774_);
lean_dec(v___x_2773_);
v___x_2775_ = l_Lean_instantiateMVarsCore(v_mctx_2774_, v_e_2768_);
v_fst_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_fst_2776_);
v_snd_2777_ = lean_ctor_get(v___x_2775_, 1);
lean_inc(v_snd_2777_);
lean_dec_ref(v___x_2775_);
v___x_2778_ = lean_st_ref_take(v___y_2769_);
v_cache_2779_ = lean_ctor_get(v___x_2778_, 1);
v_zetaDeltaFVarIds_2780_ = lean_ctor_get(v___x_2778_, 2);
v_postponed_2781_ = lean_ctor_get(v___x_2778_, 3);
v_diag_2782_ = lean_ctor_get(v___x_2778_, 4);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2791_ == 0)
{
lean_object* v_unused_2792_; 
v_unused_2792_ = lean_ctor_get(v___x_2778_, 0);
lean_dec(v_unused_2792_);
v___x_2784_ = v___x_2778_;
v_isShared_2785_ = v_isSharedCheck_2791_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_diag_2782_);
lean_inc(v_postponed_2781_);
lean_inc(v_zetaDeltaFVarIds_2780_);
lean_inc(v_cache_2779_);
lean_dec(v___x_2778_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2791_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v_snd_2777_);
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_snd_2777_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v_cache_2779_);
lean_ctor_set(v_reuseFailAlloc_2790_, 2, v_zetaDeltaFVarIds_2780_);
lean_ctor_set(v_reuseFailAlloc_2790_, 3, v_postponed_2781_);
lean_ctor_set(v_reuseFailAlloc_2790_, 4, v_diag_2782_);
v___x_2787_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_st_ref_set(v___y_2769_, v___x_2787_);
v___x_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2789_, 0, v_fst_2776_);
return v___x_2789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2793_, v___y_2794_);
lean_dec(v___y_2794_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2797_, v___y_2799_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2811_, lean_object* v_info_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v___x_2816_; lean_object* v_env_2817_; lean_object* v_nextMacroScope_2818_; lean_object* v_ngen_2819_; lean_object* v_auxDeclNGen_2820_; lean_object* v_traceState_2821_; lean_object* v_messages_2822_; lean_object* v_infoState_2823_; lean_object* v_snapshotTasks_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2851_; 
v___x_2816_ = lean_st_ref_take(v___y_2814_);
v_env_2817_ = lean_ctor_get(v___x_2816_, 0);
v_nextMacroScope_2818_ = lean_ctor_get(v___x_2816_, 1);
v_ngen_2819_ = lean_ctor_get(v___x_2816_, 2);
v_auxDeclNGen_2820_ = lean_ctor_get(v___x_2816_, 3);
v_traceState_2821_ = lean_ctor_get(v___x_2816_, 4);
v_messages_2822_ = lean_ctor_get(v___x_2816_, 6);
v_infoState_2823_ = lean_ctor_get(v___x_2816_, 7);
v_snapshotTasks_2824_ = lean_ctor_get(v___x_2816_, 8);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; 
v_unused_2852_ = lean_ctor_get(v___x_2816_, 5);
lean_dec(v_unused_2852_);
v___x_2826_ = v___x_2816_;
v_isShared_2827_ = v_isSharedCheck_2851_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_snapshotTasks_2824_);
lean_inc(v_infoState_2823_);
lean_inc(v_messages_2822_);
lean_inc(v_traceState_2821_);
lean_inc(v_auxDeclNGen_2820_);
lean_inc(v_ngen_2819_);
lean_inc(v_nextMacroScope_2818_);
lean_inc(v_env_2817_);
lean_dec(v___x_2816_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2851_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
v___x_2828_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2817_, v_matcherName_2811_, v_info_2812_);
v___x_2829_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2827_ == 0)
{
lean_ctor_set(v___x_2826_, 5, v___x_2829_);
lean_ctor_set(v___x_2826_, 0, v___x_2828_);
v___x_2831_ = v___x_2826_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2828_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_nextMacroScope_2818_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_ngen_2819_);
lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_auxDeclNGen_2820_);
lean_ctor_set(v_reuseFailAlloc_2850_, 4, v_traceState_2821_);
lean_ctor_set(v_reuseFailAlloc_2850_, 5, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2850_, 6, v_messages_2822_);
lean_ctor_set(v_reuseFailAlloc_2850_, 7, v_infoState_2823_);
lean_ctor_set(v_reuseFailAlloc_2850_, 8, v_snapshotTasks_2824_);
v___x_2831_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v_mctx_2834_; lean_object* v_zetaDeltaFVarIds_2835_; lean_object* v_postponed_2836_; lean_object* v_diag_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2848_; 
v___x_2832_ = lean_st_ref_set(v___y_2814_, v___x_2831_);
v___x_2833_ = lean_st_ref_take(v___y_2813_);
v_mctx_2834_ = lean_ctor_get(v___x_2833_, 0);
v_zetaDeltaFVarIds_2835_ = lean_ctor_get(v___x_2833_, 2);
v_postponed_2836_ = lean_ctor_get(v___x_2833_, 3);
v_diag_2837_ = lean_ctor_get(v___x_2833_, 4);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2848_ == 0)
{
lean_object* v_unused_2849_; 
v_unused_2849_ = lean_ctor_get(v___x_2833_, 1);
lean_dec(v_unused_2849_);
v___x_2839_ = v___x_2833_;
v_isShared_2840_ = v_isSharedCheck_2848_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_diag_2837_);
lean_inc(v_postponed_2836_);
lean_inc(v_zetaDeltaFVarIds_2835_);
lean_inc(v_mctx_2834_);
lean_dec(v___x_2833_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2848_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2841_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v___x_2841_);
v___x_2843_ = v___x_2839_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_mctx_2834_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2847_, 2, v_zetaDeltaFVarIds_2835_);
lean_ctor_set(v_reuseFailAlloc_2847_, 3, v_postponed_2836_);
lean_ctor_set(v_reuseFailAlloc_2847_, 4, v_diag_2837_);
v___x_2843_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2844_ = lean_st_ref_set(v___y_2813_, v___x_2843_);
v___x_2845_ = lean_box(0);
v___x_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2845_);
return v___x_2846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2853_, lean_object* v_info_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_){
_start:
{
lean_object* v_res_2858_; 
v_res_2858_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2853_, v_info_2854_, v___y_2855_, v___y_2856_);
lean_dec(v___y_2856_);
lean_dec(v___y_2855_);
return v_res_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2859_, lean_object* v_info_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2859_, v_info_2860_, v___y_2862_, v___y_2864_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2867_, lean_object* v_info_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2867_, v_info_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_);
lean_dec(v___y_2872_);
lean_dec_ref(v___y_2871_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2875_, lean_object* v___x_2876_, lean_object* v_newEqs1_2877_, uint8_t v___x_2878_, uint8_t v___x_2879_, uint8_t v___x_2880_, lean_object* v_ism1_x27_2881_, lean_object* v_ism2_x27_2882_, lean_object* v_newRefls1_2883_, lean_object* v_newEqs2_2884_, lean_object* v_newRefls2_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2891_ = l_Lean_mkAppN(v_motive_2875_, v___x_2876_);
v___x_2892_ = l_Array_append___redArg(v_newEqs1_2877_, v_newEqs2_2884_);
v___x_2893_ = l_Lean_Meta_mkForallFVars(v___x_2892_, v___x_2891_, v___x_2878_, v___x_2879_, v___x_2879_, v___x_2880_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec_ref(v___x_2892_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = l_Array_append___redArg(v_ism1_x27_2881_, v_ism2_x27_2882_);
v___x_2896_ = l_Lean_Meta_mkLambdaFVars(v___x_2895_, v_a_2894_, v___x_2878_, v___x_2879_, v___x_2878_, v___x_2879_, v___x_2880_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec_ref(v___x_2895_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2906_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2899_ = v___x_2896_;
v_isShared_2900_ = v_isSharedCheck_2906_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2896_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2906_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2904_; 
v___x_2901_ = l_Array_append___redArg(v_newRefls1_2883_, v_newRefls2_2885_);
v___x_2902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2902_, 0, v_a_2897_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 0, v___x_2902_);
v___x_2904_ = v___x_2899_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
else
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
lean_dec_ref(v_newRefls1_2883_);
v_a_2907_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2896_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2896_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec_ref(v_newRefls1_2883_);
lean_dec_ref(v_ism1_x27_2881_);
v_a_2915_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2893_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2893_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2923_, lean_object* v___x_2924_, lean_object* v_newEqs1_2925_, lean_object* v___x_2926_, lean_object* v___x_2927_, lean_object* v___x_2928_, lean_object* v_ism1_x27_2929_, lean_object* v_ism2_x27_2930_, lean_object* v_newRefls1_2931_, lean_object* v_newEqs2_2932_, lean_object* v_newRefls2_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
uint8_t v___x_15166__boxed_2939_; uint8_t v___x_15167__boxed_2940_; uint8_t v___x_15168__boxed_2941_; lean_object* v_res_2942_; 
v___x_15166__boxed_2939_ = lean_unbox(v___x_2926_);
v___x_15167__boxed_2940_ = lean_unbox(v___x_2927_);
v___x_15168__boxed_2941_ = lean_unbox(v___x_2928_);
v_res_2942_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2923_, v___x_2924_, v_newEqs1_2925_, v___x_15166__boxed_2939_, v___x_15167__boxed_2940_, v___x_15168__boxed_2941_, v_ism1_x27_2929_, v_ism2_x27_2930_, v_newRefls1_2931_, v_newEqs2_2932_, v_newRefls2_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec_ref(v_newRefls2_2933_);
lean_dec_ref(v_newEqs2_2932_);
lean_dec_ref(v_ism2_x27_2930_);
lean_dec_ref(v___x_2924_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2943_, lean_object* v___x_2944_, uint8_t v___x_2945_, uint8_t v___x_2946_, uint8_t v___x_2947_, lean_object* v_ism1_x27_2948_, lean_object* v_ism2_x27_2949_, lean_object* v_is_2950_, lean_object* v___x_2951_, lean_object* v_newEqs1_2952_, lean_object* v_newRefls1_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___f_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2959_ = lean_box(v___x_2945_);
v___x_2960_ = lean_box(v___x_2946_);
v___x_2961_ = lean_box(v___x_2947_);
lean_inc_ref(v_ism2_x27_2949_);
v___f_2962_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2962_, 0, v_motive_2943_);
lean_closure_set(v___f_2962_, 1, v___x_2944_);
lean_closure_set(v___f_2962_, 2, v_newEqs1_2952_);
lean_closure_set(v___f_2962_, 3, v___x_2959_);
lean_closure_set(v___f_2962_, 4, v___x_2960_);
lean_closure_set(v___f_2962_, 5, v___x_2961_);
lean_closure_set(v___f_2962_, 6, v_ism1_x27_2948_);
lean_closure_set(v___f_2962_, 7, v_ism2_x27_2949_);
lean_closure_set(v___f_2962_, 8, v_newRefls1_2953_);
v___x_2963_ = lean_array_push(v_is_2950_, v___x_2951_);
v___x_2964_ = l_Lean_Meta_withNewEqs___redArg(v___x_2963_, v_ism2_x27_2949_, v___f_2962_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2965_, lean_object* v___x_2966_, lean_object* v___x_2967_, lean_object* v___x_2968_, lean_object* v___x_2969_, lean_object* v_ism1_x27_2970_, lean_object* v_ism2_x27_2971_, lean_object* v_is_2972_, lean_object* v___x_2973_, lean_object* v_newEqs1_2974_, lean_object* v_newRefls1_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
uint8_t v___x_15257__boxed_2981_; uint8_t v___x_15258__boxed_2982_; uint8_t v___x_15259__boxed_2983_; lean_object* v_res_2984_; 
v___x_15257__boxed_2981_ = lean_unbox(v___x_2967_);
v___x_15258__boxed_2982_ = lean_unbox(v___x_2968_);
v___x_15259__boxed_2983_ = lean_unbox(v___x_2969_);
v_res_2984_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2965_, v___x_2966_, v___x_15257__boxed_2981_, v___x_15258__boxed_2982_, v___x_15259__boxed_2983_, v_ism1_x27_2970_, v_ism2_x27_2971_, v_is_2972_, v___x_2973_, v_newEqs1_2974_, v_newRefls1_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_2985_, uint8_t v___x_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Lean_addDecl(v___x_2985_, v___x_2986_, v___y_2989_, v___y_2990_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_2993_, lean_object* v___x_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_){
_start:
{
uint8_t v___x_15299__boxed_3000_; lean_object* v_res_3001_; 
v___x_15299__boxed_3000_ = lean_unbox(v___x_2994_);
v_res_3001_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_2993_, v___x_15299__boxed_3000_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
return v_res_3001_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3004_ = l_Lean_stringToMessageData(v___x_3003_);
return v___x_3004_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3007_ = l_Lean_stringToMessageData(v___x_3006_);
return v___x_3007_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = lean_box(0);
v___x_3014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3015_ = l_Lean_mkConst(v___x_3014_, v___x_3013_);
return v___x_3015_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3018_ = l_Lean_stringToMessageData(v___x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3019_, lean_object* v_a_3020_, lean_object* v___x_3021_, lean_object* v_zs1_3022_, lean_object* v_snd_3023_, uint8_t v___x_3024_, uint8_t v___x_3025_, uint8_t v___x_3026_, lean_object* v_alts_3027_, lean_object* v_zs2_3028_, lean_object* v___ctorRet2_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = lean_array_get_borrowed(v___x_3019_, v_a_3020_, v___x_3021_);
lean_inc_ref(v_zs1_3022_);
v___x_3036_ = l_Array_append___redArg(v_zs1_3022_, v_zs2_3028_);
lean_inc(v___x_3035_);
v___x_3037_ = l_Lean_Meta_instantiateForall(v___x_3035_, v___x_3036_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v_a_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v___x_3037_, 1);
v___x_3039_ = lean_box(0);
v___x_3040_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3038_, v___x_3039_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
v___x_3042_ = l_Lean_Expr_mvarId_x21(v_a_3041_);
v___x_3043_ = lean_array_get_size(v_snd_3023_);
v___x_3044_ = lean_box(0);
v___x_3045_ = lean_box(0);
lean_inc_ref(v___y_3032_);
v___x_3046_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3043_, v___x_3042_, v___x_3044_, v___x_3045_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3046_, 1);
if (lean_obj_tag(v_a_3047_) == 1)
{
lean_object* v_val_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3095_; 
v_val_3048_ = lean_ctor_get(v_a_3047_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v_a_3047_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3050_ = v_a_3047_;
v_isShared_3051_ = v_isSharedCheck_3095_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_val_3048_);
lean_dec(v_a_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3095_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v_fst_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3093_; 
v_fst_3052_ = lean_ctor_get(v_val_3048_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_val_3048_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; 
v_unused_3094_ = lean_ctor_get(v_val_3048_, 1);
lean_dec(v_unused_3094_);
v___x_3054_ = v_val_3048_;
v_isShared_3055_ = v_isSharedCheck_3093_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_fst_3052_);
lean_dec(v_val_3048_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3093_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___y_3057_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; uint8_t v___x_3088_; 
v___x_3085_ = lean_array_get_borrowed(v___x_3019_, v_alts_3027_, v___x_3021_);
v___x_3086_ = lean_array_get_size(v_zs1_3022_);
lean_dec_ref(v_zs1_3022_);
v___x_3087_ = lean_unsigned_to_nat(0u);
v___x_3088_ = lean_nat_dec_eq(v___x_3086_, v___x_3087_);
if (v___x_3088_ == 0)
{
lean_inc(v___x_3085_);
v___y_3057_ = v___x_3085_;
goto v___jp_3056_;
}
else
{
lean_object* v___x_3089_; uint8_t v___x_3090_; 
v___x_3089_ = lean_array_get_size(v_zs2_3028_);
v___x_3090_ = lean_nat_dec_eq(v___x_3089_, v___x_3087_);
if (v___x_3090_ == 0)
{
lean_inc(v___x_3085_);
v___y_3057_ = v___x_3085_;
goto v___jp_3056_;
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3091_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3085_);
v___x_3092_ = l_Lean_Expr_app___override(v___x_3085_, v___x_3091_);
v___y_3057_ = v___x_3092_;
goto v___jp_3056_;
}
}
v___jp_3056_:
{
uint8_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = 0;
v___x_3059_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3059_, 0, v___x_3058_);
lean_ctor_set_uint8(v___x_3059_, 1, v___x_3024_);
lean_ctor_set_uint8(v___x_3059_, 2, v___x_3025_);
lean_ctor_set_uint8(v___x_3059_, 3, v___x_3024_);
lean_inc_ref(v___y_3057_);
lean_inc(v_fst_3052_);
v___x_3060_ = l_Lean_MVarId_apply(v_fst_3052_, v___y_3057_, v___x_3059_, v___x_3045_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
if (lean_obj_tag(v_a_3061_) == 0)
{
lean_object* v___x_3062_; 
lean_dec_ref(v___y_3057_);
lean_del_object(v___x_3054_);
lean_dec(v_fst_3052_);
lean_del_object(v___x_3050_);
v___x_3062_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3041_, v___y_3031_);
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_object* v_a_3063_; lean_object* v___x_3064_; 
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v___x_3064_ = l_Lean_Meta_mkLambdaFVars(v___x_3036_, v_a_3063_, v___x_3025_, v___x_3024_, v___x_3025_, v___x_3024_, v___x_3026_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
lean_dec_ref(v___x_3036_);
return v___x_3064_;
}
else
{
lean_dec_ref(v___x_3036_);
return v___x_3062_;
}
}
else
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3068_; 
lean_dec(v_a_3061_);
lean_dec(v_a_3041_);
lean_dec_ref(v___x_3036_);
v___x_3065_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3066_ = l_Lean_MessageData_ofExpr(v___y_3057_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set_tag(v___x_3054_, 7);
lean_ctor_set(v___x_3054_, 1, v___x_3066_);
lean_ctor_set(v___x_3054_, 0, v___x_3065_);
v___x_3068_ = v___x_3054_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3065_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v___x_3066_);
v___x_3068_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3072_; 
v___x_3069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3068_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v_fst_3052_);
v___x_3072_ = v___x_3050_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_fst_3052_);
v___x_3072_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3070_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3073_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
return v___x_3074_;
}
}
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_dec_ref(v___y_3057_);
lean_del_object(v___x_3054_);
lean_dec(v_fst_3052_);
lean_del_object(v___x_3050_);
lean_dec(v_a_3041_);
lean_dec_ref(v___x_3036_);
v_a_3077_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3060_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3060_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; 
lean_dec(v_a_3047_);
lean_dec(v_a_3041_);
lean_dec_ref(v___x_3036_);
lean_dec_ref(v_zs1_3022_);
v___x_3096_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3097_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3096_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
return v___x_3097_;
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v_a_3041_);
lean_dec_ref(v___x_3036_);
lean_dec_ref(v_zs1_3022_);
v_a_3098_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3046_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3046_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
else
{
lean_dec_ref(v___x_3036_);
lean_dec_ref(v_zs1_3022_);
return v___x_3040_;
}
}
else
{
lean_dec_ref(v___x_3036_);
lean_dec_ref(v_zs1_3022_);
return v___x_3037_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3106_, lean_object* v_a_3107_, lean_object* v___x_3108_, lean_object* v_zs1_3109_, lean_object* v_snd_3110_, lean_object* v___x_3111_, lean_object* v___x_3112_, lean_object* v___x_3113_, lean_object* v_alts_3114_, lean_object* v_zs2_3115_, lean_object* v___ctorRet2_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_){
_start:
{
uint8_t v___x_15359__boxed_3122_; uint8_t v___x_15360__boxed_3123_; uint8_t v___x_15361__boxed_3124_; lean_object* v_res_3125_; 
v___x_15359__boxed_3122_ = lean_unbox(v___x_3111_);
v___x_15360__boxed_3123_ = lean_unbox(v___x_3112_);
v___x_15361__boxed_3124_ = lean_unbox(v___x_3113_);
v_res_3125_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3106_, v_a_3107_, v___x_3108_, v_zs1_3109_, v_snd_3110_, v___x_15359__boxed_3122_, v___x_15360__boxed_3123_, v___x_15361__boxed_3124_, v_alts_3114_, v_zs2_3115_, v___ctorRet2_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec_ref(v___ctorRet2_3116_);
lean_dec_ref(v_zs2_3115_);
lean_dec_ref(v_alts_3114_);
lean_dec_ref(v_snd_3110_);
lean_dec(v___x_3108_);
lean_dec_ref(v_a_3107_);
lean_dec_ref(v___x_3106_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3126_, lean_object* v_a_3127_, lean_object* v___x_3128_, lean_object* v_snd_3129_, uint8_t v___x_3130_, uint8_t v___x_3131_, uint8_t v___x_3132_, lean_object* v_alts_3133_, lean_object* v_a_3134_, lean_object* v_zs1_3135_, lean_object* v___ctorRet1_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___f_3145_; lean_object* v___x_3146_; 
v___x_3142_ = lean_box(v___x_3130_);
v___x_3143_ = lean_box(v___x_3131_);
v___x_3144_ = lean_box(v___x_3132_);
v___f_3145_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3145_, 0, v___x_3126_);
lean_closure_set(v___f_3145_, 1, v_a_3127_);
lean_closure_set(v___f_3145_, 2, v___x_3128_);
lean_closure_set(v___f_3145_, 3, v_zs1_3135_);
lean_closure_set(v___f_3145_, 4, v_snd_3129_);
lean_closure_set(v___f_3145_, 5, v___x_3142_);
lean_closure_set(v___f_3145_, 6, v___x_3143_);
lean_closure_set(v___f_3145_, 7, v___x_3144_);
lean_closure_set(v___f_3145_, 8, v_alts_3133_);
v___x_3146_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3134_, v___f_3145_, v___x_3131_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3147_, lean_object* v_a_3148_, lean_object* v___x_3149_, lean_object* v_snd_3150_, lean_object* v___x_3151_, lean_object* v___x_3152_, lean_object* v___x_3153_, lean_object* v_alts_3154_, lean_object* v_a_3155_, lean_object* v_zs1_3156_, lean_object* v___ctorRet1_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
uint8_t v___x_15558__boxed_3163_; uint8_t v___x_15559__boxed_3164_; uint8_t v___x_15560__boxed_3165_; lean_object* v_res_3166_; 
v___x_15558__boxed_3163_ = lean_unbox(v___x_3151_);
v___x_15559__boxed_3164_ = lean_unbox(v___x_3152_);
v___x_15560__boxed_3165_ = lean_unbox(v___x_3153_);
v_res_3166_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3147_, v_a_3148_, v___x_3149_, v_snd_3150_, v___x_15558__boxed_3163_, v___x_15559__boxed_3164_, v___x_15560__boxed_3165_, v_alts_3154_, v_a_3155_, v_zs1_3156_, v___ctorRet1_3157_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec_ref(v___ctorRet1_3157_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3167_, lean_object* v_params_3168_, lean_object* v_a_3169_, lean_object* v_snd_3170_, lean_object* v_alts_3171_, size_t v_sz_3172_, size_t v_i_3173_, lean_object* v_bs_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
uint8_t v___x_3180_; 
v___x_3180_ = lean_usize_dec_lt(v_i_3173_, v_sz_3172_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
lean_dec_ref(v_alts_3171_);
lean_dec_ref(v_snd_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_tail_3167_);
v___x_3181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3181_, 0, v_bs_3174_);
return v___x_3181_;
}
else
{
lean_object* v_v_3182_; lean_object* v___x_3183_; lean_object* v_bs_x27_3184_; lean_object* v___y_3186_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v_v_3182_ = lean_array_uget(v_bs_3174_, v_i_3173_);
v___x_3183_ = lean_unsigned_to_nat(0u);
v_bs_x27_3184_ = lean_array_uset(v_bs_3174_, v_i_3173_, v___x_3183_);
lean_inc(v_tail_3167_);
v___x_3200_ = l_Lean_mkConst(v_v_3182_, v_tail_3167_);
v___x_3201_ = l_Lean_mkAppN(v___x_3200_, v_params_3168_);
lean_inc(v___y_3178_);
lean_inc_ref(v___y_3177_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
v___x_3202_ = lean_infer_type(v___x_3201_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; uint8_t v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___f_3211_; lean_object* v___x_3212_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc_n(v_a_3203_, 2);
lean_dec_ref_known(v___x_3202_, 1);
v___x_3204_ = l_Lean_instInhabitedExpr;
v___x_3205_ = 0;
v___x_3206_ = 1;
v___x_3207_ = lean_usize_to_nat(v_i_3173_);
v___x_3208_ = lean_box(v___x_3180_);
v___x_3209_ = lean_box(v___x_3205_);
v___x_3210_ = lean_box(v___x_3206_);
lean_inc_ref(v_alts_3171_);
lean_inc_ref(v_snd_3170_);
lean_inc_ref(v_a_3169_);
v___f_3211_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3211_, 0, v___x_3204_);
lean_closure_set(v___f_3211_, 1, v_a_3169_);
lean_closure_set(v___f_3211_, 2, v___x_3207_);
lean_closure_set(v___f_3211_, 3, v_snd_3170_);
lean_closure_set(v___f_3211_, 4, v___x_3208_);
lean_closure_set(v___f_3211_, 5, v___x_3209_);
lean_closure_set(v___f_3211_, 6, v___x_3210_);
lean_closure_set(v___f_3211_, 7, v_alts_3171_);
lean_closure_set(v___f_3211_, 8, v_a_3203_);
v___x_3212_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3203_, v___f_3211_, v___x_3205_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
v___y_3186_ = v___x_3212_;
goto v___jp_3185_;
}
else
{
v___y_3186_ = v___x_3202_;
goto v___jp_3185_;
}
v___jp_3185_:
{
if (lean_obj_tag(v___y_3186_) == 0)
{
lean_object* v_a_3187_; size_t v___x_3188_; size_t v___x_3189_; lean_object* v___x_3190_; 
v_a_3187_ = lean_ctor_get(v___y_3186_, 0);
lean_inc(v_a_3187_);
lean_dec_ref_known(v___y_3186_, 1);
v___x_3188_ = ((size_t)1ULL);
v___x_3189_ = lean_usize_add(v_i_3173_, v___x_3188_);
v___x_3190_ = lean_array_uset(v_bs_x27_3184_, v_i_3173_, v_a_3187_);
v_i_3173_ = v___x_3189_;
v_bs_3174_ = v___x_3190_;
goto _start;
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_dec_ref(v_bs_x27_3184_);
lean_dec_ref(v_alts_3171_);
lean_dec_ref(v_snd_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_tail_3167_);
v_a_3192_ = lean_ctor_get(v___y_3186_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___y_3186_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___y_3186_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___y_3186_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3213_, lean_object* v_params_3214_, lean_object* v_a_3215_, lean_object* v_snd_3216_, lean_object* v_alts_3217_, lean_object* v_sz_3218_, lean_object* v_i_3219_, lean_object* v_bs_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
size_t v_sz_boxed_3226_; size_t v_i_boxed_3227_; lean_object* v_res_3228_; 
v_sz_boxed_3226_ = lean_unbox_usize(v_sz_3218_);
lean_dec(v_sz_3218_);
v_i_boxed_3227_ = lean_unbox_usize(v_i_3219_);
lean_dec(v_i_3219_);
v_res_3228_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3213_, v_params_3214_, v_a_3215_, v_snd_3216_, v_alts_3217_, v_sz_boxed_3226_, v_i_boxed_3227_, v_bs_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec_ref(v_params_3214_);
return v_res_3228_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_unsigned_to_nat(16u);
v___x_3231_ = lean_mk_array(v___x_3230_, v___x_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3232_, lean_object* v___x_3233_, uint8_t v___x_3234_, uint8_t v___x_3235_, uint8_t v___x_3236_, lean_object* v_ism1_x27_3237_, lean_object* v_is_3238_, lean_object* v___x_3239_, lean_object* v___x_3240_, lean_object* v___x_3241_, lean_object* v___x_3242_, lean_object* v_params_3243_, lean_object* v___x_3244_, lean_object* v___x_3245_, lean_object* v_heq_3246_, lean_object* v_val_3247_, lean_object* v_tail_3248_, lean_object* v_alts_3249_, size_t v_sz_3250_, size_t v___x_3251_, lean_object* v___x_3252_, lean_object* v___x_3253_, lean_object* v_declName_3254_, lean_object* v_levelParams_3255_, lean_object* v_numIndices_3256_, lean_object* v___x_3257_, lean_object* v___x_3258_, lean_object* v_numParams_3259_, lean_object* v_snd_3260_, lean_object* v_ism2_x27_3261_, lean_object* v_x_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___f_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3268_ = lean_box(v___x_3234_);
v___x_3269_ = lean_box(v___x_3235_);
v___x_3270_ = lean_box(v___x_3236_);
lean_inc_ref(v___x_3239_);
lean_inc_ref_n(v_is_3238_, 2);
lean_inc_ref(v_ism1_x27_3237_);
lean_inc_ref(v_motive_3232_);
v___f_3271_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3271_, 0, v_motive_3232_);
lean_closure_set(v___f_3271_, 1, v___x_3233_);
lean_closure_set(v___f_3271_, 2, v___x_3268_);
lean_closure_set(v___f_3271_, 3, v___x_3269_);
lean_closure_set(v___f_3271_, 4, v___x_3270_);
lean_closure_set(v___f_3271_, 5, v_ism1_x27_3237_);
lean_closure_set(v___f_3271_, 6, v_ism2_x27_3261_);
lean_closure_set(v___f_3271_, 7, v_is_3238_);
lean_closure_set(v___f_3271_, 8, v___x_3239_);
lean_inc_ref(v___x_3240_);
v___x_3272_ = lean_array_push(v_is_3238_, v___x_3240_);
v___x_3273_ = l_Lean_Meta_withNewEqs___redArg(v___x_3272_, v_ism1_x27_3237_, v___f_3271_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v_a_3274_; lean_object* v_fst_3275_; lean_object* v_snd_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3377_; 
v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc(v_a_3274_);
lean_dec_ref_known(v___x_3273_, 1);
v_fst_3275_ = lean_ctor_get(v_a_3274_, 0);
v_snd_3276_ = lean_ctor_get(v_a_3274_, 1);
v_isSharedCheck_3377_ = !lean_is_exclusive(v_a_3274_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3278_ = v_a_3274_;
v_isShared_3279_ = v_isSharedCheck_3377_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_snd_3276_);
lean_inc(v_fst_3275_);
lean_dec(v_a_3274_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3377_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3280_ = l_Lean_mkConst(v___x_3241_, v___x_3242_);
v___x_3281_ = l_Lean_mkAppN(v___x_3280_, v_params_3243_);
v___x_3282_ = l_Lean_Expr_app___override(v___x_3281_, v_fst_3275_);
lean_inc_ref(v_is_3238_);
v___x_3283_ = l_Array_append___redArg(v_is_3238_, v___x_3244_);
v___x_3284_ = l_Array_append___redArg(v___x_3283_, v_is_3238_);
v___x_3285_ = l_Array_append___redArg(v___x_3284_, v___x_3245_);
v___x_3286_ = l_Lean_mkAppN(v___x_3282_, v___x_3285_);
lean_dec_ref(v___x_3285_);
lean_inc_ref(v_heq_3246_);
v___x_3287_ = l_Lean_Expr_app___override(v___x_3286_, v_heq_3246_);
v___x_3288_ = l_Lean_InductiveVal_numCtors(v_val_3247_);
lean_inc_ref(v___x_3287_);
v___x_3289_ = l_Lean_Meta_inferArgumentTypesN(v___x_3288_, v___x_3287_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3291_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref_known(v___x_3289_, 1);
lean_inc_ref(v_alts_3249_);
lean_inc(v_snd_3276_);
v___x_3291_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3248_, v_params_3243_, v_a_3290_, v_snd_3276_, v_alts_3249_, v_sz_3250_, v___x_3251_, v___x_3252_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3291_) == 0)
{
lean_object* v_a_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v_a_3292_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_a_3292_);
lean_dec_ref_known(v___x_3291_, 1);
v___x_3293_ = l_Lean_mkAppN(v___x_3287_, v_a_3292_);
lean_dec(v_a_3292_);
v___x_3294_ = l_Lean_mkAppN(v___x_3293_, v_snd_3276_);
lean_dec(v_snd_3276_);
lean_inc_ref(v___x_3253_);
v___x_3295_ = lean_array_push(v___x_3253_, v_motive_3232_);
v___x_3296_ = l_Array_append___redArg(v_params_3243_, v___x_3295_);
lean_dec_ref(v___x_3295_);
v___x_3297_ = l_Array_append___redArg(v___x_3296_, v_is_3238_);
lean_dec_ref(v_is_3238_);
v___x_3298_ = lean_unsigned_to_nat(2u);
v___x_3299_ = lean_mk_empty_array_with_capacity(v___x_3298_);
v___x_3300_ = lean_array_push(v___x_3299_, v___x_3240_);
v___x_3301_ = lean_array_push(v___x_3300_, v___x_3239_);
v___x_3302_ = l_Array_append___redArg(v___x_3297_, v___x_3301_);
lean_dec_ref(v___x_3301_);
v___x_3303_ = lean_array_push(v___x_3253_, v_heq_3246_);
v___x_3304_ = l_Array_append___redArg(v___x_3302_, v___x_3303_);
lean_dec_ref(v___x_3303_);
v___x_3305_ = l_Array_append___redArg(v___x_3304_, v_alts_3249_);
lean_dec_ref(v_alts_3249_);
v___x_3306_ = l_Lean_Meta_mkLambdaFVars(v___x_3305_, v___x_3294_, v___x_3234_, v___x_3235_, v___x_3234_, v___x_3235_, v___x_3236_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec_ref(v___x_3305_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc_n(v_a_3307_, 2);
lean_dec_ref_known(v___x_3306_, 1);
lean_inc(v___y_3266_);
lean_inc_ref(v___y_3265_);
lean_inc(v___y_3264_);
lean_inc_ref(v___y_3263_);
v___x_3308_ = lean_infer_type(v_a_3307_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3344_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref_known(v___x_3308_, 1);
v___x_3310_ = lean_box(1);
lean_inc(v_declName_3254_);
v___x_3311_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3254_, v_levelParams_3255_, v_a_3309_, v_a_3307_, v___x_3310_, v___y_3266_);
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3344_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3344_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 1);
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
lean_object* v___x_3318_; lean_object* v___f_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3329_; 
v___x_3318_ = lean_box(v___x_3234_);
lean_inc_ref(v___x_3317_);
v___f_3319_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3319_, 0, v___x_3317_);
lean_closure_set(v___f_3319_, 1, v___x_3318_);
v___x_3320_ = lean_nat_add(v_numIndices_3256_, v___x_3257_);
lean_inc(v___x_3258_);
v___x_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3258_);
v___x_3322_ = lean_box(0);
v___x_3323_ = lean_mk_empty_array_with_capacity(v___x_3257_);
v___x_3324_ = lean_array_push(v___x_3323_, v___x_3322_);
v___x_3325_ = lean_array_push(v___x_3324_, v___x_3322_);
v___x_3326_ = lean_array_push(v___x_3325_, v___x_3322_);
v___x_3327_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 1, v___x_3327_);
lean_ctor_set(v___x_3278_, 0, v___x_3258_);
v___x_3329_ = v___x_3278_;
goto v_reusejp_3328_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v___x_3327_);
v___x_3329_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3328_;
}
v_reusejp_3328_:
{
lean_object* v___x_3330_; uint8_t v___y_3332_; uint8_t v___x_3341_; 
v___x_3330_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3330_, 0, v_numParams_3259_);
lean_ctor_set(v___x_3330_, 1, v___x_3320_);
lean_ctor_set(v___x_3330_, 2, v_snd_3260_);
lean_ctor_set(v___x_3330_, 3, v___x_3321_);
lean_ctor_set(v___x_3330_, 4, v___x_3326_);
lean_ctor_set(v___x_3330_, 5, v___x_3329_);
v___x_3341_ = l_Lean_isPrivateName(v_declName_3254_);
if (v___x_3341_ == 0)
{
v___y_3332_ = v___x_3235_;
goto v___jp_3331_;
}
else
{
v___y_3332_ = v___x_3234_;
goto v___jp_3331_;
}
v___jp_3331_:
{
lean_object* v___x_3333_; 
v___x_3333_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3319_, v___y_3332_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_dec_ref_known(v___x_3333_, 1);
v___x_3334_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3254_);
v___x_3335_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3334_, v_declName_3254_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v___x_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; 
lean_dec_ref_known(v___x_3335_, 1);
lean_inc_n(v_declName_3254_, 2);
v___x_3336_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3254_, v___x_3330_, v___y_3264_, v___y_3266_);
lean_dec_ref(v___x_3336_);
v___x_3337_ = 0;
v___x_3338_ = l_Lean_Meta_setInlineAttribute(v_declName_3254_, v___x_3337_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3338_) == 0)
{
lean_object* v___x_3339_; 
lean_dec_ref_known(v___x_3338_, 1);
v___x_3339_ = l_Lean_enableRealizationsForConst(v_declName_3254_, v___y_3265_, v___y_3266_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v___x_3340_; 
lean_dec_ref_known(v___x_3339_, 1);
v___x_3340_ = l_Lean_compileDecl(v___x_3317_, v___x_3235_, v___y_3265_, v___y_3266_);
return v___x_3340_;
}
else
{
lean_dec_ref(v___x_3317_);
return v___x_3339_;
}
}
else
{
lean_dec_ref(v___x_3317_);
lean_dec(v_declName_3254_);
return v___x_3338_;
}
}
else
{
lean_dec_ref_known(v___x_3330_, 6);
lean_dec_ref(v___x_3317_);
lean_dec(v_declName_3254_);
return v___x_3335_;
}
}
else
{
lean_dec_ref_known(v___x_3330_, 6);
lean_dec_ref(v___x_3317_);
lean_dec(v_declName_3254_);
return v___x_3333_;
}
}
}
}
}
}
else
{
lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v_a_3307_);
lean_del_object(v___x_3278_);
lean_dec_ref(v_snd_3260_);
lean_dec(v_numParams_3259_);
lean_dec(v___x_3258_);
lean_dec(v_levelParams_3255_);
lean_dec(v_declName_3254_);
v_a_3345_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3308_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3308_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_del_object(v___x_3278_);
lean_dec_ref(v_snd_3260_);
lean_dec(v_numParams_3259_);
lean_dec(v___x_3258_);
lean_dec(v_levelParams_3255_);
lean_dec(v_declName_3254_);
v_a_3353_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3306_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3306_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec_ref(v___x_3287_);
lean_del_object(v___x_3278_);
lean_dec(v_snd_3276_);
lean_dec_ref(v_snd_3260_);
lean_dec(v_numParams_3259_);
lean_dec(v___x_3258_);
lean_dec(v_levelParams_3255_);
lean_dec(v_declName_3254_);
lean_dec_ref(v___x_3253_);
lean_dec_ref(v_alts_3249_);
lean_dec_ref(v_heq_3246_);
lean_dec_ref(v_params_3243_);
lean_dec_ref(v___x_3240_);
lean_dec_ref(v___x_3239_);
lean_dec_ref(v_is_3238_);
lean_dec_ref(v_motive_3232_);
v_a_3361_ = lean_ctor_get(v___x_3291_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3291_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3291_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3291_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3366_; 
if (v_isShared_3364_ == 0)
{
v___x_3366_ = v___x_3363_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v_a_3361_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec_ref(v___x_3287_);
lean_del_object(v___x_3278_);
lean_dec(v_snd_3276_);
lean_dec_ref(v_snd_3260_);
lean_dec(v_numParams_3259_);
lean_dec(v___x_3258_);
lean_dec(v_levelParams_3255_);
lean_dec(v_declName_3254_);
lean_dec_ref(v___x_3253_);
lean_dec_ref(v___x_3252_);
lean_dec_ref(v_alts_3249_);
lean_dec(v_tail_3248_);
lean_dec_ref(v_heq_3246_);
lean_dec_ref(v_params_3243_);
lean_dec_ref(v___x_3240_);
lean_dec_ref(v___x_3239_);
lean_dec_ref(v_is_3238_);
lean_dec_ref(v_motive_3232_);
v_a_3369_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3289_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3289_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
lean_dec_ref(v_snd_3260_);
lean_dec(v_numParams_3259_);
lean_dec(v___x_3258_);
lean_dec(v_levelParams_3255_);
lean_dec(v_declName_3254_);
lean_dec_ref(v___x_3253_);
lean_dec_ref(v___x_3252_);
lean_dec_ref(v_alts_3249_);
lean_dec(v_tail_3248_);
lean_dec_ref(v_heq_3246_);
lean_dec_ref(v_params_3243_);
lean_dec(v___x_3242_);
lean_dec(v___x_3241_);
lean_dec_ref(v___x_3240_);
lean_dec_ref(v___x_3239_);
lean_dec_ref(v_is_3238_);
lean_dec_ref(v_motive_3232_);
v_a_3378_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3273_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3273_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3386_ = _args[0];
lean_object* v___x_3387_ = _args[1];
lean_object* v___x_3388_ = _args[2];
lean_object* v___x_3389_ = _args[3];
lean_object* v___x_3390_ = _args[4];
lean_object* v_ism1_x27_3391_ = _args[5];
lean_object* v_is_3392_ = _args[6];
lean_object* v___x_3393_ = _args[7];
lean_object* v___x_3394_ = _args[8];
lean_object* v___x_3395_ = _args[9];
lean_object* v___x_3396_ = _args[10];
lean_object* v_params_3397_ = _args[11];
lean_object* v___x_3398_ = _args[12];
lean_object* v___x_3399_ = _args[13];
lean_object* v_heq_3400_ = _args[14];
lean_object* v_val_3401_ = _args[15];
lean_object* v_tail_3402_ = _args[16];
lean_object* v_alts_3403_ = _args[17];
lean_object* v_sz_3404_ = _args[18];
lean_object* v___x_3405_ = _args[19];
lean_object* v___x_3406_ = _args[20];
lean_object* v___x_3407_ = _args[21];
lean_object* v_declName_3408_ = _args[22];
lean_object* v_levelParams_3409_ = _args[23];
lean_object* v_numIndices_3410_ = _args[24];
lean_object* v___x_3411_ = _args[25];
lean_object* v___x_3412_ = _args[26];
lean_object* v_numParams_3413_ = _args[27];
lean_object* v_snd_3414_ = _args[28];
lean_object* v_ism2_x27_3415_ = _args[29];
lean_object* v_x_3416_ = _args[30];
lean_object* v___y_3417_ = _args[31];
lean_object* v___y_3418_ = _args[32];
lean_object* v___y_3419_ = _args[33];
lean_object* v___y_3420_ = _args[34];
lean_object* v___y_3421_ = _args[35];
_start:
{
uint8_t v___x_15697__boxed_3422_; uint8_t v___x_15698__boxed_3423_; uint8_t v___x_15699__boxed_3424_; size_t v_sz_boxed_3425_; size_t v___x_15708__boxed_3426_; lean_object* v_res_3427_; 
v___x_15697__boxed_3422_ = lean_unbox(v___x_3388_);
v___x_15698__boxed_3423_ = lean_unbox(v___x_3389_);
v___x_15699__boxed_3424_ = lean_unbox(v___x_3390_);
v_sz_boxed_3425_ = lean_unbox_usize(v_sz_3404_);
lean_dec(v_sz_3404_);
v___x_15708__boxed_3426_ = lean_unbox_usize(v___x_3405_);
lean_dec(v___x_3405_);
v_res_3427_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3386_, v___x_3387_, v___x_15697__boxed_3422_, v___x_15698__boxed_3423_, v___x_15699__boxed_3424_, v_ism1_x27_3391_, v_is_3392_, v___x_3393_, v___x_3394_, v___x_3395_, v___x_3396_, v_params_3397_, v___x_3398_, v___x_3399_, v_heq_3400_, v_val_3401_, v_tail_3402_, v_alts_3403_, v_sz_boxed_3425_, v___x_15708__boxed_3426_, v___x_3406_, v___x_3407_, v_declName_3408_, v_levelParams_3409_, v_numIndices_3410_, v___x_3411_, v___x_3412_, v_numParams_3413_, v_snd_3414_, v_ism2_x27_3415_, v_x_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v_x_3416_);
lean_dec(v___x_3411_);
lean_dec(v_numIndices_3410_);
lean_dec_ref(v_val_3401_);
lean_dec_ref(v___x_3399_);
lean_dec_ref(v___x_3398_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3428_, lean_object* v___x_3429_, uint8_t v___x_3430_, uint8_t v___x_3431_, uint8_t v___x_3432_, lean_object* v_is_3433_, lean_object* v___x_3434_, lean_object* v___x_3435_, lean_object* v___x_3436_, lean_object* v___x_3437_, lean_object* v_params_3438_, lean_object* v___x_3439_, lean_object* v___x_3440_, lean_object* v_heq_3441_, lean_object* v_val_3442_, lean_object* v_tail_3443_, lean_object* v_alts_3444_, size_t v_sz_3445_, size_t v___x_3446_, lean_object* v___x_3447_, lean_object* v___x_3448_, lean_object* v_declName_3449_, lean_object* v_levelParams_3450_, lean_object* v_numIndices_3451_, lean_object* v___x_3452_, lean_object* v___x_3453_, lean_object* v_numParams_3454_, lean_object* v_snd_3455_, lean_object* v___x_3456_, lean_object* v___x_3457_, lean_object* v_ism1_x27_3458_, lean_object* v_x_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___f_3470_; lean_object* v___x_3471_; 
v___x_3465_ = lean_box(v___x_3430_);
v___x_3466_ = lean_box(v___x_3431_);
v___x_3467_ = lean_box(v___x_3432_);
v___x_3468_ = lean_box_usize(v_sz_3445_);
v___x_3469_ = lean_box_usize(v___x_3446_);
v___f_3470_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3470_, 0, v_motive_3428_);
lean_closure_set(v___f_3470_, 1, v___x_3429_);
lean_closure_set(v___f_3470_, 2, v___x_3465_);
lean_closure_set(v___f_3470_, 3, v___x_3466_);
lean_closure_set(v___f_3470_, 4, v___x_3467_);
lean_closure_set(v___f_3470_, 5, v_ism1_x27_3458_);
lean_closure_set(v___f_3470_, 6, v_is_3433_);
lean_closure_set(v___f_3470_, 7, v___x_3434_);
lean_closure_set(v___f_3470_, 8, v___x_3435_);
lean_closure_set(v___f_3470_, 9, v___x_3436_);
lean_closure_set(v___f_3470_, 10, v___x_3437_);
lean_closure_set(v___f_3470_, 11, v_params_3438_);
lean_closure_set(v___f_3470_, 12, v___x_3439_);
lean_closure_set(v___f_3470_, 13, v___x_3440_);
lean_closure_set(v___f_3470_, 14, v_heq_3441_);
lean_closure_set(v___f_3470_, 15, v_val_3442_);
lean_closure_set(v___f_3470_, 16, v_tail_3443_);
lean_closure_set(v___f_3470_, 17, v_alts_3444_);
lean_closure_set(v___f_3470_, 18, v___x_3468_);
lean_closure_set(v___f_3470_, 19, v___x_3469_);
lean_closure_set(v___f_3470_, 20, v___x_3447_);
lean_closure_set(v___f_3470_, 21, v___x_3448_);
lean_closure_set(v___f_3470_, 22, v_declName_3449_);
lean_closure_set(v___f_3470_, 23, v_levelParams_3450_);
lean_closure_set(v___f_3470_, 24, v_numIndices_3451_);
lean_closure_set(v___f_3470_, 25, v___x_3452_);
lean_closure_set(v___f_3470_, 26, v___x_3453_);
lean_closure_set(v___f_3470_, 27, v_numParams_3454_);
lean_closure_set(v___f_3470_, 28, v_snd_3455_);
v___x_3471_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3456_, v___x_3457_, v___f_3470_, v___x_3430_, v___x_3430_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3472_ = _args[0];
lean_object* v___x_3473_ = _args[1];
lean_object* v___x_3474_ = _args[2];
lean_object* v___x_3475_ = _args[3];
lean_object* v___x_3476_ = _args[4];
lean_object* v_is_3477_ = _args[5];
lean_object* v___x_3478_ = _args[6];
lean_object* v___x_3479_ = _args[7];
lean_object* v___x_3480_ = _args[8];
lean_object* v___x_3481_ = _args[9];
lean_object* v_params_3482_ = _args[10];
lean_object* v___x_3483_ = _args[11];
lean_object* v___x_3484_ = _args[12];
lean_object* v_heq_3485_ = _args[13];
lean_object* v_val_3486_ = _args[14];
lean_object* v_tail_3487_ = _args[15];
lean_object* v_alts_3488_ = _args[16];
lean_object* v_sz_3489_ = _args[17];
lean_object* v___x_3490_ = _args[18];
lean_object* v___x_3491_ = _args[19];
lean_object* v___x_3492_ = _args[20];
lean_object* v_declName_3493_ = _args[21];
lean_object* v_levelParams_3494_ = _args[22];
lean_object* v_numIndices_3495_ = _args[23];
lean_object* v___x_3496_ = _args[24];
lean_object* v___x_3497_ = _args[25];
lean_object* v_numParams_3498_ = _args[26];
lean_object* v_snd_3499_ = _args[27];
lean_object* v___x_3500_ = _args[28];
lean_object* v___x_3501_ = _args[29];
lean_object* v_ism1_x27_3502_ = _args[30];
lean_object* v_x_3503_ = _args[31];
lean_object* v___y_3504_ = _args[32];
lean_object* v___y_3505_ = _args[33];
lean_object* v___y_3506_ = _args[34];
lean_object* v___y_3507_ = _args[35];
lean_object* v___y_3508_ = _args[36];
_start:
{
uint8_t v___x_16019__boxed_3509_; uint8_t v___x_16020__boxed_3510_; uint8_t v___x_16021__boxed_3511_; size_t v_sz_boxed_3512_; size_t v___x_16030__boxed_3513_; lean_object* v_res_3514_; 
v___x_16019__boxed_3509_ = lean_unbox(v___x_3474_);
v___x_16020__boxed_3510_ = lean_unbox(v___x_3475_);
v___x_16021__boxed_3511_ = lean_unbox(v___x_3476_);
v_sz_boxed_3512_ = lean_unbox_usize(v_sz_3489_);
lean_dec(v_sz_3489_);
v___x_16030__boxed_3513_ = lean_unbox_usize(v___x_3490_);
lean_dec(v___x_3490_);
v_res_3514_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3472_, v___x_3473_, v___x_16019__boxed_3509_, v___x_16020__boxed_3510_, v___x_16021__boxed_3511_, v_is_3477_, v___x_3478_, v___x_3479_, v___x_3480_, v___x_3481_, v_params_3482_, v___x_3483_, v___x_3484_, v_heq_3485_, v_val_3486_, v_tail_3487_, v_alts_3488_, v_sz_boxed_3512_, v___x_16030__boxed_3513_, v___x_3491_, v___x_3492_, v_declName_3493_, v_levelParams_3494_, v_numIndices_3495_, v___x_3496_, v___x_3497_, v_numParams_3498_, v_snd_3499_, v___x_3500_, v___x_3501_, v_ism1_x27_3502_, v_x_3503_, v___y_3504_, v___y_3505_, v___y_3506_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3506_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec_ref(v_x_3503_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3515_, lean_object* v___x_3516_, lean_object* v_motive_3517_, lean_object* v___x_3518_, uint8_t v___x_3519_, uint8_t v___x_3520_, uint8_t v___x_3521_, lean_object* v_is_3522_, lean_object* v___x_3523_, lean_object* v___x_3524_, lean_object* v___x_3525_, lean_object* v___x_3526_, lean_object* v_params_3527_, lean_object* v___x_3528_, lean_object* v___x_3529_, lean_object* v_heq_3530_, lean_object* v_val_3531_, lean_object* v_tail_3532_, size_t v_sz_3533_, size_t v___x_3534_, lean_object* v___x_3535_, lean_object* v___x_3536_, lean_object* v_declName_3537_, lean_object* v_levelParams_3538_, lean_object* v___x_3539_, lean_object* v___x_3540_, lean_object* v_numParams_3541_, lean_object* v_snd_3542_, lean_object* v___x_3543_, lean_object* v_alts_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_){
_start:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___f_3557_; lean_object* v___x_3558_; 
v___x_3550_ = lean_nat_add(v_numIndices_3515_, v___x_3516_);
v___x_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
v___x_3552_ = lean_box(v___x_3519_);
v___x_3553_ = lean_box(v___x_3520_);
v___x_3554_ = lean_box(v___x_3521_);
v___x_3555_ = lean_box_usize(v_sz_3533_);
v___x_3556_ = lean_box_usize(v___x_3534_);
lean_inc_ref(v___x_3551_);
lean_inc_ref(v___x_3543_);
v___f_3557_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3557_, 0, v_motive_3517_);
lean_closure_set(v___f_3557_, 1, v___x_3518_);
lean_closure_set(v___f_3557_, 2, v___x_3552_);
lean_closure_set(v___f_3557_, 3, v___x_3553_);
lean_closure_set(v___f_3557_, 4, v___x_3554_);
lean_closure_set(v___f_3557_, 5, v_is_3522_);
lean_closure_set(v___f_3557_, 6, v___x_3523_);
lean_closure_set(v___f_3557_, 7, v___x_3524_);
lean_closure_set(v___f_3557_, 8, v___x_3525_);
lean_closure_set(v___f_3557_, 9, v___x_3526_);
lean_closure_set(v___f_3557_, 10, v_params_3527_);
lean_closure_set(v___f_3557_, 11, v___x_3528_);
lean_closure_set(v___f_3557_, 12, v___x_3529_);
lean_closure_set(v___f_3557_, 13, v_heq_3530_);
lean_closure_set(v___f_3557_, 14, v_val_3531_);
lean_closure_set(v___f_3557_, 15, v_tail_3532_);
lean_closure_set(v___f_3557_, 16, v_alts_3544_);
lean_closure_set(v___f_3557_, 17, v___x_3555_);
lean_closure_set(v___f_3557_, 18, v___x_3556_);
lean_closure_set(v___f_3557_, 19, v___x_3535_);
lean_closure_set(v___f_3557_, 20, v___x_3536_);
lean_closure_set(v___f_3557_, 21, v_declName_3537_);
lean_closure_set(v___f_3557_, 22, v_levelParams_3538_);
lean_closure_set(v___f_3557_, 23, v_numIndices_3515_);
lean_closure_set(v___f_3557_, 24, v___x_3539_);
lean_closure_set(v___f_3557_, 25, v___x_3540_);
lean_closure_set(v___f_3557_, 26, v_numParams_3541_);
lean_closure_set(v___f_3557_, 27, v_snd_3542_);
lean_closure_set(v___f_3557_, 28, v___x_3543_);
lean_closure_set(v___f_3557_, 29, v___x_3551_);
v___x_3558_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3543_, v___x_3551_, v___f_3557_, v___x_3519_, v___x_3519_, v___y_3545_, v___y_3546_, v___y_3547_, v___y_3548_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3559_ = _args[0];
lean_object* v___x_3560_ = _args[1];
lean_object* v_motive_3561_ = _args[2];
lean_object* v___x_3562_ = _args[3];
lean_object* v___x_3563_ = _args[4];
lean_object* v___x_3564_ = _args[5];
lean_object* v___x_3565_ = _args[6];
lean_object* v_is_3566_ = _args[7];
lean_object* v___x_3567_ = _args[8];
lean_object* v___x_3568_ = _args[9];
lean_object* v___x_3569_ = _args[10];
lean_object* v___x_3570_ = _args[11];
lean_object* v_params_3571_ = _args[12];
lean_object* v___x_3572_ = _args[13];
lean_object* v___x_3573_ = _args[14];
lean_object* v_heq_3574_ = _args[15];
lean_object* v_val_3575_ = _args[16];
lean_object* v_tail_3576_ = _args[17];
lean_object* v_sz_3577_ = _args[18];
lean_object* v___x_3578_ = _args[19];
lean_object* v___x_3579_ = _args[20];
lean_object* v___x_3580_ = _args[21];
lean_object* v_declName_3581_ = _args[22];
lean_object* v_levelParams_3582_ = _args[23];
lean_object* v___x_3583_ = _args[24];
lean_object* v___x_3584_ = _args[25];
lean_object* v_numParams_3585_ = _args[26];
lean_object* v_snd_3586_ = _args[27];
lean_object* v___x_3587_ = _args[28];
lean_object* v_alts_3588_ = _args[29];
lean_object* v___y_3589_ = _args[30];
lean_object* v___y_3590_ = _args[31];
lean_object* v___y_3591_ = _args[32];
lean_object* v___y_3592_ = _args[33];
lean_object* v___y_3593_ = _args[34];
_start:
{
uint8_t v___x_16112__boxed_3594_; uint8_t v___x_16113__boxed_3595_; uint8_t v___x_16114__boxed_3596_; size_t v_sz_boxed_3597_; size_t v___x_16123__boxed_3598_; lean_object* v_res_3599_; 
v___x_16112__boxed_3594_ = lean_unbox(v___x_3563_);
v___x_16113__boxed_3595_ = lean_unbox(v___x_3564_);
v___x_16114__boxed_3596_ = lean_unbox(v___x_3565_);
v_sz_boxed_3597_ = lean_unbox_usize(v_sz_3577_);
lean_dec(v_sz_3577_);
v___x_16123__boxed_3598_ = lean_unbox_usize(v___x_3578_);
lean_dec(v___x_3578_);
v_res_3599_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3559_, v___x_3560_, v_motive_3561_, v___x_3562_, v___x_16112__boxed_3594_, v___x_16113__boxed_3595_, v___x_16114__boxed_3596_, v_is_3566_, v___x_3567_, v___x_3568_, v___x_3569_, v___x_3570_, v_params_3571_, v___x_3572_, v___x_3573_, v_heq_3574_, v_val_3575_, v_tail_3576_, v_sz_boxed_3597_, v___x_16123__boxed_3598_, v___x_3579_, v___x_3580_, v_declName_3581_, v_levelParams_3582_, v___x_3583_, v___x_3584_, v_numParams_3585_, v_snd_3586_, v___x_3587_, v_alts_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___x_3560_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3600_, lean_object* v_declInfos_3601_, lean_object* v_k_3602_, lean_object* v_kind_3603_, lean_object* v_x_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
uint8_t v_kind_boxed_3610_; lean_object* v_res_3611_; 
v_kind_boxed_3610_ = lean_unbox(v_kind_3603_);
v_res_3611_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3600_, v_declInfos_3601_, v_k_3602_, v_kind_boxed_3610_, v_x_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3612_, lean_object* v_k_3613_, uint8_t v_kind_3614_, lean_object* v_acc_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v___x_3621_; lean_object* v_toApplicative_3622_; lean_object* v_toFunctor_3623_; lean_object* v_toSeq_3624_; lean_object* v_toSeqLeft_3625_; lean_object* v_toSeqRight_3626_; lean_object* v___f_3627_; lean_object* v___f_3628_; lean_object* v___f_3629_; lean_object* v___f_3630_; lean_object* v___x_3631_; lean_object* v___f_3632_; lean_object* v___f_3633_; lean_object* v___f_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v_toApplicative_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3695_; 
v___x_3621_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3622_ = lean_ctor_get(v___x_3621_, 0);
v_toFunctor_3623_ = lean_ctor_get(v_toApplicative_3622_, 0);
v_toSeq_3624_ = lean_ctor_get(v_toApplicative_3622_, 2);
v_toSeqLeft_3625_ = lean_ctor_get(v_toApplicative_3622_, 3);
v_toSeqRight_3626_ = lean_ctor_get(v_toApplicative_3622_, 4);
v___f_3627_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3628_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3623_, 2);
v___f_3629_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3629_, 0, v_toFunctor_3623_);
v___f_3630_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3630_, 0, v_toFunctor_3623_);
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___f_3629_);
lean_ctor_set(v___x_3631_, 1, v___f_3630_);
lean_inc(v_toSeqRight_3626_);
v___f_3632_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3632_, 0, v_toSeqRight_3626_);
lean_inc(v_toSeqLeft_3625_);
v___f_3633_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3633_, 0, v_toSeqLeft_3625_);
lean_inc(v_toSeq_3624_);
v___f_3634_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3634_, 0, v_toSeq_3624_);
v___x_3635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3631_);
lean_ctor_set(v___x_3635_, 1, v___f_3627_);
lean_ctor_set(v___x_3635_, 2, v___f_3634_);
lean_ctor_set(v___x_3635_, 3, v___f_3633_);
lean_ctor_set(v___x_3635_, 4, v___f_3632_);
v___x_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
lean_ctor_set(v___x_3636_, 1, v___f_3628_);
v___x_3637_ = l_StateRefT_x27_instMonad___redArg(v___x_3636_);
v_toApplicative_3638_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3695_ == 0)
{
lean_object* v_unused_3696_; 
v_unused_3696_ = lean_ctor_get(v___x_3637_, 1);
lean_dec(v_unused_3696_);
v___x_3640_ = v___x_3637_;
v_isShared_3641_ = v_isSharedCheck_3695_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_toApplicative_3638_);
lean_dec(v___x_3637_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3695_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v_toFunctor_3642_; lean_object* v_toSeq_3643_; lean_object* v_toSeqLeft_3644_; lean_object* v_toSeqRight_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3693_; 
v_toFunctor_3642_ = lean_ctor_get(v_toApplicative_3638_, 0);
v_toSeq_3643_ = lean_ctor_get(v_toApplicative_3638_, 2);
v_toSeqLeft_3644_ = lean_ctor_get(v_toApplicative_3638_, 3);
v_toSeqRight_3645_ = lean_ctor_get(v_toApplicative_3638_, 4);
v_isSharedCheck_3693_ = !lean_is_exclusive(v_toApplicative_3638_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; 
v_unused_3694_ = lean_ctor_get(v_toApplicative_3638_, 1);
lean_dec(v_unused_3694_);
v___x_3647_ = v_toApplicative_3638_;
v_isShared_3648_ = v_isSharedCheck_3693_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_toSeqRight_3645_);
lean_inc(v_toSeqLeft_3644_);
lean_inc(v_toSeq_3643_);
lean_inc(v_toFunctor_3642_);
lean_dec(v_toApplicative_3638_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3693_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___f_3649_; lean_object* v___f_3650_; lean_object* v___f_3651_; lean_object* v___f_3652_; lean_object* v___x_3653_; lean_object* v___f_3654_; lean_object* v___f_3655_; lean_object* v___f_3656_; lean_object* v___x_3658_; 
v___f_3649_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3650_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3642_);
v___f_3651_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3651_, 0, v_toFunctor_3642_);
v___f_3652_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3652_, 0, v_toFunctor_3642_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___f_3651_);
lean_ctor_set(v___x_3653_, 1, v___f_3652_);
v___f_3654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3654_, 0, v_toSeqRight_3645_);
v___f_3655_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3655_, 0, v_toSeqLeft_3644_);
v___f_3656_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3656_, 0, v_toSeq_3643_);
if (v_isShared_3648_ == 0)
{
lean_ctor_set(v___x_3647_, 4, v___f_3654_);
lean_ctor_set(v___x_3647_, 3, v___f_3655_);
lean_ctor_set(v___x_3647_, 2, v___f_3656_);
lean_ctor_set(v___x_3647_, 1, v___f_3649_);
lean_ctor_set(v___x_3647_, 0, v___x_3653_);
v___x_3658_ = v___x_3647_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3653_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v___f_3649_);
lean_ctor_set(v_reuseFailAlloc_3692_, 2, v___f_3656_);
lean_ctor_set(v_reuseFailAlloc_3692_, 3, v___f_3655_);
lean_ctor_set(v_reuseFailAlloc_3692_, 4, v___f_3654_);
v___x_3658_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3660_; 
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 1, v___f_3650_);
lean_ctor_set(v___x_3640_, 0, v___x_3658_);
v___x_3660_ = v___x_3640_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v___f_3650_);
v___x_3660_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
v___x_3661_ = lean_array_get_size(v_acc_3615_);
v___x_3662_ = lean_array_get_size(v_declInfos_3612_);
v___x_3663_ = lean_nat_dec_lt(v___x_3661_, v___x_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; 
lean_dec_ref(v___x_3660_);
lean_dec_ref(v_declInfos_3612_);
lean_inc(v___y_3619_);
lean_inc_ref(v___y_3618_);
lean_inc(v___y_3617_);
lean_inc_ref(v___y_3616_);
v___x_3664_ = lean_apply_6(v_k_3613_, v_acc_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, lean_box(0));
return v___x_3664_;
}
else
{
lean_object* v___f_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; lean_object* v___f_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v_snd_3673_; lean_object* v_fst_3674_; lean_object* v_fst_3675_; lean_object* v_snd_3676_; lean_object* v___x_3677_; 
v___f_3665_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3665_, 0, v___x_3660_);
v___x_3666_ = lean_box(0);
v___x_3667_ = 0;
v___f_3668_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3668_, 0, v___f_3665_);
v___x_3669_ = lean_box(v___x_3667_);
v___x_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
lean_ctor_set(v___x_3670_, 1, v___f_3668_);
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3666_);
lean_ctor_set(v___x_3671_, 1, v___x_3670_);
v___x_3672_ = lean_array_get(v___x_3671_, v_declInfos_3612_, v___x_3661_);
lean_dec_ref_known(v___x_3671_, 2);
v_snd_3673_ = lean_ctor_get(v___x_3672_, 1);
lean_inc(v_snd_3673_);
v_fst_3674_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_fst_3674_);
lean_dec(v___x_3672_);
v_fst_3675_ = lean_ctor_get(v_snd_3673_, 0);
lean_inc(v_fst_3675_);
v_snd_3676_ = lean_ctor_get(v_snd_3673_, 1);
lean_inc(v_snd_3676_);
lean_dec(v_snd_3673_);
lean_inc(v___y_3619_);
lean_inc_ref(v___y_3618_);
lean_inc(v___y_3617_);
lean_inc_ref(v___y_3616_);
lean_inc_ref(v_acc_3615_);
v___x_3677_ = lean_apply_6(v_snd_3676_, v_acc_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, lean_box(0));
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3679_; lean_object* v___f_3680_; uint8_t v___x_3681_; lean_object* v___x_3682_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3677_, 1);
v___x_3679_ = lean_box(v_kind_3614_);
v___f_3680_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3680_, 0, v_acc_3615_);
lean_closure_set(v___f_3680_, 1, v_declInfos_3612_);
lean_closure_set(v___f_3680_, 2, v_k_3613_);
lean_closure_set(v___f_3680_, 3, v___x_3679_);
v___x_3681_ = lean_unbox(v_fst_3675_);
lean_dec(v_fst_3675_);
v___x_3682_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3674_, v___x_3681_, v_a_3678_, v___f_3680_, v_kind_3614_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
return v___x_3682_;
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_dec(v_fst_3675_);
lean_dec(v_fst_3674_);
lean_dec_ref(v_acc_3615_);
lean_dec_ref(v_k_3613_);
lean_dec_ref(v_declInfos_3612_);
v_a_3683_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3677_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3677_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3697_, lean_object* v_declInfos_3698_, lean_object* v_k_3699_, uint8_t v_kind_3700_, lean_object* v_x_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3707_ = lean_array_push(v_acc_3697_, v_x_3701_);
v___x_3708_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3698_, v_k_3699_, v_kind_3700_, v___x_3707_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3709_, lean_object* v_k_3710_, lean_object* v_kind_3711_, lean_object* v_acc_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
uint8_t v_kind_boxed_3718_; lean_object* v_res_3719_; 
v_kind_boxed_3718_ = lean_unbox(v_kind_3711_);
v_res_3719_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3709_, v_k_3710_, v_kind_boxed_3718_, v_acc_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3720_, lean_object* v_k_3721_, uint8_t v_kind_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3729_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3720_, v_k_3721_, v_kind_3722_, v___x_3728_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
return v___x_3729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3730_, lean_object* v_k_3731_, lean_object* v_kind_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
uint8_t v_kind_boxed_3738_; lean_object* v_res_3739_; 
v_kind_boxed_3738_ = lean_unbox(v_kind_3732_);
v_res_3739_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3730_, v_k_3731_, v_kind_boxed_3738_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec_ref(v___y_3733_);
return v_res_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3740_, lean_object* v_k_3741_, uint8_t v_kind_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
size_t v_sz_3748_; size_t v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v_sz_3748_ = lean_array_size(v_declInfos_3740_);
v___x_3749_ = ((size_t)0ULL);
v___x_3750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3748_, v___x_3749_, v_declInfos_3740_);
v___x_3751_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3750_, v_k_3741_, v_kind_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
return v___x_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3752_, lean_object* v_k_3753_, lean_object* v_kind_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
uint8_t v_kind_boxed_3760_; lean_object* v_res_3761_; 
v_kind_boxed_3760_ = lean_unbox(v_kind_3754_);
v_res_3761_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3752_, v_k_3753_, v_kind_boxed_3760_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3762_, lean_object* v_k_3763_, uint8_t v_kind_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
size_t v_sz_3770_; size_t v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v_sz_3770_ = lean_array_size(v_declInfos_3762_);
v___x_3771_ = ((size_t)0ULL);
v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3770_, v___x_3771_, v_declInfos_3762_);
v___x_3773_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3772_, v_k_3763_, v_kind_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3774_, lean_object* v_k_3775_, lean_object* v_kind_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
uint8_t v_kind_boxed_3782_; lean_object* v_res_3783_; 
v_kind_boxed_3782_ = lean_unbox(v_kind_3776_);
v_res_3783_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3774_, v_k_3775_, v_kind_boxed_3782_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
return v_res_3783_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3786_ = lean_box(0);
v___x_3787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3788_ = l_Lean_mkConst(v___x_3787_, v___x_3786_);
return v___x_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3789_, lean_object* v___x_3790_, lean_object* v_motive_3791_, uint8_t v___x_3792_, uint8_t v___x_3793_, uint8_t v___x_3794_, lean_object* v___x_3795_, lean_object* v_v_3796_, lean_object* v___x_3797_, lean_object* v_zs12_3798_, lean_object* v_is_3799_, lean_object* v_fields1_3800_, lean_object* v_fields2_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v_e_3817_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
lean_inc(v___x_3789_);
v___x_3827_ = l_Lean_mkNatLit(v___x_3789_);
v___x_3828_ = l_Lean_Meta_mkEqRefl(v___x_3827_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
lean_dec_ref_known(v___x_3828_, 1);
lean_inc_ref(v___x_3790_);
v___x_3830_ = l_Lean_mkAppN(v___x_3790_, v_fields1_3800_);
v___x_3831_ = l_Lean_mkAppN(v___x_3790_, v_fields2_3801_);
v___x_3832_ = lean_unsigned_to_nat(3u);
v___x_3833_ = lean_mk_empty_array_with_capacity(v___x_3832_);
v___x_3834_ = lean_array_push(v___x_3833_, v___x_3830_);
v___x_3835_ = lean_array_push(v___x_3834_, v___x_3831_);
v___x_3836_ = lean_array_push(v___x_3835_, v_a_3829_);
v___x_3837_ = l_Array_append___redArg(v_is_3799_, v___x_3836_);
lean_dec_ref(v___x_3836_);
v___x_3838_ = l_Lean_mkAppN(v_motive_3791_, v___x_3837_);
lean_dec_ref(v___x_3837_);
v___x_3839_ = l_Lean_Meta_mkForallFVars(v_zs12_3798_, v___x_3838_, v___x_3792_, v___x_3793_, v___x_3793_, v___x_3794_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3841_; uint8_t v___x_3842_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_a_3840_);
lean_dec_ref_known(v___x_3839_, 1);
v___x_3841_ = lean_array_get_size(v_zs12_3798_);
v___x_3842_ = lean_nat_dec_eq(v___x_3841_, v___x_3795_);
if (v___x_3842_ == 0)
{
v_e_3817_ = v_a_3840_;
goto v___jp_3816_;
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3844_ = l_Lean_mkArrow(v___x_3843_, v_a_3840_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
v_e_3817_ = v_a_3845_;
goto v___jp_3816_;
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_dec(v_v_3796_);
lean_dec(v___x_3795_);
lean_dec(v___x_3789_);
v_a_3846_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3844_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3844_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
}
}
else
{
lean_object* v_a_3854_; lean_object* v___x_3856_; uint8_t v_isShared_3857_; uint8_t v_isSharedCheck_3861_; 
lean_dec(v_v_3796_);
lean_dec(v___x_3795_);
lean_dec(v___x_3789_);
v_a_3854_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3861_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3861_ == 0)
{
v___x_3856_ = v___x_3839_;
v_isShared_3857_ = v_isSharedCheck_3861_;
goto v_resetjp_3855_;
}
else
{
lean_inc(v_a_3854_);
lean_dec(v___x_3839_);
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
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec_ref(v_is_3799_);
lean_dec(v_v_3796_);
lean_dec(v___x_3795_);
lean_dec_ref(v_motive_3791_);
lean_dec_ref(v___x_3790_);
lean_dec(v___x_3789_);
v_a_3862_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3828_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3828_);
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
v___jp_3807_:
{
lean_object* v___x_3810_; uint8_t v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3810_ = lean_array_get_size(v_zs12_3798_);
v___x_3811_ = lean_nat_dec_eq(v___x_3810_, v___x_3795_);
v___x_3812_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3795_);
lean_ctor_set_uint8(v___x_3812_, sizeof(void*)*2, v___x_3811_);
v___x_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___y_3809_);
lean_ctor_set(v___x_3813_, 1, v___y_3808_);
v___x_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
lean_ctor_set(v___x_3814_, 1, v___x_3812_);
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
return v___x_3815_;
}
v___jp_3816_:
{
if (lean_obj_tag(v_v_3796_) == 1)
{
lean_object* v_str_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; 
lean_dec(v___x_3789_);
v_str_3818_ = lean_ctor_get(v_v_3796_, 1);
lean_inc_ref(v_str_3818_);
lean_dec_ref_known(v_v_3796_, 2);
v___x_3819_ = lean_box(0);
v___x_3820_ = l_Lean_Name_str___override(v___x_3819_, v_str_3818_);
v___y_3808_ = v_e_3817_;
v___y_3809_ = v___x_3820_;
goto v___jp_3807_;
}
else
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_dec(v_v_3796_);
v___x_3821_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3822_ = lean_nat_add(v___x_3789_, v___x_3797_);
lean_dec(v___x_3789_);
v___x_3823_ = l_Nat_reprFast(v___x_3822_);
v___x_3824_ = lean_string_append(v___x_3821_, v___x_3823_);
lean_dec_ref(v___x_3823_);
v___x_3825_ = lean_box(0);
v___x_3826_ = l_Lean_Name_str___override(v___x_3825_, v___x_3824_);
v___y_3808_ = v_e_3817_;
v___y_3809_ = v___x_3826_;
goto v___jp_3807_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3870_ = _args[0];
lean_object* v___x_3871_ = _args[1];
lean_object* v_motive_3872_ = _args[2];
lean_object* v___x_3873_ = _args[3];
lean_object* v___x_3874_ = _args[4];
lean_object* v___x_3875_ = _args[5];
lean_object* v___x_3876_ = _args[6];
lean_object* v_v_3877_ = _args[7];
lean_object* v___x_3878_ = _args[8];
lean_object* v_zs12_3879_ = _args[9];
lean_object* v_is_3880_ = _args[10];
lean_object* v_fields1_3881_ = _args[11];
lean_object* v_fields2_3882_ = _args[12];
lean_object* v___y_3883_ = _args[13];
lean_object* v___y_3884_ = _args[14];
lean_object* v___y_3885_ = _args[15];
lean_object* v___y_3886_ = _args[16];
lean_object* v___y_3887_ = _args[17];
_start:
{
uint8_t v___x_16455__boxed_3888_; uint8_t v___x_16456__boxed_3889_; uint8_t v___x_16457__boxed_3890_; lean_object* v_res_3891_; 
v___x_16455__boxed_3888_ = lean_unbox(v___x_3873_);
v___x_16456__boxed_3889_ = lean_unbox(v___x_3874_);
v___x_16457__boxed_3890_ = lean_unbox(v___x_3875_);
v_res_3891_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3870_, v___x_3871_, v_motive_3872_, v___x_16455__boxed_3888_, v___x_16456__boxed_3889_, v___x_16457__boxed_3890_, v___x_3876_, v_v_3877_, v___x_3878_, v_zs12_3879_, v_is_3880_, v_fields1_3881_, v_fields2_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec_ref(v_fields2_3882_);
lean_dec_ref(v_fields1_3881_);
lean_dec_ref(v_zs12_3879_);
lean_dec(v___x_3878_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3892_, lean_object* v_params_3893_, lean_object* v_motive_3894_, size_t v_sz_3895_, size_t v_i_3896_, lean_object* v_bs_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_){
_start:
{
uint8_t v___x_3903_; 
v___x_3903_ = lean_usize_dec_lt(v_i_3896_, v_sz_3895_);
if (v___x_3903_ == 0)
{
lean_object* v___x_3904_; 
lean_dec_ref(v_motive_3894_);
lean_dec(v_tail_3892_);
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v_bs_3897_);
return v___x_3904_;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; uint8_t v___x_3908_; lean_object* v_v_3909_; lean_object* v_bs_x27_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; 
v___x_3905_ = lean_unsigned_to_nat(0u);
v___x_3906_ = lean_unsigned_to_nat(1u);
v___x_3907_ = 0;
v___x_3908_ = 1;
v_v_3909_ = lean_array_uget(v_bs_3897_, v_i_3896_);
v_bs_x27_3910_ = lean_array_uset(v_bs_3897_, v_i_3896_, v___x_3905_);
v___x_3911_ = lean_usize_to_nat(v_i_3896_);
lean_inc(v_tail_3892_);
lean_inc(v_v_3909_);
v___x_3912_ = l_Lean_mkConst(v_v_3909_, v_tail_3892_);
v___x_3913_ = l_Lean_mkAppN(v___x_3912_, v_params_3893_);
v___x_3914_ = lean_box(v___x_3907_);
v___x_3915_ = lean_box(v___x_3903_);
v___x_3916_ = lean_box(v___x_3908_);
lean_inc_ref(v_motive_3894_);
lean_inc_ref(v___x_3913_);
v___f_3917_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3917_, 0, v___x_3911_);
lean_closure_set(v___f_3917_, 1, v___x_3913_);
lean_closure_set(v___f_3917_, 2, v_motive_3894_);
lean_closure_set(v___f_3917_, 3, v___x_3914_);
lean_closure_set(v___f_3917_, 4, v___x_3915_);
lean_closure_set(v___f_3917_, 5, v___x_3916_);
lean_closure_set(v___f_3917_, 6, v___x_3905_);
lean_closure_set(v___f_3917_, 7, v_v_3909_);
lean_closure_set(v___f_3917_, 8, v___x_3906_);
v___x_3918_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3913_, v___f_3917_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v_a_3919_; size_t v___x_3920_; size_t v___x_3921_; lean_object* v___x_3922_; 
v_a_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3919_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3920_ = ((size_t)1ULL);
v___x_3921_ = lean_usize_add(v_i_3896_, v___x_3920_);
v___x_3922_ = lean_array_uset(v_bs_x27_3910_, v_i_3896_, v_a_3919_);
v_i_3896_ = v___x_3921_;
v_bs_3897_ = v___x_3922_;
goto _start;
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec_ref(v_bs_x27_3910_);
lean_dec_ref(v_motive_3894_);
lean_dec(v_tail_3892_);
v_a_3924_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3918_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3918_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3932_, lean_object* v_params_3933_, lean_object* v_motive_3934_, lean_object* v_sz_3935_, lean_object* v_i_3936_, lean_object* v_bs_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
size_t v_sz_boxed_3943_; size_t v_i_boxed_3944_; lean_object* v_res_3945_; 
v_sz_boxed_3943_ = lean_unbox_usize(v_sz_3935_);
lean_dec(v_sz_3935_);
v_i_boxed_3944_ = lean_unbox_usize(v_i_3936_);
lean_dec(v_i_3936_);
v_res_3945_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3932_, v_params_3933_, v_motive_3934_, v_sz_boxed_3943_, v_i_boxed_3944_, v_bs_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec_ref(v_params_3933_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3948_, lean_object* v_tail_3949_, lean_object* v_params_3950_, lean_object* v_numIndices_3951_, lean_object* v___x_3952_, lean_object* v___x_3953_, uint8_t v___x_3954_, uint8_t v___x_3955_, uint8_t v___x_3956_, lean_object* v_is_3957_, lean_object* v___x_3958_, lean_object* v___x_3959_, lean_object* v___x_3960_, lean_object* v___x_3961_, lean_object* v___x_3962_, lean_object* v___x_3963_, lean_object* v_heq_3964_, lean_object* v_val_3965_, lean_object* v___x_3966_, lean_object* v_declName_3967_, lean_object* v_levelParams_3968_, lean_object* v___x_3969_, lean_object* v___x_3970_, lean_object* v_numParams_3971_, lean_object* v___x_3972_, lean_object* v_motive_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v___x_3979_; size_t v_sz_3980_; size_t v___x_3981_; lean_object* v___x_3982_; 
v___x_3979_ = lean_array_mk(v_ctors_3948_);
v_sz_3980_ = lean_array_size(v___x_3979_);
v___x_3981_ = ((size_t)0ULL);
lean_inc_ref(v___x_3979_);
lean_inc_ref(v_motive_3973_);
lean_inc(v_tail_3949_);
v___x_3982_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3949_, v_params_3950_, v_motive_3973_, v_sz_3980_, v___x_3981_, v___x_3979_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v___x_3984_; lean_object* v_fst_3985_; lean_object* v_snd_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___f_3992_; uint8_t v___x_3993_; lean_object* v___x_3994_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref_known(v___x_3982_, 1);
v___x_3984_ = l_Array_unzip___redArg(v_a_3983_);
lean_dec(v_a_3983_);
v_fst_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_fst_3985_);
v_snd_3986_ = lean_ctor_get(v___x_3984_, 1);
lean_inc(v_snd_3986_);
lean_dec_ref(v___x_3984_);
v___x_3987_ = lean_box(v___x_3954_);
v___x_3988_ = lean_box(v___x_3955_);
v___x_3989_ = lean_box(v___x_3956_);
v___x_3990_ = lean_box_usize(v_sz_3980_);
v___x_3991_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_3992_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_3992_, 0, v_numIndices_3951_);
lean_closure_set(v___f_3992_, 1, v___x_3952_);
lean_closure_set(v___f_3992_, 2, v_motive_3973_);
lean_closure_set(v___f_3992_, 3, v___x_3953_);
lean_closure_set(v___f_3992_, 4, v___x_3987_);
lean_closure_set(v___f_3992_, 5, v___x_3988_);
lean_closure_set(v___f_3992_, 6, v___x_3989_);
lean_closure_set(v___f_3992_, 7, v_is_3957_);
lean_closure_set(v___f_3992_, 8, v___x_3958_);
lean_closure_set(v___f_3992_, 9, v___x_3959_);
lean_closure_set(v___f_3992_, 10, v___x_3960_);
lean_closure_set(v___f_3992_, 11, v___x_3961_);
lean_closure_set(v___f_3992_, 12, v_params_3950_);
lean_closure_set(v___f_3992_, 13, v___x_3962_);
lean_closure_set(v___f_3992_, 14, v___x_3963_);
lean_closure_set(v___f_3992_, 15, v_heq_3964_);
lean_closure_set(v___f_3992_, 16, v_val_3965_);
lean_closure_set(v___f_3992_, 17, v_tail_3949_);
lean_closure_set(v___f_3992_, 18, v___x_3990_);
lean_closure_set(v___f_3992_, 19, v___x_3991_);
lean_closure_set(v___f_3992_, 20, v___x_3979_);
lean_closure_set(v___f_3992_, 21, v___x_3966_);
lean_closure_set(v___f_3992_, 22, v_declName_3967_);
lean_closure_set(v___f_3992_, 23, v_levelParams_3968_);
lean_closure_set(v___f_3992_, 24, v___x_3969_);
lean_closure_set(v___f_3992_, 25, v___x_3970_);
lean_closure_set(v___f_3992_, 26, v_numParams_3971_);
lean_closure_set(v___f_3992_, 27, v_snd_3986_);
lean_closure_set(v___f_3992_, 28, v___x_3972_);
v___x_3993_ = 0;
v___x_3994_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_3985_, v___f_3992_, v___x_3993_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
return v___x_3994_;
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_dec_ref(v___x_3979_);
lean_dec_ref(v_motive_3973_);
lean_dec_ref(v___x_3972_);
lean_dec(v_numParams_3971_);
lean_dec(v___x_3970_);
lean_dec(v___x_3969_);
lean_dec(v_levelParams_3968_);
lean_dec(v_declName_3967_);
lean_dec_ref(v___x_3966_);
lean_dec_ref(v_val_3965_);
lean_dec_ref(v_heq_3964_);
lean_dec_ref(v___x_3963_);
lean_dec_ref(v___x_3962_);
lean_dec(v___x_3961_);
lean_dec(v___x_3960_);
lean_dec_ref(v___x_3959_);
lean_dec_ref(v___x_3958_);
lean_dec_ref(v_is_3957_);
lean_dec_ref(v___x_3953_);
lean_dec(v___x_3952_);
lean_dec(v_numIndices_3951_);
lean_dec_ref(v_params_3950_);
lean_dec(v_tail_3949_);
v_a_3995_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3982_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3982_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4003_ = _args[0];
lean_object* v_tail_4004_ = _args[1];
lean_object* v_params_4005_ = _args[2];
lean_object* v_numIndices_4006_ = _args[3];
lean_object* v___x_4007_ = _args[4];
lean_object* v___x_4008_ = _args[5];
lean_object* v___x_4009_ = _args[6];
lean_object* v___x_4010_ = _args[7];
lean_object* v___x_4011_ = _args[8];
lean_object* v_is_4012_ = _args[9];
lean_object* v___x_4013_ = _args[10];
lean_object* v___x_4014_ = _args[11];
lean_object* v___x_4015_ = _args[12];
lean_object* v___x_4016_ = _args[13];
lean_object* v___x_4017_ = _args[14];
lean_object* v___x_4018_ = _args[15];
lean_object* v_heq_4019_ = _args[16];
lean_object* v_val_4020_ = _args[17];
lean_object* v___x_4021_ = _args[18];
lean_object* v_declName_4022_ = _args[19];
lean_object* v_levelParams_4023_ = _args[20];
lean_object* v___x_4024_ = _args[21];
lean_object* v___x_4025_ = _args[22];
lean_object* v_numParams_4026_ = _args[23];
lean_object* v___x_4027_ = _args[24];
lean_object* v_motive_4028_ = _args[25];
lean_object* v___y_4029_ = _args[26];
lean_object* v___y_4030_ = _args[27];
lean_object* v___y_4031_ = _args[28];
lean_object* v___y_4032_ = _args[29];
lean_object* v___y_4033_ = _args[30];
_start:
{
uint8_t v___x_16694__boxed_4034_; uint8_t v___x_16695__boxed_4035_; uint8_t v___x_16696__boxed_4036_; lean_object* v_res_4037_; 
v___x_16694__boxed_4034_ = lean_unbox(v___x_4009_);
v___x_16695__boxed_4035_ = lean_unbox(v___x_4010_);
v___x_16696__boxed_4036_ = lean_unbox(v___x_4011_);
v_res_4037_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4003_, v_tail_4004_, v_params_4005_, v_numIndices_4006_, v___x_4007_, v___x_4008_, v___x_16694__boxed_4034_, v___x_16695__boxed_4035_, v___x_16696__boxed_4036_, v_is_4012_, v___x_4013_, v___x_4014_, v___x_4015_, v___x_4016_, v___x_4017_, v___x_4018_, v_heq_4019_, v_val_4020_, v___x_4021_, v_declName_4022_, v_levelParams_4023_, v___x_4024_, v___x_4025_, v_numParams_4026_, v___x_4027_, v_motive_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4038_, lean_object* v___x_4039_, lean_object* v_is_4040_, lean_object* v_head_4041_, lean_object* v_ctors_4042_, lean_object* v_tail_4043_, lean_object* v_params_4044_, lean_object* v_numIndices_4045_, lean_object* v___x_4046_, lean_object* v___x_4047_, lean_object* v___x_4048_, lean_object* v___x_4049_, lean_object* v___x_4050_, lean_object* v_val_4051_, lean_object* v___x_4052_, lean_object* v_declName_4053_, lean_object* v_levelParams_4054_, lean_object* v___x_4055_, lean_object* v_numParams_4056_, lean_object* v___x_4057_, lean_object* v_heq_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; uint8_t v___x_4071_; uint8_t v___x_4072_; uint8_t v___x_4073_; lean_object* v___x_4074_; 
v___x_4064_ = lean_unsigned_to_nat(3u);
v___x_4065_ = lean_mk_empty_array_with_capacity(v___x_4064_);
lean_inc_ref(v___x_4038_);
v___x_4066_ = lean_array_push(v___x_4065_, v___x_4038_);
lean_inc_ref(v___x_4039_);
v___x_4067_ = lean_array_push(v___x_4066_, v___x_4039_);
lean_inc_ref(v_heq_4058_);
v___x_4068_ = lean_array_push(v___x_4067_, v_heq_4058_);
lean_inc_ref(v_is_4040_);
v___x_4069_ = l_Array_append___redArg(v_is_4040_, v___x_4068_);
lean_dec_ref(v___x_4068_);
v___x_4070_ = l_Lean_mkSort(v_head_4041_);
v___x_4071_ = 0;
v___x_4072_ = 1;
v___x_4073_ = 1;
v___x_4074_ = l_Lean_Meta_mkForallFVars(v___x_4069_, v___x_4070_, v___x_4071_, v___x_4072_, v___x_4072_, v___x_4073_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___f_4079_; lean_object* v___x_4080_; uint8_t v___x_4081_; lean_object* v___x_4082_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___x_4074_, 1);
v___x_4076_ = lean_box(v___x_4071_);
v___x_4077_ = lean_box(v___x_4072_);
v___x_4078_ = lean_box(v___x_4073_);
v___f_4079_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4079_, 0, v_ctors_4042_);
lean_closure_set(v___f_4079_, 1, v_tail_4043_);
lean_closure_set(v___f_4079_, 2, v_params_4044_);
lean_closure_set(v___f_4079_, 3, v_numIndices_4045_);
lean_closure_set(v___f_4079_, 4, v___x_4046_);
lean_closure_set(v___f_4079_, 5, v___x_4069_);
lean_closure_set(v___f_4079_, 6, v___x_4076_);
lean_closure_set(v___f_4079_, 7, v___x_4077_);
lean_closure_set(v___f_4079_, 8, v___x_4078_);
lean_closure_set(v___f_4079_, 9, v_is_4040_);
lean_closure_set(v___f_4079_, 10, v___x_4039_);
lean_closure_set(v___f_4079_, 11, v___x_4038_);
lean_closure_set(v___f_4079_, 12, v___x_4047_);
lean_closure_set(v___f_4079_, 13, v___x_4048_);
lean_closure_set(v___f_4079_, 14, v___x_4049_);
lean_closure_set(v___f_4079_, 15, v___x_4050_);
lean_closure_set(v___f_4079_, 16, v_heq_4058_);
lean_closure_set(v___f_4079_, 17, v_val_4051_);
lean_closure_set(v___f_4079_, 18, v___x_4052_);
lean_closure_set(v___f_4079_, 19, v_declName_4053_);
lean_closure_set(v___f_4079_, 20, v_levelParams_4054_);
lean_closure_set(v___f_4079_, 21, v___x_4064_);
lean_closure_set(v___f_4079_, 22, v___x_4055_);
lean_closure_set(v___f_4079_, 23, v_numParams_4056_);
lean_closure_set(v___f_4079_, 24, v___x_4057_);
v___x_4080_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4081_ = 0;
v___x_4082_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4080_, v___x_4073_, v_a_4075_, v___f_4079_, v___x_4081_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_);
return v___x_4082_;
}
else
{
lean_object* v_a_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4090_; 
lean_dec_ref(v___x_4069_);
lean_dec_ref(v_heq_4058_);
lean_dec_ref(v___x_4057_);
lean_dec(v_numParams_4056_);
lean_dec(v___x_4055_);
lean_dec(v_levelParams_4054_);
lean_dec(v_declName_4053_);
lean_dec_ref(v___x_4052_);
lean_dec_ref(v_val_4051_);
lean_dec_ref(v___x_4050_);
lean_dec_ref(v___x_4049_);
lean_dec(v___x_4048_);
lean_dec(v___x_4047_);
lean_dec(v___x_4046_);
lean_dec(v_numIndices_4045_);
lean_dec_ref(v_params_4044_);
lean_dec(v_tail_4043_);
lean_dec(v_ctors_4042_);
lean_dec_ref(v_is_4040_);
lean_dec_ref(v___x_4039_);
lean_dec_ref(v___x_4038_);
v_a_4083_ = lean_ctor_get(v___x_4074_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4074_);
if (v_isSharedCheck_4090_ == 0)
{
v___x_4085_ = v___x_4074_;
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_a_4083_);
lean_dec(v___x_4074_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4090_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4088_; 
if (v_isShared_4086_ == 0)
{
v___x_4088_ = v___x_4085_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v_a_4083_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4091_ = _args[0];
lean_object* v___x_4092_ = _args[1];
lean_object* v_is_4093_ = _args[2];
lean_object* v_head_4094_ = _args[3];
lean_object* v_ctors_4095_ = _args[4];
lean_object* v_tail_4096_ = _args[5];
lean_object* v_params_4097_ = _args[6];
lean_object* v_numIndices_4098_ = _args[7];
lean_object* v___x_4099_ = _args[8];
lean_object* v___x_4100_ = _args[9];
lean_object* v___x_4101_ = _args[10];
lean_object* v___x_4102_ = _args[11];
lean_object* v___x_4103_ = _args[12];
lean_object* v_val_4104_ = _args[13];
lean_object* v___x_4105_ = _args[14];
lean_object* v_declName_4106_ = _args[15];
lean_object* v_levelParams_4107_ = _args[16];
lean_object* v___x_4108_ = _args[17];
lean_object* v_numParams_4109_ = _args[18];
lean_object* v___x_4110_ = _args[19];
lean_object* v_heq_4111_ = _args[20];
lean_object* v___y_4112_ = _args[21];
lean_object* v___y_4113_ = _args[22];
lean_object* v___y_4114_ = _args[23];
lean_object* v___y_4115_ = _args[24];
lean_object* v___y_4116_ = _args[25];
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4091_, v___x_4092_, v_is_4093_, v_head_4094_, v_ctors_4095_, v_tail_4096_, v_params_4097_, v_numIndices_4098_, v___x_4099_, v___x_4100_, v___x_4101_, v___x_4102_, v___x_4103_, v_val_4104_, v___x_4105_, v_declName_4106_, v_levelParams_4107_, v___x_4108_, v_numParams_4109_, v___x_4110_, v_heq_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4118_, lean_object* v_x1_4119_, lean_object* v_indName_4120_, lean_object* v_tail_4121_, lean_object* v_params_4122_, lean_object* v_is_4123_, lean_object* v___x_4124_, lean_object* v_head_4125_, lean_object* v_ctors_4126_, lean_object* v_numIndices_4127_, lean_object* v___x_4128_, lean_object* v___x_4129_, lean_object* v_val_4130_, lean_object* v_declName_4131_, lean_object* v_levelParams_4132_, lean_object* v_numParams_4133_, lean_object* v___x_4134_, lean_object* v_x2_4135_, lean_object* v_x_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4142_ = lean_unsigned_to_nat(0u);
v___x_4143_ = lean_array_get_borrowed(v___x_4118_, v_x1_4119_, v___x_4142_);
v___x_4144_ = lean_array_get_borrowed(v___x_4118_, v_x2_4135_, v___x_4142_);
v___x_4145_ = l_Lean_mkCtorIdxName(v_indName_4120_);
lean_inc(v_tail_4121_);
v___x_4146_ = l_Lean_mkConst(v___x_4145_, v_tail_4121_);
lean_inc_ref(v_params_4122_);
v___x_4147_ = l_Array_append___redArg(v_params_4122_, v_is_4123_);
v___x_4148_ = lean_mk_empty_array_with_capacity(v___x_4124_);
lean_inc(v___x_4143_);
lean_inc_ref_n(v___x_4148_, 2);
v___x_4149_ = lean_array_push(v___x_4148_, v___x_4143_);
lean_inc_ref(v___x_4147_);
v___x_4150_ = l_Array_append___redArg(v___x_4147_, v___x_4149_);
lean_inc_ref(v___x_4146_);
v___x_4151_ = l_Lean_mkAppN(v___x_4146_, v___x_4150_);
lean_dec_ref(v___x_4150_);
lean_inc(v___x_4144_);
v___x_4152_ = lean_array_push(v___x_4148_, v___x_4144_);
v___x_4153_ = l_Array_append___redArg(v___x_4147_, v___x_4152_);
v___x_4154_ = l_Lean_mkAppN(v___x_4146_, v___x_4153_);
lean_dec_ref(v___x_4153_);
v___x_4155_ = l_Lean_Meta_mkEq(v___x_4151_, v___x_4154_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___f_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
lean_inc(v___x_4144_);
lean_inc(v___x_4143_);
v___f_4157_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4157_, 0, v___x_4143_);
lean_closure_set(v___f_4157_, 1, v___x_4144_);
lean_closure_set(v___f_4157_, 2, v_is_4123_);
lean_closure_set(v___f_4157_, 3, v_head_4125_);
lean_closure_set(v___f_4157_, 4, v_ctors_4126_);
lean_closure_set(v___f_4157_, 5, v_tail_4121_);
lean_closure_set(v___f_4157_, 6, v_params_4122_);
lean_closure_set(v___f_4157_, 7, v_numIndices_4127_);
lean_closure_set(v___f_4157_, 8, v___x_4124_);
lean_closure_set(v___f_4157_, 9, v___x_4128_);
lean_closure_set(v___f_4157_, 10, v___x_4129_);
lean_closure_set(v___f_4157_, 11, v___x_4149_);
lean_closure_set(v___f_4157_, 12, v___x_4152_);
lean_closure_set(v___f_4157_, 13, v_val_4130_);
lean_closure_set(v___f_4157_, 14, v___x_4148_);
lean_closure_set(v___f_4157_, 15, v_declName_4131_);
lean_closure_set(v___f_4157_, 16, v_levelParams_4132_);
lean_closure_set(v___f_4157_, 17, v___x_4142_);
lean_closure_set(v___f_4157_, 18, v_numParams_4133_);
lean_closure_set(v___f_4157_, 19, v___x_4134_);
v___x_4158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4159_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4158_, v_a_4156_, v___f_4157_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
return v___x_4159_;
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec_ref(v___x_4152_);
lean_dec_ref(v___x_4149_);
lean_dec_ref(v___x_4148_);
lean_dec_ref(v___x_4134_);
lean_dec(v_numParams_4133_);
lean_dec(v_levelParams_4132_);
lean_dec(v_declName_4131_);
lean_dec_ref(v_val_4130_);
lean_dec(v___x_4129_);
lean_dec(v___x_4128_);
lean_dec(v_numIndices_4127_);
lean_dec(v_ctors_4126_);
lean_dec(v_head_4125_);
lean_dec(v___x_4124_);
lean_dec_ref(v_is_4123_);
lean_dec_ref(v_params_4122_);
lean_dec(v_tail_4121_);
v_a_4160_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4155_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4155_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4168_ = _args[0];
lean_object* v_x1_4169_ = _args[1];
lean_object* v_indName_4170_ = _args[2];
lean_object* v_tail_4171_ = _args[3];
lean_object* v_params_4172_ = _args[4];
lean_object* v_is_4173_ = _args[5];
lean_object* v___x_4174_ = _args[6];
lean_object* v_head_4175_ = _args[7];
lean_object* v_ctors_4176_ = _args[8];
lean_object* v_numIndices_4177_ = _args[9];
lean_object* v___x_4178_ = _args[10];
lean_object* v___x_4179_ = _args[11];
lean_object* v_val_4180_ = _args[12];
lean_object* v_declName_4181_ = _args[13];
lean_object* v_levelParams_4182_ = _args[14];
lean_object* v_numParams_4183_ = _args[15];
lean_object* v___x_4184_ = _args[16];
lean_object* v_x2_4185_ = _args[17];
lean_object* v_x_4186_ = _args[18];
lean_object* v___y_4187_ = _args[19];
lean_object* v___y_4188_ = _args[20];
lean_object* v___y_4189_ = _args[21];
lean_object* v___y_4190_ = _args[22];
lean_object* v___y_4191_ = _args[23];
_start:
{
lean_object* v_res_4192_; 
v_res_4192_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4168_, v_x1_4169_, v_indName_4170_, v_tail_4171_, v_params_4172_, v_is_4173_, v___x_4174_, v_head_4175_, v_ctors_4176_, v_numIndices_4177_, v___x_4178_, v___x_4179_, v_val_4180_, v_declName_4181_, v_levelParams_4182_, v_numParams_4183_, v___x_4184_, v_x2_4185_, v_x_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec_ref(v_x_4186_);
lean_dec_ref(v_x2_4185_);
lean_dec_ref(v_x1_4169_);
lean_dec_ref(v___x_4168_);
return v_res_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4193_, lean_object* v_indName_4194_, lean_object* v_tail_4195_, lean_object* v_params_4196_, lean_object* v_is_4197_, lean_object* v___x_4198_, lean_object* v_head_4199_, lean_object* v_ctors_4200_, lean_object* v_numIndices_4201_, lean_object* v___x_4202_, lean_object* v___x_4203_, lean_object* v_val_4204_, lean_object* v_declName_4205_, lean_object* v_levelParams_4206_, lean_object* v_numParams_4207_, lean_object* v___x_4208_, lean_object* v_t_4209_, lean_object* v___x_4210_, lean_object* v_x1_4211_, lean_object* v_x_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v___f_4218_; uint8_t v___x_4219_; lean_object* v___x_4220_; 
v___f_4218_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4218_, 0, v___x_4193_);
lean_closure_set(v___f_4218_, 1, v_x1_4211_);
lean_closure_set(v___f_4218_, 2, v_indName_4194_);
lean_closure_set(v___f_4218_, 3, v_tail_4195_);
lean_closure_set(v___f_4218_, 4, v_params_4196_);
lean_closure_set(v___f_4218_, 5, v_is_4197_);
lean_closure_set(v___f_4218_, 6, v___x_4198_);
lean_closure_set(v___f_4218_, 7, v_head_4199_);
lean_closure_set(v___f_4218_, 8, v_ctors_4200_);
lean_closure_set(v___f_4218_, 9, v_numIndices_4201_);
lean_closure_set(v___f_4218_, 10, v___x_4202_);
lean_closure_set(v___f_4218_, 11, v___x_4203_);
lean_closure_set(v___f_4218_, 12, v_val_4204_);
lean_closure_set(v___f_4218_, 13, v_declName_4205_);
lean_closure_set(v___f_4218_, 14, v_levelParams_4206_);
lean_closure_set(v___f_4218_, 15, v_numParams_4207_);
lean_closure_set(v___f_4218_, 16, v___x_4208_);
v___x_4219_ = 0;
v___x_4220_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4209_, v___x_4210_, v___f_4218_, v___x_4219_, v___x_4219_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4221_ = _args[0];
lean_object* v_indName_4222_ = _args[1];
lean_object* v_tail_4223_ = _args[2];
lean_object* v_params_4224_ = _args[3];
lean_object* v_is_4225_ = _args[4];
lean_object* v___x_4226_ = _args[5];
lean_object* v_head_4227_ = _args[6];
lean_object* v_ctors_4228_ = _args[7];
lean_object* v_numIndices_4229_ = _args[8];
lean_object* v___x_4230_ = _args[9];
lean_object* v___x_4231_ = _args[10];
lean_object* v_val_4232_ = _args[11];
lean_object* v_declName_4233_ = _args[12];
lean_object* v_levelParams_4234_ = _args[13];
lean_object* v_numParams_4235_ = _args[14];
lean_object* v___x_4236_ = _args[15];
lean_object* v_t_4237_ = _args[16];
lean_object* v___x_4238_ = _args[17];
lean_object* v_x1_4239_ = _args[18];
lean_object* v_x_4240_ = _args[19];
lean_object* v___y_4241_ = _args[20];
lean_object* v___y_4242_ = _args[21];
lean_object* v___y_4243_ = _args[22];
lean_object* v___y_4244_ = _args[23];
lean_object* v___y_4245_ = _args[24];
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4221_, v_indName_4222_, v_tail_4223_, v_params_4224_, v_is_4225_, v___x_4226_, v_head_4227_, v_ctors_4228_, v_numIndices_4229_, v___x_4230_, v___x_4231_, v_val_4232_, v_declName_4233_, v_levelParams_4234_, v_numParams_4235_, v___x_4236_, v_t_4237_, v___x_4238_, v_x1_4239_, v_x_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
lean_dec(v___y_4244_);
lean_dec_ref(v___y_4243_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
lean_dec_ref(v_x_4240_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4247_, lean_object* v_indName_4248_, lean_object* v_tail_4249_, lean_object* v_params_4250_, lean_object* v_head_4251_, lean_object* v_ctors_4252_, lean_object* v_numIndices_4253_, lean_object* v___x_4254_, lean_object* v___x_4255_, lean_object* v_val_4256_, lean_object* v_declName_4257_, lean_object* v_levelParams_4258_, lean_object* v_numParams_4259_, lean_object* v___x_4260_, lean_object* v_is_4261_, lean_object* v_t_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___f_4270_; uint8_t v___x_4271_; lean_object* v___x_4272_; 
v___x_4268_ = lean_unsigned_to_nat(1u);
v___x_4269_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4262_);
v___f_4270_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4270_, 0, v___x_4247_);
lean_closure_set(v___f_4270_, 1, v_indName_4248_);
lean_closure_set(v___f_4270_, 2, v_tail_4249_);
lean_closure_set(v___f_4270_, 3, v_params_4250_);
lean_closure_set(v___f_4270_, 4, v_is_4261_);
lean_closure_set(v___f_4270_, 5, v___x_4268_);
lean_closure_set(v___f_4270_, 6, v_head_4251_);
lean_closure_set(v___f_4270_, 7, v_ctors_4252_);
lean_closure_set(v___f_4270_, 8, v_numIndices_4253_);
lean_closure_set(v___f_4270_, 9, v___x_4254_);
lean_closure_set(v___f_4270_, 10, v___x_4255_);
lean_closure_set(v___f_4270_, 11, v_val_4256_);
lean_closure_set(v___f_4270_, 12, v_declName_4257_);
lean_closure_set(v___f_4270_, 13, v_levelParams_4258_);
lean_closure_set(v___f_4270_, 14, v_numParams_4259_);
lean_closure_set(v___f_4270_, 15, v___x_4260_);
lean_closure_set(v___f_4270_, 16, v_t_4262_);
lean_closure_set(v___f_4270_, 17, v___x_4269_);
v___x_4271_ = 0;
v___x_4272_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4262_, v___x_4269_, v___f_4270_, v___x_4271_, v___x_4271_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4273_ = _args[0];
lean_object* v_indName_4274_ = _args[1];
lean_object* v_tail_4275_ = _args[2];
lean_object* v_params_4276_ = _args[3];
lean_object* v_head_4277_ = _args[4];
lean_object* v_ctors_4278_ = _args[5];
lean_object* v_numIndices_4279_ = _args[6];
lean_object* v___x_4280_ = _args[7];
lean_object* v___x_4281_ = _args[8];
lean_object* v_val_4282_ = _args[9];
lean_object* v_declName_4283_ = _args[10];
lean_object* v_levelParams_4284_ = _args[11];
lean_object* v_numParams_4285_ = _args[12];
lean_object* v___x_4286_ = _args[13];
lean_object* v_is_4287_ = _args[14];
lean_object* v_t_4288_ = _args[15];
lean_object* v___y_4289_ = _args[16];
lean_object* v___y_4290_ = _args[17];
lean_object* v___y_4291_ = _args[18];
lean_object* v___y_4292_ = _args[19];
lean_object* v___y_4293_ = _args[20];
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4273_, v_indName_4274_, v_tail_4275_, v_params_4276_, v_head_4277_, v_ctors_4278_, v_numIndices_4279_, v___x_4280_, v___x_4281_, v_val_4282_, v_declName_4283_, v_levelParams_4284_, v_numParams_4285_, v___x_4286_, v_is_4287_, v_t_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4295_, lean_object* v_indName_4296_, lean_object* v_tail_4297_, lean_object* v_head_4298_, lean_object* v_ctors_4299_, lean_object* v_numIndices_4300_, lean_object* v___x_4301_, lean_object* v___x_4302_, lean_object* v_val_4303_, lean_object* v_declName_4304_, lean_object* v_levelParams_4305_, lean_object* v_numParams_4306_, lean_object* v_params_4307_, lean_object* v_t_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; lean_object* v___f_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; lean_object* v___x_4318_; 
v___x_4314_ = l_Lean_Expr_bindingBody_x21(v_t_4308_);
lean_inc_ref(v___x_4314_);
lean_inc(v_numIndices_4300_);
v___f_4315_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4315_, 0, v___x_4295_);
lean_closure_set(v___f_4315_, 1, v_indName_4296_);
lean_closure_set(v___f_4315_, 2, v_tail_4297_);
lean_closure_set(v___f_4315_, 3, v_params_4307_);
lean_closure_set(v___f_4315_, 4, v_head_4298_);
lean_closure_set(v___f_4315_, 5, v_ctors_4299_);
lean_closure_set(v___f_4315_, 6, v_numIndices_4300_);
lean_closure_set(v___f_4315_, 7, v___x_4301_);
lean_closure_set(v___f_4315_, 8, v___x_4302_);
lean_closure_set(v___f_4315_, 9, v_val_4303_);
lean_closure_set(v___f_4315_, 10, v_declName_4304_);
lean_closure_set(v___f_4315_, 11, v_levelParams_4305_);
lean_closure_set(v___f_4315_, 12, v_numParams_4306_);
lean_closure_set(v___f_4315_, 13, v___x_4314_);
v___x_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4316_, 0, v_numIndices_4300_);
v___x_4317_ = 0;
v___x_4318_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4314_, v___x_4316_, v___f_4315_, v___x_4317_, v___x_4317_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
return v___x_4318_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4319_ = _args[0];
lean_object* v_indName_4320_ = _args[1];
lean_object* v_tail_4321_ = _args[2];
lean_object* v_head_4322_ = _args[3];
lean_object* v_ctors_4323_ = _args[4];
lean_object* v_numIndices_4324_ = _args[5];
lean_object* v___x_4325_ = _args[6];
lean_object* v___x_4326_ = _args[7];
lean_object* v_val_4327_ = _args[8];
lean_object* v_declName_4328_ = _args[9];
lean_object* v_levelParams_4329_ = _args[10];
lean_object* v_numParams_4330_ = _args[11];
lean_object* v_params_4331_ = _args[12];
lean_object* v_t_4332_ = _args[13];
lean_object* v___y_4333_ = _args[14];
lean_object* v___y_4334_ = _args[15];
lean_object* v___y_4335_ = _args[16];
lean_object* v___y_4336_ = _args[17];
lean_object* v___y_4337_ = _args[18];
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4319_, v_indName_4320_, v_tail_4321_, v_head_4322_, v_ctors_4323_, v_numIndices_4324_, v___x_4325_, v___x_4326_, v_val_4327_, v_declName_4328_, v_levelParams_4329_, v_numParams_4330_, v_params_4331_, v_t_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
lean_dec_ref(v_t_4332_);
return v_res_4338_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4343_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4344_ = lean_unsigned_to_nat(58u);
v___x_4345_ = lean_unsigned_to_nat(142u);
v___x_4346_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4347_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4348_ = l_mkPanicMessageWithDecl(v___x_4347_, v___x_4346_, v___x_4345_, v___x_4344_, v___x_4343_);
return v___x_4348_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4349_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4350_ = lean_unsigned_to_nat(60u);
v___x_4351_ = lean_unsigned_to_nat(136u);
v___x_4352_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4353_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4354_ = l_mkPanicMessageWithDecl(v___x_4353_, v___x_4352_, v___x_4351_, v___x_4350_, v___x_4349_);
return v___x_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4355_, lean_object* v_indName_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v___x_4362_; 
lean_inc(v_indName_4356_);
v___x_4362_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4362_, 1);
if (lean_obj_tag(v_a_4363_) == 5)
{
lean_object* v_val_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v_val_4364_ = lean_ctor_get(v_a_4363_, 0);
lean_inc_ref(v_val_4364_);
lean_dec_ref_known(v_a_4363_, 1);
v___x_4365_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4355_);
v___x_4366_ = l_Lean_Name_append(v_declName_4355_, v___x_4365_);
lean_inc(v_indName_4356_);
lean_inc(v___x_4366_);
v___x_4367_ = l_Lean_mkCasesOnSameCtorHet(v___x_4366_, v_indName_4356_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4400_; 
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4400_ == 0)
{
lean_object* v_unused_4401_; 
v_unused_4401_ = lean_ctor_get(v___x_4367_, 0);
lean_dec(v_unused_4401_);
v___x_4369_ = v___x_4367_;
v_isShared_4370_ = v_isSharedCheck_4400_;
goto v_resetjp_4368_;
}
else
{
lean_dec(v___x_4367_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4400_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; 
lean_inc(v_indName_4356_);
v___x_4371_ = l_Lean_mkCasesOnName(v_indName_4356_);
v___x_4372_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4371_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v_levelParams_4374_; lean_object* v_type_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_a_4373_);
lean_dec_ref_known(v___x_4372_, 1);
v_levelParams_4374_ = lean_ctor_get(v_a_4373_, 1);
lean_inc_n(v_levelParams_4374_, 2);
v_type_4375_ = lean_ctor_get(v_a_4373_, 2);
lean_inc_ref(v_type_4375_);
lean_dec(v_a_4373_);
v___x_4376_ = lean_box(0);
v___x_4377_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4374_, v___x_4376_);
if (lean_obj_tag(v___x_4377_) == 1)
{
lean_object* v_head_4378_; lean_object* v_tail_4379_; lean_object* v_numParams_4380_; lean_object* v_numIndices_4381_; lean_object* v_ctors_4382_; lean_object* v___x_4383_; lean_object* v___f_4384_; lean_object* v___x_4386_; 
v_head_4378_ = lean_ctor_get(v___x_4377_, 0);
lean_inc(v_head_4378_);
v_tail_4379_ = lean_ctor_get(v___x_4377_, 1);
lean_inc(v_tail_4379_);
v_numParams_4380_ = lean_ctor_get(v_val_4364_, 1);
lean_inc_n(v_numParams_4380_, 2);
v_numIndices_4381_ = lean_ctor_get(v_val_4364_, 2);
lean_inc(v_numIndices_4381_);
v_ctors_4382_ = lean_ctor_get(v_val_4364_, 4);
lean_inc(v_ctors_4382_);
v___x_4383_ = l_Lean_instInhabitedExpr;
v___f_4384_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4384_, 0, v___x_4383_);
lean_closure_set(v___f_4384_, 1, v_indName_4356_);
lean_closure_set(v___f_4384_, 2, v_tail_4379_);
lean_closure_set(v___f_4384_, 3, v_head_4378_);
lean_closure_set(v___f_4384_, 4, v_ctors_4382_);
lean_closure_set(v___f_4384_, 5, v_numIndices_4381_);
lean_closure_set(v___f_4384_, 6, v___x_4366_);
lean_closure_set(v___f_4384_, 7, v___x_4377_);
lean_closure_set(v___f_4384_, 8, v_val_4364_);
lean_closure_set(v___f_4384_, 9, v_declName_4355_);
lean_closure_set(v___f_4384_, 10, v_levelParams_4374_);
lean_closure_set(v___f_4384_, 11, v_numParams_4380_);
if (v_isShared_4370_ == 0)
{
lean_ctor_set_tag(v___x_4369_, 1);
lean_ctor_set(v___x_4369_, 0, v_numParams_4380_);
v___x_4386_ = v___x_4369_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_numParams_4380_);
v___x_4386_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
uint8_t v___x_4387_; lean_object* v___x_4388_; 
v___x_4387_ = 0;
v___x_4388_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4375_, v___x_4386_, v___f_4384_, v___x_4387_, v___x_4387_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
return v___x_4388_;
}
}
else
{
lean_object* v___x_4390_; lean_object* v___x_4391_; 
lean_dec(v___x_4377_);
lean_dec_ref(v_type_4375_);
lean_dec(v_levelParams_4374_);
lean_del_object(v___x_4369_);
lean_dec(v___x_4366_);
lean_dec_ref(v_val_4364_);
lean_dec(v_indName_4356_);
lean_dec(v_declName_4355_);
v___x_4390_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4391_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4390_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
return v___x_4391_;
}
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
lean_del_object(v___x_4369_);
lean_dec(v___x_4366_);
lean_dec_ref(v_val_4364_);
lean_dec(v_indName_4356_);
lean_dec(v_declName_4355_);
v_a_4392_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4372_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4372_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
}
else
{
lean_dec(v___x_4366_);
lean_dec_ref(v_val_4364_);
lean_dec(v_indName_4356_);
lean_dec(v_declName_4355_);
return v___x_4367_;
}
}
else
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
lean_dec(v_a_4363_);
lean_dec(v_indName_4356_);
lean_dec(v_declName_4355_);
v___x_4402_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4403_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4402_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
return v___x_4403_;
}
}
else
{
lean_object* v_a_4404_; lean_object* v___x_4406_; uint8_t v_isShared_4407_; uint8_t v_isSharedCheck_4411_; 
lean_dec(v_indName_4356_);
lean_dec(v_declName_4355_);
v_a_4404_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4411_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4411_ == 0)
{
v___x_4406_ = v___x_4362_;
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
else
{
lean_inc(v_a_4404_);
lean_dec(v___x_4362_);
v___x_4406_ = lean_box(0);
v_isShared_4407_ = v_isSharedCheck_4411_;
goto v_resetjp_4405_;
}
v_resetjp_4405_:
{
lean_object* v___x_4409_; 
if (v_isShared_4407_ == 0)
{
v___x_4409_ = v___x_4406_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_a_4404_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4412_, lean_object* v_indName_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_, lean_object* v_a_4418_){
_start:
{
lean_object* v_res_4419_; 
v_res_4419_ = l_Lean_mkCasesOnSameCtor(v_declName_4412_, v_indName_4413_, v_a_4414_, v_a_4415_, v_a_4416_, v_a_4417_);
lean_dec(v_a_4417_);
lean_dec_ref(v_a_4416_);
lean_dec(v_a_4415_);
lean_dec_ref(v_a_4414_);
return v_res_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4420_, lean_object* v_params_4421_, lean_object* v_motive_4422_, lean_object* v_as_4423_, size_t v_sz_4424_, size_t v_i_4425_, lean_object* v_bs_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v___x_4432_; 
v___x_4432_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4420_, v_params_4421_, v_motive_4422_, v_sz_4424_, v_i_4425_, v_bs_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
return v___x_4432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4433_, lean_object* v_params_4434_, lean_object* v_motive_4435_, lean_object* v_as_4436_, lean_object* v_sz_4437_, lean_object* v_i_4438_, lean_object* v_bs_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
size_t v_sz_boxed_4445_; size_t v_i_boxed_4446_; lean_object* v_res_4447_; 
v_sz_boxed_4445_ = lean_unbox_usize(v_sz_4437_);
lean_dec(v_sz_4437_);
v_i_boxed_4446_ = lean_unbox_usize(v_i_4438_);
lean_dec(v_i_4438_);
v_res_4447_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4433_, v_params_4434_, v_motive_4435_, v_as_4436_, v_sz_boxed_4445_, v_i_boxed_4446_, v_bs_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec_ref(v_as_4436_);
lean_dec_ref(v_params_4434_);
return v_res_4447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4448_, lean_object* v_params_4449_, lean_object* v_a_4450_, lean_object* v_snd_4451_, lean_object* v_alts_4452_, lean_object* v_as_4453_, size_t v_sz_4454_, size_t v_i_4455_, lean_object* v_bs_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v___x_4462_; 
v___x_4462_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4448_, v_params_4449_, v_a_4450_, v_snd_4451_, v_alts_4452_, v_sz_4454_, v_i_4455_, v_bs_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4463_, lean_object* v_params_4464_, lean_object* v_a_4465_, lean_object* v_snd_4466_, lean_object* v_alts_4467_, lean_object* v_as_4468_, lean_object* v_sz_4469_, lean_object* v_i_4470_, lean_object* v_bs_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
size_t v_sz_boxed_4477_; size_t v_i_boxed_4478_; lean_object* v_res_4479_; 
v_sz_boxed_4477_ = lean_unbox_usize(v_sz_4469_);
lean_dec(v_sz_4469_);
v_i_boxed_4478_ = lean_unbox_usize(v_i_4470_);
lean_dec(v_i_4470_);
v_res_4479_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4463_, v_params_4464_, v_a_4465_, v_snd_4466_, v_alts_4467_, v_as_4468_, v_sz_boxed_4477_, v_i_boxed_4478_, v_bs_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
lean_dec(v___y_4475_);
lean_dec_ref(v___y_4474_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec_ref(v_as_4468_);
lean_dec_ref(v_params_4464_);
return v_res_4479_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Constructions_CtorElim(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_App(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SameCtorUtils(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
