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
lean_object* v___x_345_; lean_object* v_env_346_; uint8_t v_isExporting_347_; lean_object* v___x_413_; uint8_t v_isModule_414_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_346_);
lean_dec(v___x_345_);
v_isExporting_347_ = lean_ctor_get_uint8(v_env_346_, sizeof(void*)*8);
v___x_413_ = l_Lean_Environment_header(v_env_346_);
lean_dec_ref(v_env_346_);
v_isModule_414_ = lean_ctor_get_uint8(v___x_413_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_413_);
if (v_isModule_414_ == 0)
{
lean_object* v___x_415_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v___x_415_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
return v___x_415_;
}
else
{
if (v_isExporting_347_ == 0)
{
if (v_isExporting_339_ == 0)
{
lean_object* v___x_416_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v___x_416_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
return v___x_416_;
}
else
{
goto v___jp_348_;
}
}
else
{
if (v_isExporting_339_ == 0)
{
goto v___jp_348_;
}
else
{
lean_object* v___x_417_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v___x_417_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
return v___x_417_;
}
}
}
v___jp_348_:
{
lean_object* v___x_349_; lean_object* v_env_350_; lean_object* v_nextMacroScope_351_; lean_object* v_ngen_352_; lean_object* v_auxDeclNGen_353_; lean_object* v_traceState_354_; lean_object* v_messages_355_; lean_object* v_infoState_356_; lean_object* v_snapshotTasks_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_411_; 
v___x_349_ = lean_st_ref_take(v___y_343_);
v_env_350_ = lean_ctor_get(v___x_349_, 0);
v_nextMacroScope_351_ = lean_ctor_get(v___x_349_, 1);
v_ngen_352_ = lean_ctor_get(v___x_349_, 2);
v_auxDeclNGen_353_ = lean_ctor_get(v___x_349_, 3);
v_traceState_354_ = lean_ctor_get(v___x_349_, 4);
v_messages_355_ = lean_ctor_get(v___x_349_, 6);
v_infoState_356_ = lean_ctor_get(v___x_349_, 7);
v_snapshotTasks_357_ = lean_ctor_get(v___x_349_, 8);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_349_, 5);
lean_dec(v_unused_412_);
v___x_359_ = v___x_349_;
v_isShared_360_ = v_isSharedCheck_411_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_snapshotTasks_357_);
lean_inc(v_infoState_356_);
lean_inc(v_messages_355_);
lean_inc(v_traceState_354_);
lean_inc(v_auxDeclNGen_353_);
lean_inc(v_ngen_352_);
lean_inc(v_nextMacroScope_351_);
lean_inc(v_env_350_);
lean_dec(v___x_349_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_411_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_361_ = l_Lean_Environment_setExporting(v_env_350_, v_isExporting_339_);
v___x_362_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 5, v___x_362_);
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_364_ = v___x_359_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_361_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_nextMacroScope_351_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_ngen_352_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_auxDeclNGen_353_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_traceState_354_);
lean_ctor_set(v_reuseFailAlloc_410_, 5, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_410_, 6, v_messages_355_);
lean_ctor_set(v_reuseFailAlloc_410_, 7, v_infoState_356_);
lean_ctor_set(v_reuseFailAlloc_410_, 8, v_snapshotTasks_357_);
v___x_364_ = v_reuseFailAlloc_410_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v_mctx_367_; lean_object* v_zetaDeltaFVarIds_368_; lean_object* v_postponed_369_; lean_object* v_diag_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_408_; 
v___x_365_ = lean_st_ref_set(v___y_343_, v___x_364_);
v___x_366_ = lean_st_ref_take(v___y_341_);
v_mctx_367_ = lean_ctor_get(v___x_366_, 0);
v_zetaDeltaFVarIds_368_ = lean_ctor_get(v___x_366_, 2);
v_postponed_369_ = lean_ctor_get(v___x_366_, 3);
v_diag_370_ = lean_ctor_get(v___x_366_, 4);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_408_ == 0)
{
lean_object* v_unused_409_; 
v_unused_409_ = lean_ctor_get(v___x_366_, 1);
lean_dec(v_unused_409_);
v___x_372_ = v___x_366_;
v_isShared_373_ = v_isSharedCheck_408_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_diag_370_);
lean_inc(v_postponed_369_);
lean_inc(v_zetaDeltaFVarIds_368_);
lean_inc(v_mctx_367_);
lean_dec(v___x_366_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_408_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v___x_374_);
v___x_376_ = v___x_372_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_mctx_367_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_zetaDeltaFVarIds_368_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v_postponed_369_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_diag_370_);
v___x_376_ = v_reuseFailAlloc_407_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v_r_378_; 
v___x_377_ = lean_st_ref_set(v___y_341_, v___x_376_);
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v_r_378_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
if (lean_obj_tag(v_r_378_) == 0)
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_395_; 
v_a_379_ = lean_ctor_get(v_r_378_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v_r_378_);
if (v_isSharedCheck_395_ == 0)
{
v___x_381_ = v_r_378_;
v_isShared_382_ = v_isSharedCheck_395_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v_r_378_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_395_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
lean_inc(v_a_379_);
if (v_isShared_382_ == 0)
{
lean_ctor_set_tag(v___x_381_, 1);
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_394_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v___x_385_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_347_, v___x_362_, v___y_341_, v___x_374_, v___x_384_);
lean_dec_ref(v___x_384_);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; 
v_unused_393_ = lean_ctor_get(v___x_385_, 0);
lean_dec(v_unused_393_);
v___x_387_ = v___x_385_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_dec(v___x_385_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v_a_379_);
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_379_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
}
else
{
lean_object* v_a_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
v_a_396_ = lean_ctor_get(v_r_378_, 0);
lean_inc(v_a_396_);
lean_dec_ref_known(v_r_378_, 1);
v___x_397_ = lean_box(0);
v___x_398_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_347_, v___x_362_, v___y_341_, v___x_374_, v___x_397_);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; 
v_unused_406_ = lean_ctor_get(v___x_398_, 0);
lean_dec(v_unused_406_);
v___x_400_ = v___x_398_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_dec(v___x_398_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set_tag(v___x_400_, 1);
lean_ctor_set(v___x_400_, 0, v_a_396_);
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_396_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_418_, lean_object* v_isExporting_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v_isExporting_boxed_425_; lean_object* v_res_426_; 
v_isExporting_boxed_425_ = lean_unbox(v_isExporting_419_);
v_res_426_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_418_, v_isExporting_boxed_425_, v___y_420_, v___y_421_, v___y_422_, v___y_423_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_427_, lean_object* v_x_428_, uint8_t v_isExporting_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_428_, v_isExporting_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_436_, lean_object* v_x_437_, lean_object* v_isExporting_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v_isExporting_boxed_444_; lean_object* v_res_445_; 
v_isExporting_boxed_444_ = lean_unbox(v_isExporting_438_);
v_res_445_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_436_, v_x_437_, v_isExporting_boxed_444_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_msg_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___f_453_; lean_object* v___x_15668__overap_454_; lean_object* v___x_455_; 
v___f_453_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15668__overap_454_ = lean_panic_fn_borrowed(v___f_453_, v_msg_447_);
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
lean_inc(v___y_449_);
lean_inc_ref(v___y_448_);
v___x_455_ = lean_apply_5(v___x_15668__overap_454_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, lean_box(0));
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_msg_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_msg_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object* v_name_463_, lean_object* v_type_464_, lean_object* v_k_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
uint8_t v___x_471_; uint8_t v___x_472_; lean_object* v___x_473_; 
v___x_471_ = 0;
v___x_472_ = 0;
v___x_473_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_463_, v___x_471_, v_type_464_, v_k_465_, v___x_472_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object* v_name_474_, lean_object* v_type_475_, lean_object* v_k_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_474_, v_type_475_, v_k_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object* v___x_483_, lean_object* v_ism2_484_, lean_object* v_motive_485_, uint8_t v___x_486_, uint8_t v___x_487_, uint8_t v___x_488_, lean_object* v_a_489_, lean_object* v___f_490_, lean_object* v_zs1_491_, lean_object* v_val_492_, lean_object* v___x_493_, lean_object* v_indName_494_, lean_object* v_v_495_, lean_object* v___x_496_, lean_object* v_params_497_, lean_object* v___x_498_, lean_object* v_h_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = l_Array_append___redArg(v___x_483_, v_ism2_484_);
v___x_506_ = l_Lean_mkAppN(v_motive_485_, v___x_505_);
lean_dec_ref(v___x_505_);
v___x_507_ = l_Lean_Meta_mkLambdaFVars(v_ism2_484_, v___x_506_, v___x_486_, v___x_487_, v___x_486_, v___x_487_, v___x_488_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v___x_509_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_489_, v___f_490_, v___x_486_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___y_512_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
lean_inc(v_a_510_);
lean_dec_ref_known(v___x_509_, 1);
v___x_515_ = l_Lean_InductiveVal_numCtors(v_val_492_);
v___x_516_ = lean_nat_dec_eq(v___x_515_, v___x_493_);
lean_dec(v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v___x_498_);
v___x_517_ = l_Lean_mkConstructorElimName(v_indName_494_, v_v_495_);
v___x_518_ = l_Lean_mkConst(v___x_517_, v___x_496_);
v___x_519_ = lean_mk_empty_array_with_capacity(v___x_493_);
v___x_520_ = lean_array_push(v___x_519_, v_a_508_);
v___x_521_ = l_Array_append___redArg(v_params_497_, v___x_520_);
lean_dec_ref(v___x_520_);
v___x_522_ = l_Array_append___redArg(v___x_521_, v_ism2_484_);
v___x_523_ = lean_unsigned_to_nat(2u);
v___x_524_ = lean_mk_empty_array_with_capacity(v___x_523_);
lean_inc_ref(v_h_499_);
v___x_525_ = lean_array_push(v___x_524_, v_h_499_);
v___x_526_ = lean_array_push(v___x_525_, v_a_510_);
v___x_527_ = l_Array_append___redArg(v___x_522_, v___x_526_);
lean_dec_ref(v___x_526_);
v___x_528_ = l_Lean_mkAppN(v___x_518_, v___x_527_);
lean_dec_ref(v___x_527_);
v___y_512_ = v___x_528_;
goto v___jp_511_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_v_495_);
v___x_529_ = l_Lean_mkConst(v___x_498_, v___x_496_);
v___x_530_ = lean_mk_empty_array_with_capacity(v___x_493_);
lean_inc_ref(v___x_530_);
v___x_531_ = lean_array_push(v___x_530_, v_a_508_);
v___x_532_ = l_Array_append___redArg(v_params_497_, v___x_531_);
lean_dec_ref(v___x_531_);
v___x_533_ = l_Array_append___redArg(v___x_532_, v_ism2_484_);
v___x_534_ = lean_array_push(v___x_530_, v_a_510_);
v___x_535_ = l_Array_append___redArg(v___x_533_, v___x_534_);
lean_dec_ref(v___x_534_);
v___x_536_ = l_Lean_mkAppN(v___x_529_, v___x_535_);
lean_dec_ref(v___x_535_);
v___y_512_ = v___x_536_;
goto v___jp_511_;
}
v___jp_511_:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_array_push(v_zs1_491_, v_h_499_);
v___x_514_ = l_Lean_Meta_mkLambdaFVars(v___x_513_, v___y_512_, v___x_486_, v___x_487_, v___x_486_, v___x_487_, v___x_488_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec_ref(v___x_513_);
return v___x_514_;
}
}
else
{
lean_dec(v_a_508_);
lean_dec_ref(v_h_499_);
lean_dec(v___x_498_);
lean_dec_ref(v_params_497_);
lean_dec(v___x_496_);
lean_dec(v_v_495_);
lean_dec_ref(v_zs1_491_);
return v___x_509_;
}
}
else
{
lean_dec_ref(v_h_499_);
lean_dec(v___x_498_);
lean_dec_ref(v_params_497_);
lean_dec(v___x_496_);
lean_dec(v_v_495_);
lean_dec_ref(v_zs1_491_);
lean_dec_ref(v___f_490_);
lean_dec_ref(v_a_489_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_537_ = _args[0];
lean_object* v_ism2_538_ = _args[1];
lean_object* v_motive_539_ = _args[2];
lean_object* v___x_540_ = _args[3];
lean_object* v___x_541_ = _args[4];
lean_object* v___x_542_ = _args[5];
lean_object* v_a_543_ = _args[6];
lean_object* v___f_544_ = _args[7];
lean_object* v_zs1_545_ = _args[8];
lean_object* v_val_546_ = _args[9];
lean_object* v___x_547_ = _args[10];
lean_object* v_indName_548_ = _args[11];
lean_object* v_v_549_ = _args[12];
lean_object* v___x_550_ = _args[13];
lean_object* v_params_551_ = _args[14];
lean_object* v___x_552_ = _args[15];
lean_object* v_h_553_ = _args[16];
lean_object* v___y_554_ = _args[17];
lean_object* v___y_555_ = _args[18];
lean_object* v___y_556_ = _args[19];
lean_object* v___y_557_ = _args[20];
lean_object* v___y_558_ = _args[21];
_start:
{
uint8_t v___x_20771__boxed_559_; uint8_t v___x_20772__boxed_560_; uint8_t v___x_20773__boxed_561_; lean_object* v_res_562_; 
v___x_20771__boxed_559_ = lean_unbox(v___x_540_);
v___x_20772__boxed_560_ = lean_unbox(v___x_541_);
v___x_20773__boxed_561_ = lean_unbox(v___x_542_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_537_, v_ism2_538_, v_motive_539_, v___x_20771__boxed_559_, v___x_20772__boxed_560_, v___x_20773__boxed_561_, v_a_543_, v___f_544_, v_zs1_545_, v_val_546_, v___x_547_, v_indName_548_, v_v_549_, v___x_550_, v_params_551_, v___x_552_, v_h_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v_indName_548_);
lean_dec(v___x_547_);
lean_dec_ref(v_val_546_);
lean_dec_ref(v_ism2_538_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object* v___x_563_, lean_object* v_alts_564_, lean_object* v___x_565_, lean_object* v_zs1_566_, uint8_t v___x_567_, uint8_t v___x_568_, uint8_t v___x_569_, lean_object* v_zs2_570_, lean_object* v_x_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_577_ = lean_array_get_borrowed(v___x_563_, v_alts_564_, v___x_565_);
v___x_578_ = l_Array_append___redArg(v_zs1_566_, v_zs2_570_);
lean_inc(v___x_577_);
v___x_579_ = l_Lean_mkAppN(v___x_577_, v___x_578_);
lean_dec_ref(v___x_578_);
v___x_580_ = l_Lean_Meta_mkLambdaFVars(v_zs2_570_, v___x_579_, v___x_567_, v___x_568_, v___x_567_, v___x_568_, v___x_569_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object* v___x_581_, lean_object* v_alts_582_, lean_object* v___x_583_, lean_object* v_zs1_584_, lean_object* v___x_585_, lean_object* v___x_586_, lean_object* v___x_587_, lean_object* v_zs2_588_, lean_object* v_x_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
uint8_t v___x_20883__boxed_595_; uint8_t v___x_20884__boxed_596_; uint8_t v___x_20885__boxed_597_; lean_object* v_res_598_; 
v___x_20883__boxed_595_ = lean_unbox(v___x_585_);
v___x_20884__boxed_596_ = lean_unbox(v___x_586_);
v___x_20885__boxed_597_ = lean_unbox(v___x_587_);
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_581_, v_alts_582_, v___x_583_, v_zs1_584_, v___x_20883__boxed_595_, v___x_20884__boxed_596_, v___x_20885__boxed_597_, v_zs2_588_, v_x_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec_ref(v_x_589_);
lean_dec_ref(v_zs2_588_);
lean_dec(v___x_583_);
lean_dec_ref(v_alts_582_);
lean_dec_ref(v___x_581_);
return v_res_598_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_599_; lean_object* v_dummy_600_; 
v___x_599_ = lean_box(0);
v_dummy_600_ = l_Lean_Expr_sort___override(v___x_599_);
return v_dummy_600_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_607_ = lean_box(0);
v___x_608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4));
v___x_609_ = l_Lean_mkConst(v___x_608_, v___x_607_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object* v___x_610_, lean_object* v_alts_611_, lean_object* v___x_612_, uint8_t v___x_613_, uint8_t v___x_614_, uint8_t v___x_615_, lean_object* v___x_616_, lean_object* v___x_617_, lean_object* v___x_618_, lean_object* v_ism2_619_, lean_object* v_motive_620_, lean_object* v_a_621_, lean_object* v_val_622_, lean_object* v_indName_623_, lean_object* v_v_624_, lean_object* v___x_625_, lean_object* v_params_626_, lean_object* v___x_627_, lean_object* v___x_628_, lean_object* v___x_629_, lean_object* v_zs1_630_, lean_object* v_ctorRet1_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; 
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
lean_inc(v___y_633_);
lean_inc_ref(v___y_632_);
v___x_637_ = lean_whnf(v_ctorRet1_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___f_642_; lean_object* v___x_643_; lean_object* v_dummy_644_; lean_object* v_nargs_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___f_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
v___x_639_ = lean_box(v___x_613_);
v___x_640_ = lean_box(v___x_614_);
v___x_641_ = lean_box(v___x_615_);
lean_inc_ref(v_zs1_630_);
lean_inc(v___x_612_);
v___f_642_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_642_, 0, v___x_610_);
lean_closure_set(v___f_642_, 1, v_alts_611_);
lean_closure_set(v___f_642_, 2, v___x_612_);
lean_closure_set(v___f_642_, 3, v_zs1_630_);
lean_closure_set(v___f_642_, 4, v___x_639_);
lean_closure_set(v___f_642_, 5, v___x_640_);
lean_closure_set(v___f_642_, 6, v___x_641_);
v___x_643_ = l_Lean_mkAppN(v___x_616_, v_zs1_630_);
v_dummy_644_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_645_ = l_Lean_Expr_getAppNumArgs(v_a_638_);
lean_inc(v_nargs_645_);
v___x_646_ = lean_mk_array(v_nargs_645_, v_dummy_644_);
v___x_647_ = lean_nat_sub(v_nargs_645_, v___x_617_);
lean_dec(v_nargs_645_);
v___x_648_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_638_, v___x_646_, v___x_647_);
v___x_649_ = lean_array_get_size(v___x_648_);
v___x_650_ = l_Array_toSubarray___redArg(v___x_648_, v___x_618_, v___x_649_);
v___x_651_ = l_Subarray_copy___redArg(v___x_650_);
v___x_652_ = lean_array_push(v___x_651_, v___x_643_);
v___x_653_ = lean_box(v___x_613_);
v___x_654_ = lean_box(v___x_614_);
v___x_655_ = lean_box(v___x_615_);
lean_inc(v___x_617_);
v___f_656_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed), 22, 16);
lean_closure_set(v___f_656_, 0, v___x_652_);
lean_closure_set(v___f_656_, 1, v_ism2_619_);
lean_closure_set(v___f_656_, 2, v_motive_620_);
lean_closure_set(v___f_656_, 3, v___x_653_);
lean_closure_set(v___f_656_, 4, v___x_654_);
lean_closure_set(v___f_656_, 5, v___x_655_);
lean_closure_set(v___f_656_, 6, v_a_621_);
lean_closure_set(v___f_656_, 7, v___f_642_);
lean_closure_set(v___f_656_, 8, v_zs1_630_);
lean_closure_set(v___f_656_, 9, v_val_622_);
lean_closure_set(v___f_656_, 10, v___x_617_);
lean_closure_set(v___f_656_, 11, v_indName_623_);
lean_closure_set(v___f_656_, 12, v_v_624_);
lean_closure_set(v___f_656_, 13, v___x_625_);
lean_closure_set(v___f_656_, 14, v_params_626_);
lean_closure_set(v___f_656_, 15, v___x_627_);
v___x_657_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2));
v___x_658_ = l_Lean_Level_ofNat(v___x_617_);
lean_dec(v___x_617_);
v___x_659_ = lean_box(0);
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = l_Lean_mkConst(v___x_657_, v___x_660_);
v___x_662_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
v___x_663_ = l_Lean_mkRawNatLit(v___x_612_);
v___x_664_ = l_Lean_mkApp3(v___x_661_, v___x_662_, v___x_628_, v___x_663_);
v___x_665_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_629_, v___x_664_, v___f_656_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
return v___x_665_;
}
else
{
lean_dec_ref(v_zs1_630_);
lean_dec(v___x_629_);
lean_dec_ref(v___x_628_);
lean_dec(v___x_627_);
lean_dec_ref(v_params_626_);
lean_dec(v___x_625_);
lean_dec(v_v_624_);
lean_dec(v_indName_623_);
lean_dec_ref(v_val_622_);
lean_dec_ref(v_a_621_);
lean_dec_ref(v_motive_620_);
lean_dec_ref(v_ism2_619_);
lean_dec(v___x_618_);
lean_dec(v___x_617_);
lean_dec_ref(v___x_616_);
lean_dec(v___x_612_);
lean_dec_ref(v_alts_611_);
lean_dec_ref(v___x_610_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_666_ = _args[0];
lean_object* v_alts_667_ = _args[1];
lean_object* v___x_668_ = _args[2];
lean_object* v___x_669_ = _args[3];
lean_object* v___x_670_ = _args[4];
lean_object* v___x_671_ = _args[5];
lean_object* v___x_672_ = _args[6];
lean_object* v___x_673_ = _args[7];
lean_object* v___x_674_ = _args[8];
lean_object* v_ism2_675_ = _args[9];
lean_object* v_motive_676_ = _args[10];
lean_object* v_a_677_ = _args[11];
lean_object* v_val_678_ = _args[12];
lean_object* v_indName_679_ = _args[13];
lean_object* v_v_680_ = _args[14];
lean_object* v___x_681_ = _args[15];
lean_object* v_params_682_ = _args[16];
lean_object* v___x_683_ = _args[17];
lean_object* v___x_684_ = _args[18];
lean_object* v___x_685_ = _args[19];
lean_object* v_zs1_686_ = _args[20];
lean_object* v_ctorRet1_687_ = _args[21];
lean_object* v___y_688_ = _args[22];
lean_object* v___y_689_ = _args[23];
lean_object* v___y_690_ = _args[24];
lean_object* v___y_691_ = _args[25];
lean_object* v___y_692_ = _args[26];
_start:
{
uint8_t v___x_20944__boxed_693_; uint8_t v___x_20945__boxed_694_; uint8_t v___x_20946__boxed_695_; lean_object* v_res_696_; 
v___x_20944__boxed_693_ = lean_unbox(v___x_669_);
v___x_20945__boxed_694_ = lean_unbox(v___x_670_);
v___x_20946__boxed_695_ = lean_unbox(v___x_671_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_666_, v_alts_667_, v___x_668_, v___x_20944__boxed_693_, v___x_20945__boxed_694_, v___x_20946__boxed_695_, v___x_672_, v___x_673_, v___x_674_, v_ism2_675_, v_motive_676_, v_a_677_, v_val_678_, v_indName_679_, v_v_680_, v___x_681_, v_params_682_, v___x_683_, v___x_684_, v___x_685_, v_zs1_686_, v_ctorRet1_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object* v_tail_700_, lean_object* v_params_701_, lean_object* v_alts_702_, lean_object* v___x_703_, lean_object* v_ism2_704_, lean_object* v_motive_705_, lean_object* v_val_706_, lean_object* v_indName_707_, lean_object* v___x_708_, lean_object* v___x_709_, lean_object* v___x_710_, size_t v_sz_711_, size_t v_i_712_, lean_object* v_bs_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___x_719_; 
v___x_719_ = lean_usize_dec_lt(v_i_712_, v_sz_711_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec_ref(v___x_710_);
lean_dec(v___x_709_);
lean_dec(v___x_708_);
lean_dec(v_indName_707_);
lean_dec_ref(v_val_706_);
lean_dec_ref(v_motive_705_);
lean_dec_ref(v_ism2_704_);
lean_dec(v___x_703_);
lean_dec_ref(v_alts_702_);
lean_dec_ref(v_params_701_);
lean_dec(v_tail_700_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v_bs_713_);
return v___x_720_;
}
else
{
lean_object* v_v_721_; lean_object* v___x_722_; lean_object* v_bs_x27_723_; lean_object* v___y_725_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_v_721_ = lean_array_uget(v_bs_713_, v_i_712_);
v___x_722_ = lean_unsigned_to_nat(0u);
v_bs_x27_723_ = lean_array_uset(v_bs_713_, v_i_712_, v___x_722_);
lean_inc(v_tail_700_);
lean_inc(v_v_721_);
v___x_739_ = l_Lean_mkConst(v_v_721_, v_tail_700_);
v___x_740_ = l_Lean_mkAppN(v___x_739_, v_params_701_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc(v___y_715_);
lean_inc_ref(v___y_714_);
lean_inc_ref(v___x_740_);
v___x_741_ = lean_infer_type(v___x_740_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; uint8_t v___x_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___f_752_; lean_object* v___x_753_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc_n(v_a_742_, 2);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = l_Lean_instInhabitedExpr;
v___x_744_ = 0;
v___x_745_ = 1;
v___x_746_ = lean_unsigned_to_nat(1u);
v___x_747_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_748_ = lean_usize_to_nat(v_i_712_);
v___x_749_ = lean_box(v___x_744_);
v___x_750_ = lean_box(v___x_719_);
v___x_751_ = lean_box(v___x_745_);
lean_inc_ref(v___x_710_);
lean_inc(v___x_709_);
lean_inc_ref(v_params_701_);
lean_inc(v___x_708_);
lean_inc(v_indName_707_);
lean_inc_ref(v_val_706_);
lean_inc_ref(v_motive_705_);
lean_inc_ref(v_ism2_704_);
lean_inc(v___x_703_);
lean_inc_ref(v_alts_702_);
v___f_752_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed), 27, 20);
lean_closure_set(v___f_752_, 0, v___x_743_);
lean_closure_set(v___f_752_, 1, v_alts_702_);
lean_closure_set(v___f_752_, 2, v___x_748_);
lean_closure_set(v___f_752_, 3, v___x_749_);
lean_closure_set(v___f_752_, 4, v___x_750_);
lean_closure_set(v___f_752_, 5, v___x_751_);
lean_closure_set(v___f_752_, 6, v___x_740_);
lean_closure_set(v___f_752_, 7, v___x_746_);
lean_closure_set(v___f_752_, 8, v___x_703_);
lean_closure_set(v___f_752_, 9, v_ism2_704_);
lean_closure_set(v___f_752_, 10, v_motive_705_);
lean_closure_set(v___f_752_, 11, v_a_742_);
lean_closure_set(v___f_752_, 12, v_val_706_);
lean_closure_set(v___f_752_, 13, v_indName_707_);
lean_closure_set(v___f_752_, 14, v_v_721_);
lean_closure_set(v___f_752_, 15, v___x_708_);
lean_closure_set(v___f_752_, 16, v_params_701_);
lean_closure_set(v___f_752_, 17, v___x_709_);
lean_closure_set(v___f_752_, 18, v___x_710_);
lean_closure_set(v___f_752_, 19, v___x_747_);
v___x_753_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_742_, v___f_752_, v___x_744_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
v___y_725_ = v___x_753_;
goto v___jp_724_;
}
else
{
lean_dec_ref(v___x_740_);
lean_dec(v_v_721_);
v___y_725_ = v___x_741_;
goto v___jp_724_;
}
v___jp_724_:
{
if (lean_obj_tag(v___y_725_) == 0)
{
lean_object* v_a_726_; size_t v___x_727_; size_t v___x_728_; lean_object* v___x_729_; 
v_a_726_ = lean_ctor_get(v___y_725_, 0);
lean_inc(v_a_726_);
lean_dec_ref_known(v___y_725_, 1);
v___x_727_ = ((size_t)1ULL);
v___x_728_ = lean_usize_add(v_i_712_, v___x_727_);
v___x_729_ = lean_array_uset(v_bs_x27_723_, v_i_712_, v_a_726_);
v_i_712_ = v___x_728_;
v_bs_713_ = v___x_729_;
goto _start;
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec_ref(v_bs_x27_723_);
lean_dec_ref(v___x_710_);
lean_dec(v___x_709_);
lean_dec(v___x_708_);
lean_dec(v_indName_707_);
lean_dec_ref(v_val_706_);
lean_dec_ref(v_motive_705_);
lean_dec_ref(v_ism2_704_);
lean_dec(v___x_703_);
lean_dec_ref(v_alts_702_);
lean_dec_ref(v_params_701_);
lean_dec(v_tail_700_);
v_a_731_ = lean_ctor_get(v___y_725_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___y_725_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___y_725_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___y_725_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_tail_754_ = _args[0];
lean_object* v_params_755_ = _args[1];
lean_object* v_alts_756_ = _args[2];
lean_object* v___x_757_ = _args[3];
lean_object* v_ism2_758_ = _args[4];
lean_object* v_motive_759_ = _args[5];
lean_object* v_val_760_ = _args[6];
lean_object* v_indName_761_ = _args[7];
lean_object* v___x_762_ = _args[8];
lean_object* v___x_763_ = _args[9];
lean_object* v___x_764_ = _args[10];
lean_object* v_sz_765_ = _args[11];
lean_object* v_i_766_ = _args[12];
lean_object* v_bs_767_ = _args[13];
lean_object* v___y_768_ = _args[14];
lean_object* v___y_769_ = _args[15];
lean_object* v___y_770_ = _args[16];
lean_object* v___y_771_ = _args[17];
lean_object* v___y_772_ = _args[18];
_start:
{
size_t v_sz_boxed_773_; size_t v_i_boxed_774_; lean_object* v_res_775_; 
v_sz_boxed_773_ = lean_unbox_usize(v_sz_765_);
lean_dec(v_sz_765_);
v_i_boxed_774_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_754_, v_params_755_, v_alts_756_, v___x_757_, v_ism2_758_, v_motive_759_, v_val_760_, v_indName_761_, v___x_762_, v___x_763_, v___x_764_, v_sz_boxed_773_, v_i_boxed_774_, v_bs_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_776_, lean_object* v___x_777_, lean_object* v_a_778_, lean_object* v_ism1_779_, uint8_t v___x_780_, uint8_t v___x_781_, uint8_t v___x_782_, lean_object* v___x_783_, lean_object* v_tail_784_, lean_object* v_params_785_, lean_object* v_alts_786_, lean_object* v_numParams_787_, lean_object* v_ism2_788_, lean_object* v_val_789_, lean_object* v_indName_790_, lean_object* v___x_791_, lean_object* v___x_792_, lean_object* v___x_793_, lean_object* v_name_794_, lean_object* v___x_795_, lean_object* v_heq_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_inc_ref(v_motive_776_);
v___x_802_ = l_Lean_mkAppN(v_motive_776_, v___x_777_);
v___x_803_ = l_Lean_mkArrow(v_a_778_, v___x_802_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v___x_805_ = l_Lean_Meta_mkLambdaFVars(v_ism1_779_, v_a_804_, v___x_780_, v___x_781_, v___x_780_, v___x_781_, v___x_782_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; size_t v_sz_807_; size_t v___x_808_; lean_object* v___x_809_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v_sz_807_ = lean_array_size(v___x_783_);
v___x_808_ = ((size_t)0ULL);
lean_inc(v___x_791_);
lean_inc_ref(v_motive_776_);
lean_inc_ref(v_ism2_788_);
lean_inc_ref(v_alts_786_);
lean_inc_ref(v_params_785_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_784_, v_params_785_, v_alts_786_, v_numParams_787_, v_ism2_788_, v_motive_776_, v_val_789_, v_indName_790_, v___x_791_, v___x_792_, v___x_793_, v_sz_807_, v___x_808_, v___x_783_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_811_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
lean_inc_ref(v_heq_796_);
v___x_811_ = l_Lean_Meta_mkEqSymm(v_heq_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = l_Lean_mkConst(v_name_794_, v___x_791_);
v___x_814_ = l_Lean_mkAppN(v___x_813_, v_params_785_);
v___x_815_ = l_Lean_Expr_app___override(v___x_814_, v_a_806_);
v___x_816_ = l_Lean_mkAppN(v___x_815_, v_ism1_779_);
v___x_817_ = l_Lean_mkAppN(v___x_816_, v_a_810_);
lean_dec(v_a_810_);
v___x_818_ = l_Lean_Expr_app___override(v___x_817_, v_a_812_);
v___x_819_ = lean_mk_empty_array_with_capacity(v___x_795_);
lean_inc_ref(v___x_819_);
v___x_820_ = lean_array_push(v___x_819_, v_motive_776_);
v___x_821_ = l_Array_append___redArg(v_params_785_, v___x_820_);
lean_dec_ref(v___x_820_);
v___x_822_ = l_Array_append___redArg(v___x_821_, v_ism1_779_);
v___x_823_ = l_Array_append___redArg(v___x_822_, v_ism2_788_);
lean_dec_ref(v_ism2_788_);
v___x_824_ = lean_array_push(v___x_819_, v_heq_796_);
v___x_825_ = l_Array_append___redArg(v___x_823_, v___x_824_);
lean_dec_ref(v___x_824_);
v___x_826_ = l_Array_append___redArg(v___x_825_, v_alts_786_);
lean_dec_ref(v_alts_786_);
v___x_827_ = l_Lean_Meta_mkLambdaFVars(v___x_826_, v___x_818_, v___x_780_, v___x_781_, v___x_780_, v___x_781_, v___x_782_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec_ref(v___x_826_);
return v___x_827_;
}
else
{
lean_dec(v_a_810_);
lean_dec(v_a_806_);
lean_dec_ref(v_heq_796_);
lean_dec(v_name_794_);
lean_dec(v___x_791_);
lean_dec_ref(v_ism2_788_);
lean_dec_ref(v_alts_786_);
lean_dec_ref(v_params_785_);
lean_dec_ref(v_motive_776_);
return v___x_811_;
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v_a_806_);
lean_dec_ref(v_heq_796_);
lean_dec(v_name_794_);
lean_dec(v___x_791_);
lean_dec_ref(v_ism2_788_);
lean_dec_ref(v_alts_786_);
lean_dec_ref(v_params_785_);
lean_dec_ref(v_motive_776_);
v_a_828_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_809_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_809_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
else
{
lean_dec_ref(v_heq_796_);
lean_dec(v_name_794_);
lean_dec_ref(v___x_793_);
lean_dec(v___x_792_);
lean_dec(v___x_791_);
lean_dec(v_indName_790_);
lean_dec_ref(v_val_789_);
lean_dec_ref(v_ism2_788_);
lean_dec(v_numParams_787_);
lean_dec_ref(v_alts_786_);
lean_dec_ref(v_params_785_);
lean_dec(v_tail_784_);
lean_dec_ref(v___x_783_);
lean_dec_ref(v_motive_776_);
return v___x_805_;
}
}
else
{
lean_dec_ref(v_heq_796_);
lean_dec(v_name_794_);
lean_dec_ref(v___x_793_);
lean_dec(v___x_792_);
lean_dec(v___x_791_);
lean_dec(v_indName_790_);
lean_dec_ref(v_val_789_);
lean_dec_ref(v_ism2_788_);
lean_dec(v_numParams_787_);
lean_dec_ref(v_alts_786_);
lean_dec_ref(v_params_785_);
lean_dec(v_tail_784_);
lean_dec_ref(v___x_783_);
lean_dec_ref(v_motive_776_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object** _args){
lean_object* v_motive_836_ = _args[0];
lean_object* v___x_837_ = _args[1];
lean_object* v_a_838_ = _args[2];
lean_object* v_ism1_839_ = _args[3];
lean_object* v___x_840_ = _args[4];
lean_object* v___x_841_ = _args[5];
lean_object* v___x_842_ = _args[6];
lean_object* v___x_843_ = _args[7];
lean_object* v_tail_844_ = _args[8];
lean_object* v_params_845_ = _args[9];
lean_object* v_alts_846_ = _args[10];
lean_object* v_numParams_847_ = _args[11];
lean_object* v_ism2_848_ = _args[12];
lean_object* v_val_849_ = _args[13];
lean_object* v_indName_850_ = _args[14];
lean_object* v___x_851_ = _args[15];
lean_object* v___x_852_ = _args[16];
lean_object* v___x_853_ = _args[17];
lean_object* v_name_854_ = _args[18];
lean_object* v___x_855_ = _args[19];
lean_object* v_heq_856_ = _args[20];
lean_object* v___y_857_ = _args[21];
lean_object* v___y_858_ = _args[22];
lean_object* v___y_859_ = _args[23];
lean_object* v___y_860_ = _args[24];
lean_object* v___y_861_ = _args[25];
_start:
{
uint8_t v___x_21175__boxed_862_; uint8_t v___x_21176__boxed_863_; uint8_t v___x_21177__boxed_864_; lean_object* v_res_865_; 
v___x_21175__boxed_862_ = lean_unbox(v___x_840_);
v___x_21176__boxed_863_ = lean_unbox(v___x_841_);
v___x_21177__boxed_864_ = lean_unbox(v___x_842_);
v_res_865_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_836_, v___x_837_, v_a_838_, v_ism1_839_, v___x_21175__boxed_862_, v___x_21176__boxed_863_, v___x_21177__boxed_864_, v___x_843_, v_tail_844_, v_params_845_, v_alts_846_, v_numParams_847_, v_ism2_848_, v_val_849_, v_indName_850_, v___x_851_, v___x_852_, v___x_853_, v_name_854_, v___x_855_, v_heq_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___x_855_);
lean_dec_ref(v_ism1_839_);
lean_dec_ref(v___x_837_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_866_, lean_object* v_tail_867_, lean_object* v_params_868_, lean_object* v_ism1_869_, lean_object* v_ism2_870_, lean_object* v_motive_871_, lean_object* v___x_872_, uint8_t v___x_873_, uint8_t v___x_874_, uint8_t v___x_875_, lean_object* v___x_876_, lean_object* v_numParams_877_, lean_object* v_val_878_, lean_object* v___x_879_, lean_object* v___x_880_, lean_object* v_name_881_, lean_object* v___x_882_, lean_object* v_alts_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_inc(v_indName_866_);
v___x_889_ = l_Lean_mkCtorIdxName(v_indName_866_);
lean_inc(v_tail_867_);
v___x_890_ = l_Lean_mkConst(v___x_889_, v_tail_867_);
lean_inc_ref_n(v_params_868_, 2);
v___x_891_ = l_Array_append___redArg(v_params_868_, v_ism1_869_);
lean_inc_ref(v___x_890_);
v___x_892_ = l_Lean_mkAppN(v___x_890_, v___x_891_);
lean_dec_ref(v___x_891_);
v___x_893_ = l_Array_append___redArg(v_params_868_, v_ism2_870_);
v___x_894_ = l_Lean_mkAppN(v___x_890_, v___x_893_);
lean_dec_ref(v___x_893_);
lean_inc_ref(v___x_894_);
lean_inc_ref(v___x_892_);
v___x_895_ = l_Lean_Meta_mkEq(v___x_892_, v___x_894_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_897_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
lean_inc_ref(v___x_894_);
v___x_897_ = l_Lean_Meta_mkEq(v___x_894_, v___x_892_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___f_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = lean_box(v___x_873_);
v___x_900_ = lean_box(v___x_874_);
v___x_901_ = lean_box(v___x_875_);
v___f_902_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__0___boxed), 26, 20);
lean_closure_set(v___f_902_, 0, v_motive_871_);
lean_closure_set(v___f_902_, 1, v___x_872_);
lean_closure_set(v___f_902_, 2, v_a_898_);
lean_closure_set(v___f_902_, 3, v_ism1_869_);
lean_closure_set(v___f_902_, 4, v___x_899_);
lean_closure_set(v___f_902_, 5, v___x_900_);
lean_closure_set(v___f_902_, 6, v___x_901_);
lean_closure_set(v___f_902_, 7, v___x_876_);
lean_closure_set(v___f_902_, 8, v_tail_867_);
lean_closure_set(v___f_902_, 9, v_params_868_);
lean_closure_set(v___f_902_, 10, v_alts_883_);
lean_closure_set(v___f_902_, 11, v_numParams_877_);
lean_closure_set(v___f_902_, 12, v_ism2_870_);
lean_closure_set(v___f_902_, 13, v_val_878_);
lean_closure_set(v___f_902_, 14, v_indName_866_);
lean_closure_set(v___f_902_, 15, v___x_879_);
lean_closure_set(v___f_902_, 16, v___x_880_);
lean_closure_set(v___f_902_, 17, v___x_894_);
lean_closure_set(v___f_902_, 18, v_name_881_);
lean_closure_set(v___f_902_, 19, v___x_882_);
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_904_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_903_, v_a_896_, v___f_902_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
return v___x_904_;
}
else
{
lean_dec(v_a_896_);
lean_dec_ref(v___x_894_);
lean_dec_ref(v_alts_883_);
lean_dec(v___x_882_);
lean_dec(v_name_881_);
lean_dec(v___x_880_);
lean_dec(v___x_879_);
lean_dec_ref(v_val_878_);
lean_dec(v_numParams_877_);
lean_dec_ref(v___x_876_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v_motive_871_);
lean_dec_ref(v_ism2_870_);
lean_dec_ref(v_ism1_869_);
lean_dec_ref(v_params_868_);
lean_dec(v_tail_867_);
lean_dec(v_indName_866_);
return v___x_897_;
}
}
else
{
lean_dec_ref(v___x_894_);
lean_dec_ref(v___x_892_);
lean_dec_ref(v_alts_883_);
lean_dec(v___x_882_);
lean_dec(v_name_881_);
lean_dec(v___x_880_);
lean_dec(v___x_879_);
lean_dec_ref(v_val_878_);
lean_dec(v_numParams_877_);
lean_dec_ref(v___x_876_);
lean_dec_ref(v___x_872_);
lean_dec_ref(v_motive_871_);
lean_dec_ref(v_ism2_870_);
lean_dec_ref(v_ism1_869_);
lean_dec_ref(v_params_868_);
lean_dec(v_tail_867_);
lean_dec(v_indName_866_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object** _args){
lean_object* v_indName_905_ = _args[0];
lean_object* v_tail_906_ = _args[1];
lean_object* v_params_907_ = _args[2];
lean_object* v_ism1_908_ = _args[3];
lean_object* v_ism2_909_ = _args[4];
lean_object* v_motive_910_ = _args[5];
lean_object* v___x_911_ = _args[6];
lean_object* v___x_912_ = _args[7];
lean_object* v___x_913_ = _args[8];
lean_object* v___x_914_ = _args[9];
lean_object* v___x_915_ = _args[10];
lean_object* v_numParams_916_ = _args[11];
lean_object* v_val_917_ = _args[12];
lean_object* v___x_918_ = _args[13];
lean_object* v___x_919_ = _args[14];
lean_object* v_name_920_ = _args[15];
lean_object* v___x_921_ = _args[16];
lean_object* v_alts_922_ = _args[17];
lean_object* v___y_923_ = _args[18];
lean_object* v___y_924_ = _args[19];
lean_object* v___y_925_ = _args[20];
lean_object* v___y_926_ = _args[21];
lean_object* v___y_927_ = _args[22];
_start:
{
uint8_t v___x_21298__boxed_928_; uint8_t v___x_21299__boxed_929_; uint8_t v___x_21300__boxed_930_; lean_object* v_res_931_; 
v___x_21298__boxed_928_ = lean_unbox(v___x_912_);
v___x_21299__boxed_929_ = lean_unbox(v___x_913_);
v___x_21300__boxed_930_ = lean_unbox(v___x_914_);
v_res_931_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_905_, v_tail_906_, v_params_907_, v_ism1_908_, v_ism2_909_, v_motive_910_, v___x_911_, v___x_21298__boxed_928_, v___x_21299__boxed_929_, v___x_21300__boxed_930_, v___x_915_, v_numParams_916_, v_val_917_, v___x_918_, v___x_919_, v_name_920_, v___x_921_, v_alts_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_932_, lean_object* v_x_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v_snd_932_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_940_, lean_object* v_x_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_940_, v_x_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec_ref(v_x_941_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_948_, size_t v_i_949_, lean_object* v_bs_950_){
_start:
{
uint8_t v___x_951_; 
v___x_951_ = lean_usize_dec_lt(v_i_949_, v_sz_948_);
if (v___x_951_ == 0)
{
return v_bs_950_;
}
else
{
lean_object* v_v_952_; lean_object* v_fst_953_; lean_object* v_snd_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_968_; 
v_v_952_ = lean_array_uget(v_bs_950_, v_i_949_);
v_fst_953_ = lean_ctor_get(v_v_952_, 0);
v_snd_954_ = lean_ctor_get(v_v_952_, 1);
v_isSharedCheck_968_ = !lean_is_exclusive(v_v_952_);
if (v_isSharedCheck_968_ == 0)
{
v___x_956_ = v_v_952_;
v_isShared_957_ = v_isSharedCheck_968_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_snd_954_);
lean_inc(v_fst_953_);
lean_dec(v_v_952_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_968_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; lean_object* v_bs_x27_959_; lean_object* v___f_960_; lean_object* v___x_962_; 
v___x_958_ = lean_unsigned_to_nat(0u);
v_bs_x27_959_ = lean_array_uset(v_bs_950_, v_i_949_, v___x_958_);
v___f_960_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_960_, 0, v_snd_954_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___f_960_);
v___x_962_ = v___x_956_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_fst_953_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___f_960_);
v___x_962_ = v_reuseFailAlloc_967_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
size_t v___x_963_; size_t v___x_964_; lean_object* v___x_965_; 
v___x_963_ = ((size_t)1ULL);
v___x_964_ = lean_usize_add(v_i_949_, v___x_963_);
v___x_965_ = lean_array_uset(v_bs_x27_959_, v_i_949_, v___x_962_);
v_i_949_ = v___x_964_;
v_bs_950_ = v___x_965_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_969_, lean_object* v_i_970_, lean_object* v_bs_971_){
_start:
{
size_t v_sz_boxed_972_; size_t v_i_boxed_973_; lean_object* v_res_974_; 
v_sz_boxed_972_ = lean_unbox_usize(v_sz_969_);
lean_dec(v_sz_969_);
v_i_boxed_973_ = lean_unbox_usize(v_i_970_);
lean_dec(v_i_970_);
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_972_, v_i_boxed_973_, v_bs_971_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object* v___x_975_, lean_object* v_a_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v___x_20182__overap_983_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_instInhabitedExpr;
v___x_20182__overap_983_ = l_instInhabitedOfMonad___redArg(v___x_975_, v___x_982_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
v___x_984_ = lean_apply_5(v___x_20182__overap_983_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, lean_box(0));
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object* v___x_985_, lean_object* v_a_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_985_, v_a_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
lean_dec_ref(v_a_986_);
return v_res_992_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_instMonadEIO(lean_box(0));
return v___x_993_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0);
v___x_995_ = l_StateRefT_x27_instMonad___redArg(v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object* v_acc_1000_, lean_object* v_declInfos_1001_, lean_object* v_k_1002_, lean_object* v_kind_1003_, lean_object* v_x_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
uint8_t v_kind_boxed_1010_; lean_object* v_res_1011_; 
v_kind_boxed_1010_ = lean_unbox(v_kind_1003_);
v_res_1011_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_1000_, v_declInfos_1001_, v_k_1002_, v_kind_boxed_1010_, v_x_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_declInfos_1012_, lean_object* v_k_1013_, uint8_t v_kind_1014_, lean_object* v_acc_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v_toApplicative_1022_; lean_object* v_toFunctor_1023_; lean_object* v_toSeq_1024_; lean_object* v_toSeqLeft_1025_; lean_object* v_toSeqRight_1026_; lean_object* v___f_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___f_1032_; lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v_toApplicative_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1087_; 
v___x_1021_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_1022_ = lean_ctor_get(v___x_1021_, 0);
v_toFunctor_1023_ = lean_ctor_get(v_toApplicative_1022_, 0);
v_toSeq_1024_ = lean_ctor_get(v_toApplicative_1022_, 2);
v_toSeqLeft_1025_ = lean_ctor_get(v_toApplicative_1022_, 3);
v_toSeqRight_1026_ = lean_ctor_get(v_toApplicative_1022_, 4);
v___f_1027_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_1028_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_1023_, 2);
v___f_1029_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1029_, 0, v_toFunctor_1023_);
v___f_1030_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1030_, 0, v_toFunctor_1023_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___f_1029_);
lean_ctor_set(v___x_1031_, 1, v___f_1030_);
lean_inc(v_toSeqRight_1026_);
v___f_1032_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1032_, 0, v_toSeqRight_1026_);
lean_inc(v_toSeqLeft_1025_);
v___f_1033_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1033_, 0, v_toSeqLeft_1025_);
lean_inc(v_toSeq_1024_);
v___f_1034_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1034_, 0, v_toSeq_1024_);
v___x_1035_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1031_);
lean_ctor_set(v___x_1035_, 1, v___f_1027_);
lean_ctor_set(v___x_1035_, 2, v___f_1034_);
lean_ctor_set(v___x_1035_, 3, v___f_1033_);
lean_ctor_set(v___x_1035_, 4, v___f_1032_);
v___x_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1035_);
lean_ctor_set(v___x_1036_, 1, v___f_1028_);
v___x_1037_ = l_StateRefT_x27_instMonad___redArg(v___x_1036_);
v_toApplicative_1038_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v___x_1037_, 1);
lean_dec(v_unused_1088_);
v___x_1040_ = v___x_1037_;
v_isShared_1041_ = v_isSharedCheck_1087_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_toApplicative_1038_);
lean_dec(v___x_1037_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1087_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_toFunctor_1042_; lean_object* v_toSeq_1043_; lean_object* v_toSeqLeft_1044_; lean_object* v_toSeqRight_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1085_; 
v_toFunctor_1042_ = lean_ctor_get(v_toApplicative_1038_, 0);
v_toSeq_1043_ = lean_ctor_get(v_toApplicative_1038_, 2);
v_toSeqLeft_1044_ = lean_ctor_get(v_toApplicative_1038_, 3);
v_toSeqRight_1045_ = lean_ctor_get(v_toApplicative_1038_, 4);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_toApplicative_1038_);
if (v_isSharedCheck_1085_ == 0)
{
lean_object* v_unused_1086_; 
v_unused_1086_ = lean_ctor_get(v_toApplicative_1038_, 1);
lean_dec(v_unused_1086_);
v___x_1047_ = v_toApplicative_1038_;
v_isShared_1048_ = v_isSharedCheck_1085_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_toSeqRight_1045_);
lean_inc(v_toSeqLeft_1044_);
lean_inc(v_toSeq_1043_);
lean_inc(v_toFunctor_1042_);
lean_dec(v_toApplicative_1038_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1085_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___f_1049_; lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; lean_object* v___f_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___x_1058_; 
v___f_1049_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_1050_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_1042_);
v___f_1051_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1051_, 0, v_toFunctor_1042_);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1052_, 0, v_toFunctor_1042_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___f_1051_);
lean_ctor_set(v___x_1053_, 1, v___f_1052_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toSeqRight_1045_);
v___f_1055_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1055_, 0, v_toSeqLeft_1044_);
v___f_1056_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1056_, 0, v_toSeq_1043_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 4, v___f_1054_);
lean_ctor_set(v___x_1047_, 3, v___f_1055_);
lean_ctor_set(v___x_1047_, 2, v___f_1056_);
lean_ctor_set(v___x_1047_, 1, v___f_1049_);
lean_ctor_set(v___x_1047_, 0, v___x_1053_);
v___x_1058_ = v___x_1047_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___f_1049_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v___f_1056_);
lean_ctor_set(v_reuseFailAlloc_1084_, 3, v___f_1055_);
lean_ctor_set(v_reuseFailAlloc_1084_, 4, v___f_1054_);
v___x_1058_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1060_; 
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___f_1050_);
lean_ctor_set(v___x_1040_, 0, v___x_1058_);
v___x_1060_ = v___x_1040_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___f_1050_);
v___x_1060_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1061_ = lean_array_get_size(v_acc_1015_);
v___x_1062_ = lean_array_get_size(v_declInfos_1012_);
v___x_1063_ = lean_nat_dec_lt(v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; 
lean_dec_ref(v___x_1060_);
lean_dec_ref(v_declInfos_1012_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
v___x_1064_ = lean_apply_6(v_k_1013_, v_acc_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, lean_box(0));
return v___x_1064_;
}
else
{
lean_object* v___f_1065_; lean_object* v___x_1066_; uint8_t v___x_1067_; lean_object* v___f_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v_snd_1073_; lean_object* v_fst_1074_; lean_object* v_fst_1075_; lean_object* v_snd_1076_; lean_object* v___x_1077_; 
v___f_1065_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1065_, 0, v___x_1060_);
v___x_1066_ = lean_box(0);
v___x_1067_ = 0;
v___f_1068_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1068_, 0, v___f_1065_);
v___x_1069_ = lean_box(v___x_1067_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v___f_1068_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1066_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_array_get(v___x_1071_, v_declInfos_1012_, v___x_1061_);
lean_dec_ref_known(v___x_1071_, 2);
v_snd_1073_ = lean_ctor_get(v___x_1072_, 1);
lean_inc(v_snd_1073_);
v_fst_1074_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_fst_1074_);
lean_dec(v___x_1072_);
v_fst_1075_ = lean_ctor_get(v_snd_1073_, 0);
lean_inc(v_fst_1075_);
v_snd_1076_ = lean_ctor_get(v_snd_1073_, 1);
lean_inc(v_snd_1076_);
lean_dec(v_snd_1073_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc_ref(v_acc_1015_);
v___x_1077_ = lean_apply_6(v_snd_1076_, v_acc_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, lean_box(0));
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; lean_object* v___f_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = lean_box(v_kind_1014_);
v___f_1080_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1080_, 0, v_acc_1015_);
lean_closure_set(v___f_1080_, 1, v_declInfos_1012_);
lean_closure_set(v___f_1080_, 2, v_k_1013_);
lean_closure_set(v___f_1080_, 3, v___x_1079_);
v___x_1081_ = lean_unbox(v_fst_1075_);
lean_dec(v_fst_1075_);
v___x_1082_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1074_, v___x_1081_, v_a_1078_, v___f_1080_, v_kind_1014_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1082_;
}
else
{
lean_dec(v_fst_1075_);
lean_dec(v_fst_1074_);
lean_dec_ref(v_acc_1015_);
lean_dec_ref(v_k_1013_);
lean_dec_ref(v_declInfos_1012_);
return v___x_1077_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(lean_object* v_acc_1089_, lean_object* v_declInfos_1090_, lean_object* v_k_1091_, uint8_t v_kind_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = lean_array_push(v_acc_1089_, v_x_1093_);
v___x_1100_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1090_, v_k_1091_, v_kind_1092_, v___x_1099_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object* v_declInfos_1101_, lean_object* v_k_1102_, lean_object* v_kind_1103_, lean_object* v_acc_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
uint8_t v_kind_boxed_1110_; lean_object* v_res_1111_; 
v_kind_boxed_1110_ = lean_unbox(v_kind_1103_);
v_res_1111_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1101_, v_k_1102_, v_kind_boxed_1110_, v_acc_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object* v_declInfos_1114_, lean_object* v_k_1115_, uint8_t v_kind_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_1123_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1114_, v_k_1115_, v_kind_1116_, v___x_1122_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object* v_declInfos_1124_, lean_object* v_k_1125_, lean_object* v_kind_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v_kind_boxed_1132_; lean_object* v_res_1133_; 
v_kind_boxed_1132_ = lean_unbox(v_kind_1126_);
v_res_1133_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_declInfos_1124_, v_k_1125_, v_kind_boxed_1132_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
lean_dec(v___y_1128_);
lean_dec_ref(v___y_1127_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t v_sz_1134_, size_t v_i_1135_, lean_object* v_bs_1136_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_usize_dec_lt(v_i_1135_, v_sz_1134_);
if (v___x_1137_ == 0)
{
return v_bs_1136_;
}
else
{
lean_object* v_v_1138_; lean_object* v_fst_1139_; lean_object* v_snd_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1156_; 
v_v_1138_ = lean_array_uget(v_bs_1136_, v_i_1135_);
v_fst_1139_ = lean_ctor_get(v_v_1138_, 0);
v_snd_1140_ = lean_ctor_get(v_v_1138_, 1);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_v_1138_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1142_ = v_v_1138_;
v_isShared_1143_ = v_isSharedCheck_1156_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_snd_1140_);
lean_inc(v_fst_1139_);
lean_dec(v_v_1138_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1156_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v_bs_x27_1145_; uint8_t v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1144_ = lean_unsigned_to_nat(0u);
v_bs_x27_1145_ = lean_array_uset(v_bs_1136_, v_i_1135_, v___x_1144_);
v___x_1146_ = 0;
v___x_1147_ = lean_box(v___x_1146_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1147_);
v___x_1149_ = v___x_1142_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_snd_1140_);
v___x_1149_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; size_t v___x_1151_; size_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1150_, 0, v_fst_1139_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = ((size_t)1ULL);
v___x_1152_ = lean_usize_add(v_i_1135_, v___x_1151_);
v___x_1153_ = lean_array_uset(v_bs_x27_1145_, v_i_1135_, v___x_1150_);
v_i_1135_ = v___x_1152_;
v_bs_1136_ = v___x_1153_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_sz_1157_, lean_object* v_i_1158_, lean_object* v_bs_1159_){
_start:
{
size_t v_sz_boxed_1160_; size_t v_i_boxed_1161_; lean_object* v_res_1162_; 
v_sz_boxed_1160_ = lean_unbox_usize(v_sz_1157_);
lean_dec(v_sz_1157_);
v_i_boxed_1161_ = lean_unbox_usize(v_i_1158_);
lean_dec(v_i_1158_);
v_res_1162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_1160_, v_i_boxed_1161_, v_bs_1159_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_declInfos_1163_, lean_object* v_k_1164_, uint8_t v_kind_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_){
_start:
{
size_t v_sz_1171_; size_t v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_sz_1171_ = lean_array_size(v_declInfos_1163_);
v___x_1172_ = ((size_t)0ULL);
v___x_1173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1171_, v___x_1172_, v_declInfos_1163_);
v___x_1174_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v___x_1173_, v_k_1164_, v_kind_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_declInfos_1175_, lean_object* v_k_1176_, lean_object* v_kind_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_kind_boxed_1183_; lean_object* v_res_1184_; 
v_kind_boxed_1183_ = lean_unbox(v_kind_1177_);
v_res_1184_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1175_, v_k_1176_, v_kind_boxed_1183_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_declInfos_1185_, lean_object* v_k_1186_, uint8_t v_kind_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
size_t v_sz_1193_; size_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v_sz_1193_ = lean_array_size(v_declInfos_1185_);
v___x_1194_ = ((size_t)0ULL);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1193_, v___x_1194_, v_declInfos_1185_);
v___x_1196_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_1195_, v_k_1186_, v_kind_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_declInfos_1197_, lean_object* v_k_1198_, lean_object* v_kind_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_){
_start:
{
uint8_t v_kind_boxed_1205_; lean_object* v_res_1206_; 
v_kind_boxed_1205_ = lean_unbox(v_kind_1199_);
v_res_1206_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1197_, v_k_1198_, v_kind_boxed_1205_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_1208_, lean_object* v_dummy_1209_, lean_object* v___x_1210_, lean_object* v___x_1211_, lean_object* v___x_1212_, lean_object* v_motive_1213_, lean_object* v_zs1_1214_, uint8_t v___x_1215_, uint8_t v___x_1216_, uint8_t v___x_1217_, lean_object* v_v_1218_, lean_object* v___x_1219_, lean_object* v_zs2_1220_, lean_object* v_ctorRet2_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
v___x_1227_ = lean_whnf(v_ctorRet2_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1229_; lean_object* v_nargs_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc(v_a_1228_);
lean_dec_ref_known(v___x_1227_, 1);
v___x_1229_ = l_Lean_mkAppN(v___x_1208_, v_zs2_1220_);
v_nargs_1230_ = l_Lean_Expr_getAppNumArgs(v_a_1228_);
lean_inc(v_nargs_1230_);
v___x_1231_ = lean_mk_array(v_nargs_1230_, v_dummy_1209_);
v___x_1232_ = lean_nat_sub(v_nargs_1230_, v___x_1210_);
lean_dec(v_nargs_1230_);
v___x_1233_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1228_, v___x_1231_, v___x_1232_);
v___x_1234_ = lean_array_get_size(v___x_1233_);
v___x_1235_ = l_Array_toSubarray___redArg(v___x_1233_, v___x_1211_, v___x_1234_);
v___x_1236_ = l_Subarray_copy___redArg(v___x_1235_);
v___x_1237_ = lean_array_push(v___x_1236_, v___x_1229_);
v___x_1238_ = l_Array_append___redArg(v___x_1212_, v___x_1237_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = l_Lean_mkAppN(v_motive_1213_, v___x_1238_);
lean_dec_ref(v___x_1238_);
v___x_1240_ = l_Array_append___redArg(v_zs1_1214_, v_zs2_1220_);
v___x_1241_ = l_Lean_Meta_mkForallFVars(v___x_1240_, v___x_1239_, v___x_1215_, v___x_1216_, v___x_1216_, v___x_1217_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
lean_dec_ref(v___x_1240_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1261_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1261_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1261_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___y_1247_; 
if (lean_obj_tag(v_v_1218_) == 1)
{
lean_object* v_str_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_str_1252_ = lean_ctor_get(v_v_1218_, 1);
lean_inc_ref(v_str_1252_);
lean_dec_ref_known(v_v_1218_, 2);
v___x_1253_ = lean_box(0);
v___x_1254_ = l_Lean_Name_str___override(v___x_1253_, v_str_1252_);
v___y_1247_ = v___x_1254_;
goto v___jp_1246_;
}
else
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_dec(v_v_1218_);
v___x_1255_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_1256_ = lean_nat_add(v___x_1219_, v___x_1210_);
v___x_1257_ = l_Nat_reprFast(v___x_1256_);
v___x_1258_ = lean_string_append(v___x_1255_, v___x_1257_);
lean_dec_ref(v___x_1257_);
v___x_1259_ = lean_box(0);
v___x_1260_ = l_Lean_Name_str___override(v___x_1259_, v___x_1258_);
v___y_1247_ = v___x_1260_;
goto v___jp_1246_;
}
v___jp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___y_1247_);
lean_ctor_set(v___x_1248_, 1, v_a_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1248_);
v___x_1250_ = v___x_1244_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v_v_1218_);
v_a_1262_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1241_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1241_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec(v_v_1218_);
lean_dec_ref(v_zs1_1214_);
lean_dec_ref(v_motive_1213_);
lean_dec_ref(v___x_1212_);
lean_dec(v___x_1211_);
lean_dec_ref(v_dummy_1209_);
lean_dec_ref(v___x_1208_);
v_a_1270_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1227_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1227_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1278_ = _args[0];
lean_object* v_dummy_1279_ = _args[1];
lean_object* v___x_1280_ = _args[2];
lean_object* v___x_1281_ = _args[3];
lean_object* v___x_1282_ = _args[4];
lean_object* v_motive_1283_ = _args[5];
lean_object* v_zs1_1284_ = _args[6];
lean_object* v___x_1285_ = _args[7];
lean_object* v___x_1286_ = _args[8];
lean_object* v___x_1287_ = _args[9];
lean_object* v_v_1288_ = _args[10];
lean_object* v___x_1289_ = _args[11];
lean_object* v_zs2_1290_ = _args[12];
lean_object* v_ctorRet2_1291_ = _args[13];
lean_object* v___y_1292_ = _args[14];
lean_object* v___y_1293_ = _args[15];
lean_object* v___y_1294_ = _args[16];
lean_object* v___y_1295_ = _args[17];
lean_object* v___y_1296_ = _args[18];
_start:
{
uint8_t v___x_21734__boxed_1297_; uint8_t v___x_21735__boxed_1298_; uint8_t v___x_21736__boxed_1299_; lean_object* v_res_1300_; 
v___x_21734__boxed_1297_ = lean_unbox(v___x_1285_);
v___x_21735__boxed_1298_ = lean_unbox(v___x_1286_);
v___x_21736__boxed_1299_ = lean_unbox(v___x_1287_);
v_res_1300_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1278_, v_dummy_1279_, v___x_1280_, v___x_1281_, v___x_1282_, v_motive_1283_, v_zs1_1284_, v___x_21734__boxed_1297_, v___x_21735__boxed_1298_, v___x_21736__boxed_1299_, v_v_1288_, v___x_1289_, v_zs2_1290_, v_ctorRet2_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
lean_dec_ref(v_zs2_1290_);
lean_dec(v___x_1289_);
lean_dec(v___x_1280_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1301_, lean_object* v___x_1302_, lean_object* v___x_1303_, lean_object* v_motive_1304_, uint8_t v___x_1305_, uint8_t v___x_1306_, uint8_t v___x_1307_, lean_object* v_v_1308_, lean_object* v___x_1309_, lean_object* v_a_1310_, lean_object* v_zs1_1311_, lean_object* v_ctorRet1_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; 
lean_inc(v___y_1316_);
lean_inc_ref(v___y_1315_);
lean_inc(v___y_1314_);
lean_inc_ref(v___y_1313_);
v___x_1318_ = lean_whnf(v_ctorRet1_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; lean_object* v_dummy_1321_; lean_object* v_nargs_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___f_1333_; lean_object* v___x_1334_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
lean_inc_ref(v___x_1301_);
v___x_1320_ = l_Lean_mkAppN(v___x_1301_, v_zs1_1311_);
v_dummy_1321_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1322_ = l_Lean_Expr_getAppNumArgs(v_a_1319_);
lean_inc(v_nargs_1322_);
v___x_1323_ = lean_mk_array(v_nargs_1322_, v_dummy_1321_);
v___x_1324_ = lean_nat_sub(v_nargs_1322_, v___x_1302_);
lean_dec(v_nargs_1322_);
v___x_1325_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1319_, v___x_1323_, v___x_1324_);
v___x_1326_ = lean_array_get_size(v___x_1325_);
lean_inc(v___x_1303_);
v___x_1327_ = l_Array_toSubarray___redArg(v___x_1325_, v___x_1303_, v___x_1326_);
v___x_1328_ = l_Subarray_copy___redArg(v___x_1327_);
v___x_1329_ = lean_array_push(v___x_1328_, v___x_1320_);
v___x_1330_ = lean_box(v___x_1305_);
v___x_1331_ = lean_box(v___x_1306_);
v___x_1332_ = lean_box(v___x_1307_);
v___f_1333_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1333_, 0, v___x_1301_);
lean_closure_set(v___f_1333_, 1, v_dummy_1321_);
lean_closure_set(v___f_1333_, 2, v___x_1302_);
lean_closure_set(v___f_1333_, 3, v___x_1303_);
lean_closure_set(v___f_1333_, 4, v___x_1329_);
lean_closure_set(v___f_1333_, 5, v_motive_1304_);
lean_closure_set(v___f_1333_, 6, v_zs1_1311_);
lean_closure_set(v___f_1333_, 7, v___x_1330_);
lean_closure_set(v___f_1333_, 8, v___x_1331_);
lean_closure_set(v___f_1333_, 9, v___x_1332_);
lean_closure_set(v___f_1333_, 10, v_v_1308_);
lean_closure_set(v___f_1333_, 11, v___x_1309_);
v___x_1334_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1310_, v___f_1333_, v___x_1305_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1334_;
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_zs1_1311_);
lean_dec_ref(v_a_1310_);
lean_dec(v___x_1309_);
lean_dec(v_v_1308_);
lean_dec_ref(v_motive_1304_);
lean_dec(v___x_1303_);
lean_dec(v___x_1302_);
lean_dec_ref(v___x_1301_);
v_a_1335_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1318_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1318_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1343_ = _args[0];
lean_object* v___x_1344_ = _args[1];
lean_object* v___x_1345_ = _args[2];
lean_object* v_motive_1346_ = _args[3];
lean_object* v___x_1347_ = _args[4];
lean_object* v___x_1348_ = _args[5];
lean_object* v___x_1349_ = _args[6];
lean_object* v_v_1350_ = _args[7];
lean_object* v___x_1351_ = _args[8];
lean_object* v_a_1352_ = _args[9];
lean_object* v_zs1_1353_ = _args[10];
lean_object* v_ctorRet1_1354_ = _args[11];
lean_object* v___y_1355_ = _args[12];
lean_object* v___y_1356_ = _args[13];
lean_object* v___y_1357_ = _args[14];
lean_object* v___y_1358_ = _args[15];
lean_object* v___y_1359_ = _args[16];
_start:
{
uint8_t v___x_21875__boxed_1360_; uint8_t v___x_21876__boxed_1361_; uint8_t v___x_21877__boxed_1362_; lean_object* v_res_1363_; 
v___x_21875__boxed_1360_ = lean_unbox(v___x_1347_);
v___x_21876__boxed_1361_ = lean_unbox(v___x_1348_);
v___x_21877__boxed_1362_ = lean_unbox(v___x_1349_);
v_res_1363_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1343_, v___x_1344_, v___x_1345_, v_motive_1346_, v___x_21875__boxed_1360_, v___x_21876__boxed_1361_, v___x_21877__boxed_1362_, v_v_1350_, v___x_1351_, v_a_1352_, v_zs1_1353_, v_ctorRet1_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1364_, lean_object* v_params_1365_, lean_object* v___x_1366_, lean_object* v_motive_1367_, size_t v_sz_1368_, size_t v_i_1369_, lean_object* v_bs_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v___x_1376_; 
v___x_1376_ = lean_usize_dec_lt(v_i_1369_, v_sz_1368_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; 
lean_dec_ref(v_motive_1367_);
lean_dec(v___x_1366_);
lean_dec(v_tail_1364_);
v___x_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1377_, 0, v_bs_1370_);
return v___x_1377_;
}
else
{
lean_object* v_v_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v_v_1378_ = lean_array_uget(v_bs_1370_, v_i_1369_);
lean_inc(v_tail_1364_);
lean_inc(v_v_1378_);
v___x_1379_ = l_Lean_mkConst(v_v_1378_, v_tail_1364_);
v___x_1380_ = l_Lean_mkAppN(v___x_1379_, v_params_1365_);
lean_inc(v___y_1374_);
lean_inc_ref(v___y_1373_);
lean_inc(v___y_1372_);
lean_inc_ref(v___y_1371_);
lean_inc_ref(v___x_1380_);
v___x_1381_ = lean_infer_type(v___x_1380_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; lean_object* v___x_1383_; lean_object* v_bs_x27_1384_; uint8_t v___x_1385_; uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___f_1392_; lean_object* v___x_1393_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc_n(v_a_1382_, 2);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1383_ = lean_unsigned_to_nat(0u);
v_bs_x27_1384_ = lean_array_uset(v_bs_1370_, v_i_1369_, v___x_1383_);
v___x_1385_ = 0;
v___x_1386_ = 1;
v___x_1387_ = lean_unsigned_to_nat(1u);
v___x_1388_ = lean_usize_to_nat(v_i_1369_);
v___x_1389_ = lean_box(v___x_1385_);
v___x_1390_ = lean_box(v___x_1376_);
v___x_1391_ = lean_box(v___x_1386_);
lean_inc_ref(v_motive_1367_);
lean_inc(v___x_1366_);
v___f_1392_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1392_, 0, v___x_1380_);
lean_closure_set(v___f_1392_, 1, v___x_1387_);
lean_closure_set(v___f_1392_, 2, v___x_1366_);
lean_closure_set(v___f_1392_, 3, v_motive_1367_);
lean_closure_set(v___f_1392_, 4, v___x_1389_);
lean_closure_set(v___f_1392_, 5, v___x_1390_);
lean_closure_set(v___f_1392_, 6, v___x_1391_);
lean_closure_set(v___f_1392_, 7, v_v_1378_);
lean_closure_set(v___f_1392_, 8, v___x_1388_);
lean_closure_set(v___f_1392_, 9, v_a_1382_);
v___x_1393_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1382_, v___f_1392_, v___x_1385_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
if (lean_obj_tag(v___x_1393_) == 0)
{
lean_object* v_a_1394_; size_t v___x_1395_; size_t v___x_1396_; lean_object* v___x_1397_; 
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref_known(v___x_1393_, 1);
v___x_1395_ = ((size_t)1ULL);
v___x_1396_ = lean_usize_add(v_i_1369_, v___x_1395_);
v___x_1397_ = lean_array_uset(v_bs_x27_1384_, v_i_1369_, v_a_1394_);
v_i_1369_ = v___x_1396_;
v_bs_1370_ = v___x_1397_;
goto _start;
}
else
{
lean_object* v_a_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1406_; 
lean_dec_ref(v_bs_x27_1384_);
lean_dec_ref(v_motive_1367_);
lean_dec(v___x_1366_);
lean_dec(v_tail_1364_);
v_a_1399_ = lean_ctor_get(v___x_1393_, 0);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1393_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1401_ = v___x_1393_;
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_a_1399_);
lean_dec(v___x_1393_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1406_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_a_1399_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec_ref(v___x_1380_);
lean_dec(v_v_1378_);
lean_dec_ref(v_bs_1370_);
lean_dec_ref(v_motive_1367_);
lean_dec(v___x_1366_);
lean_dec(v_tail_1364_);
v_a_1407_ = lean_ctor_get(v___x_1381_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1381_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1381_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1381_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1415_, lean_object* v_params_1416_, lean_object* v___x_1417_, lean_object* v_motive_1418_, lean_object* v_sz_1419_, lean_object* v_i_1420_, lean_object* v_bs_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
size_t v_sz_boxed_1427_; size_t v_i_boxed_1428_; lean_object* v_res_1429_; 
v_sz_boxed_1427_ = lean_unbox_usize(v_sz_1419_);
lean_dec(v_sz_1419_);
v_i_boxed_1428_ = lean_unbox_usize(v_i_1420_);
lean_dec(v_i_1420_);
v_res_1429_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1415_, v_params_1416_, v___x_1417_, v_motive_1418_, v_sz_boxed_1427_, v_i_boxed_1428_, v_bs_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec_ref(v_params_1416_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1430_, lean_object* v_tail_1431_, lean_object* v_params_1432_, lean_object* v_numParams_1433_, lean_object* v_indName_1434_, lean_object* v_ism1_1435_, lean_object* v_ism2_1436_, lean_object* v___x_1437_, uint8_t v___x_1438_, uint8_t v___x_1439_, uint8_t v___x_1440_, lean_object* v_val_1441_, lean_object* v___x_1442_, lean_object* v___x_1443_, lean_object* v_name_1444_, lean_object* v___x_1445_, lean_object* v_motive_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; size_t v_sz_1453_; size_t v___x_1454_; lean_object* v___x_1455_; 
v___x_1452_ = lean_array_mk(v_ctors_1430_);
v_sz_1453_ = lean_array_size(v___x_1452_);
v___x_1454_ = ((size_t)0ULL);
lean_inc_ref(v___x_1452_);
lean_inc_ref(v_motive_1446_);
lean_inc(v_numParams_1433_);
lean_inc(v_tail_1431_);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1431_, v_params_1432_, v_numParams_1433_, v_motive_1446_, v_sz_1453_, v___x_1454_, v___x_1452_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_object* v_a_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___f_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; 
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref_known(v___x_1455_, 1);
v___x_1457_ = lean_box(v___x_1438_);
v___x_1458_ = lean_box(v___x_1439_);
v___x_1459_ = lean_box(v___x_1440_);
v___f_1460_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1460_, 0, v_indName_1434_);
lean_closure_set(v___f_1460_, 1, v_tail_1431_);
lean_closure_set(v___f_1460_, 2, v_params_1432_);
lean_closure_set(v___f_1460_, 3, v_ism1_1435_);
lean_closure_set(v___f_1460_, 4, v_ism2_1436_);
lean_closure_set(v___f_1460_, 5, v_motive_1446_);
lean_closure_set(v___f_1460_, 6, v___x_1437_);
lean_closure_set(v___f_1460_, 7, v___x_1457_);
lean_closure_set(v___f_1460_, 8, v___x_1458_);
lean_closure_set(v___f_1460_, 9, v___x_1459_);
lean_closure_set(v___f_1460_, 10, v___x_1452_);
lean_closure_set(v___f_1460_, 11, v_numParams_1433_);
lean_closure_set(v___f_1460_, 12, v_val_1441_);
lean_closure_set(v___f_1460_, 13, v___x_1442_);
lean_closure_set(v___f_1460_, 14, v___x_1443_);
lean_closure_set(v___f_1460_, 15, v_name_1444_);
lean_closure_set(v___f_1460_, 16, v___x_1445_);
v___x_1461_ = 0;
v___x_1462_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_a_1456_, v___f_1460_, v___x_1461_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
return v___x_1462_;
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v___x_1452_);
lean_dec_ref(v_motive_1446_);
lean_dec(v___x_1445_);
lean_dec(v_name_1444_);
lean_dec(v___x_1443_);
lean_dec(v___x_1442_);
lean_dec_ref(v_val_1441_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v_ism2_1436_);
lean_dec_ref(v_ism1_1435_);
lean_dec(v_indName_1434_);
lean_dec(v_numParams_1433_);
lean_dec_ref(v_params_1432_);
lean_dec(v_tail_1431_);
v_a_1463_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1455_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1455_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1471_ = _args[0];
lean_object* v_tail_1472_ = _args[1];
lean_object* v_params_1473_ = _args[2];
lean_object* v_numParams_1474_ = _args[3];
lean_object* v_indName_1475_ = _args[4];
lean_object* v_ism1_1476_ = _args[5];
lean_object* v_ism2_1477_ = _args[6];
lean_object* v___x_1478_ = _args[7];
lean_object* v___x_1479_ = _args[8];
lean_object* v___x_1480_ = _args[9];
lean_object* v___x_1481_ = _args[10];
lean_object* v_val_1482_ = _args[11];
lean_object* v___x_1483_ = _args[12];
lean_object* v___x_1484_ = _args[13];
lean_object* v_name_1485_ = _args[14];
lean_object* v___x_1486_ = _args[15];
lean_object* v_motive_1487_ = _args[16];
lean_object* v___y_1488_ = _args[17];
lean_object* v___y_1489_ = _args[18];
lean_object* v___y_1490_ = _args[19];
lean_object* v___y_1491_ = _args[20];
lean_object* v___y_1492_ = _args[21];
_start:
{
uint8_t v___x_22055__boxed_1493_; uint8_t v___x_22056__boxed_1494_; uint8_t v___x_22057__boxed_1495_; lean_object* v_res_1496_; 
v___x_22055__boxed_1493_ = lean_unbox(v___x_1479_);
v___x_22056__boxed_1494_ = lean_unbox(v___x_1480_);
v___x_22057__boxed_1495_ = lean_unbox(v___x_1481_);
v_res_1496_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1471_, v_tail_1472_, v_params_1473_, v_numParams_1474_, v_indName_1475_, v_ism1_1476_, v_ism2_1477_, v___x_1478_, v___x_22055__boxed_1493_, v___x_22056__boxed_1494_, v___x_22057__boxed_1495_, v_val_1482_, v___x_1483_, v___x_1484_, v_name_1485_, v___x_1486_, v_motive_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1500_, lean_object* v_head_1501_, lean_object* v_ctors_1502_, lean_object* v_tail_1503_, lean_object* v_params_1504_, lean_object* v_numParams_1505_, lean_object* v_indName_1506_, lean_object* v_val_1507_, lean_object* v___x_1508_, lean_object* v___x_1509_, lean_object* v_name_1510_, lean_object* v___x_1511_, lean_object* v_ism2_1512_, lean_object* v_x_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; uint8_t v___x_1522_; uint8_t v___x_1523_; lean_object* v___x_1524_; 
lean_inc_ref(v_ism1_1500_);
v___x_1519_ = l_Array_append___redArg(v_ism1_1500_, v_ism2_1512_);
v___x_1520_ = l_Lean_mkSort(v_head_1501_);
v___x_1521_ = 0;
v___x_1522_ = 1;
v___x_1523_ = 1;
v___x_1524_ = l_Lean_Meta_mkForallFVars(v___x_1519_, v___x_1520_, v___x_1521_, v___x_1522_, v___x_1522_, v___x_1523_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; lean_object* v___x_1532_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = lean_box(v___x_1521_);
v___x_1527_ = lean_box(v___x_1522_);
v___x_1528_ = lean_box(v___x_1523_);
v___f_1529_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 22, 16);
lean_closure_set(v___f_1529_, 0, v_ctors_1502_);
lean_closure_set(v___f_1529_, 1, v_tail_1503_);
lean_closure_set(v___f_1529_, 2, v_params_1504_);
lean_closure_set(v___f_1529_, 3, v_numParams_1505_);
lean_closure_set(v___f_1529_, 4, v_indName_1506_);
lean_closure_set(v___f_1529_, 5, v_ism1_1500_);
lean_closure_set(v___f_1529_, 6, v_ism2_1512_);
lean_closure_set(v___f_1529_, 7, v___x_1519_);
lean_closure_set(v___f_1529_, 8, v___x_1526_);
lean_closure_set(v___f_1529_, 9, v___x_1527_);
lean_closure_set(v___f_1529_, 10, v___x_1528_);
lean_closure_set(v___f_1529_, 11, v_val_1507_);
lean_closure_set(v___f_1529_, 12, v___x_1508_);
lean_closure_set(v___f_1529_, 13, v___x_1509_);
lean_closure_set(v___f_1529_, 14, v_name_1510_);
lean_closure_set(v___f_1529_, 15, v___x_1511_);
v___x_1530_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1531_ = 0;
v___x_1532_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1530_, v___x_1523_, v_a_1525_, v___f_1529_, v___x_1531_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1532_;
}
else
{
lean_dec_ref(v___x_1519_);
lean_dec_ref(v_ism2_1512_);
lean_dec(v___x_1511_);
lean_dec(v_name_1510_);
lean_dec(v___x_1509_);
lean_dec(v___x_1508_);
lean_dec_ref(v_val_1507_);
lean_dec(v_indName_1506_);
lean_dec(v_numParams_1505_);
lean_dec_ref(v_params_1504_);
lean_dec(v_tail_1503_);
lean_dec(v_ctors_1502_);
lean_dec_ref(v_ism1_1500_);
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1533_ = _args[0];
lean_object* v_head_1534_ = _args[1];
lean_object* v_ctors_1535_ = _args[2];
lean_object* v_tail_1536_ = _args[3];
lean_object* v_params_1537_ = _args[4];
lean_object* v_numParams_1538_ = _args[5];
lean_object* v_indName_1539_ = _args[6];
lean_object* v_val_1540_ = _args[7];
lean_object* v___x_1541_ = _args[8];
lean_object* v___x_1542_ = _args[9];
lean_object* v_name_1543_ = _args[10];
lean_object* v___x_1544_ = _args[11];
lean_object* v_ism2_1545_ = _args[12];
lean_object* v_x_1546_ = _args[13];
lean_object* v___y_1547_ = _args[14];
lean_object* v___y_1548_ = _args[15];
lean_object* v___y_1549_ = _args[16];
lean_object* v___y_1550_ = _args[17];
lean_object* v___y_1551_ = _args[18];
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1533_, v_head_1534_, v_ctors_1535_, v_tail_1536_, v_params_1537_, v_numParams_1538_, v_indName_1539_, v_val_1540_, v___x_1541_, v___x_1542_, v_name_1543_, v___x_1544_, v_ism2_1545_, v_x_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec_ref(v_x_1546_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1553_, lean_object* v_ctors_1554_, lean_object* v_tail_1555_, lean_object* v_params_1556_, lean_object* v_numParams_1557_, lean_object* v_indName_1558_, lean_object* v_val_1559_, lean_object* v___x_1560_, lean_object* v___x_1561_, lean_object* v_name_1562_, lean_object* v___x_1563_, lean_object* v_t_1564_, lean_object* v___x_1565_, lean_object* v_ism1_1566_, lean_object* v_x_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___f_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; 
v___f_1573_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 19, 12);
lean_closure_set(v___f_1573_, 0, v_ism1_1566_);
lean_closure_set(v___f_1573_, 1, v_head_1553_);
lean_closure_set(v___f_1573_, 2, v_ctors_1554_);
lean_closure_set(v___f_1573_, 3, v_tail_1555_);
lean_closure_set(v___f_1573_, 4, v_params_1556_);
lean_closure_set(v___f_1573_, 5, v_numParams_1557_);
lean_closure_set(v___f_1573_, 6, v_indName_1558_);
lean_closure_set(v___f_1573_, 7, v_val_1559_);
lean_closure_set(v___f_1573_, 8, v___x_1560_);
lean_closure_set(v___f_1573_, 9, v___x_1561_);
lean_closure_set(v___f_1573_, 10, v_name_1562_);
lean_closure_set(v___f_1573_, 11, v___x_1563_);
v___x_1574_ = 0;
v___x_1575_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1564_, v___x_1565_, v___f_1573_, v___x_1574_, v___x_1574_, v___y_1568_, v___y_1569_, v___y_1570_, v___y_1571_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1576_ = _args[0];
lean_object* v_ctors_1577_ = _args[1];
lean_object* v_tail_1578_ = _args[2];
lean_object* v_params_1579_ = _args[3];
lean_object* v_numParams_1580_ = _args[4];
lean_object* v_indName_1581_ = _args[5];
lean_object* v_val_1582_ = _args[6];
lean_object* v___x_1583_ = _args[7];
lean_object* v___x_1584_ = _args[8];
lean_object* v_name_1585_ = _args[9];
lean_object* v___x_1586_ = _args[10];
lean_object* v_t_1587_ = _args[11];
lean_object* v___x_1588_ = _args[12];
lean_object* v_ism1_1589_ = _args[13];
lean_object* v_x_1590_ = _args[14];
lean_object* v___y_1591_ = _args[15];
lean_object* v___y_1592_ = _args[16];
lean_object* v___y_1593_ = _args[17];
lean_object* v___y_1594_ = _args[18];
lean_object* v___y_1595_ = _args[19];
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1576_, v_ctors_1577_, v_tail_1578_, v_params_1579_, v_numParams_1580_, v_indName_1581_, v_val_1582_, v___x_1583_, v___x_1584_, v_name_1585_, v___x_1586_, v_t_1587_, v___x_1588_, v_ism1_1589_, v_x_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v_x_1590_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1597_, lean_object* v___x_1598_, lean_object* v_head_1599_, lean_object* v_ctors_1600_, lean_object* v_tail_1601_, lean_object* v_params_1602_, lean_object* v_numParams_1603_, lean_object* v_indName_1604_, lean_object* v_val_1605_, lean_object* v___x_1606_, lean_object* v___x_1607_, lean_object* v_name_1608_, lean_object* v_x_1609_, lean_object* v_t_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___f_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1616_ = lean_nat_add(v_numIndices_1597_, v___x_1598_);
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_inc_ref(v___x_1617_);
lean_inc_ref(v_t_1610_);
v___f_1618_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 20, 13);
lean_closure_set(v___f_1618_, 0, v_head_1599_);
lean_closure_set(v___f_1618_, 1, v_ctors_1600_);
lean_closure_set(v___f_1618_, 2, v_tail_1601_);
lean_closure_set(v___f_1618_, 3, v_params_1602_);
lean_closure_set(v___f_1618_, 4, v_numParams_1603_);
lean_closure_set(v___f_1618_, 5, v_indName_1604_);
lean_closure_set(v___f_1618_, 6, v_val_1605_);
lean_closure_set(v___f_1618_, 7, v___x_1606_);
lean_closure_set(v___f_1618_, 8, v___x_1607_);
lean_closure_set(v___f_1618_, 9, v_name_1608_);
lean_closure_set(v___f_1618_, 10, v___x_1598_);
lean_closure_set(v___f_1618_, 11, v_t_1610_);
lean_closure_set(v___f_1618_, 12, v___x_1617_);
v___x_1619_ = 0;
v___x_1620_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1610_, v___x_1617_, v___f_1618_, v___x_1619_, v___x_1619_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1621_ = _args[0];
lean_object* v___x_1622_ = _args[1];
lean_object* v_head_1623_ = _args[2];
lean_object* v_ctors_1624_ = _args[3];
lean_object* v_tail_1625_ = _args[4];
lean_object* v_params_1626_ = _args[5];
lean_object* v_numParams_1627_ = _args[6];
lean_object* v_indName_1628_ = _args[7];
lean_object* v_val_1629_ = _args[8];
lean_object* v___x_1630_ = _args[9];
lean_object* v___x_1631_ = _args[10];
lean_object* v_name_1632_ = _args[11];
lean_object* v_x_1633_ = _args[12];
lean_object* v_t_1634_ = _args[13];
lean_object* v___y_1635_ = _args[14];
lean_object* v___y_1636_ = _args[15];
lean_object* v___y_1637_ = _args[16];
lean_object* v___y_1638_ = _args[17];
lean_object* v___y_1639_ = _args[18];
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1621_, v___x_1622_, v_head_1623_, v_ctors_1624_, v_tail_1625_, v_params_1626_, v_numParams_1627_, v_indName_1628_, v_val_1629_, v___x_1630_, v___x_1631_, v_name_1632_, v_x_1633_, v_t_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec_ref(v_x_1633_);
lean_dec(v_numIndices_1621_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1643_, lean_object* v_head_1644_, lean_object* v_ctors_1645_, lean_object* v_tail_1646_, lean_object* v_numParams_1647_, lean_object* v_indName_1648_, lean_object* v_val_1649_, lean_object* v___x_1650_, lean_object* v___x_1651_, lean_object* v_name_1652_, lean_object* v_params_1653_, lean_object* v_t_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; lean_object* v___f_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; lean_object* v___x_1664_; 
v___x_1660_ = lean_unsigned_to_nat(1u);
v___f_1661_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 19, 12);
lean_closure_set(v___f_1661_, 0, v_numIndices_1643_);
lean_closure_set(v___f_1661_, 1, v___x_1660_);
lean_closure_set(v___f_1661_, 2, v_head_1644_);
lean_closure_set(v___f_1661_, 3, v_ctors_1645_);
lean_closure_set(v___f_1661_, 4, v_tail_1646_);
lean_closure_set(v___f_1661_, 5, v_params_1653_);
lean_closure_set(v___f_1661_, 6, v_numParams_1647_);
lean_closure_set(v___f_1661_, 7, v_indName_1648_);
lean_closure_set(v___f_1661_, 8, v_val_1649_);
lean_closure_set(v___f_1661_, 9, v___x_1650_);
lean_closure_set(v___f_1661_, 10, v___x_1651_);
lean_closure_set(v___f_1661_, 11, v_name_1652_);
v___x_1662_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1663_ = 0;
v___x_1664_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1654_, v___x_1662_, v___f_1661_, v___x_1663_, v___x_1663_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1665_ = _args[0];
lean_object* v_head_1666_ = _args[1];
lean_object* v_ctors_1667_ = _args[2];
lean_object* v_tail_1668_ = _args[3];
lean_object* v_numParams_1669_ = _args[4];
lean_object* v_indName_1670_ = _args[5];
lean_object* v_val_1671_ = _args[6];
lean_object* v___x_1672_ = _args[7];
lean_object* v___x_1673_ = _args[8];
lean_object* v_name_1674_ = _args[9];
lean_object* v_params_1675_ = _args[10];
lean_object* v_t_1676_ = _args[11];
lean_object* v___y_1677_ = _args[12];
lean_object* v___y_1678_ = _args[13];
lean_object* v___y_1679_ = _args[14];
lean_object* v___y_1680_ = _args[15];
lean_object* v___y_1681_ = _args[16];
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1665_, v_head_1666_, v_ctors_1667_, v_tail_1668_, v_numParams_1669_, v_indName_1670_, v_val_1671_, v___x_1672_, v___x_1673_, v_name_1674_, v_params_1675_, v_t_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1683_, lean_object* v_declName_1684_, lean_object* v_levelParams_1685_, uint8_t v___x_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
lean_inc_ref(v_a_1683_);
v___x_1692_ = lean_infer_type(v_a_1683_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1704_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___x_1694_ = lean_box(1);
v___x_1695_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1684_, v_levelParams_1685_, v_a_1693_, v_a_1683_, v___x_1694_, v___y_1690_);
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1704_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
lean_ctor_set_tag(v___x_1698_, 1);
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_addDecl(v___x_1701_, v___x_1686_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v___x_1702_;
}
}
}
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_levelParams_1685_);
lean_dec(v_declName_1684_);
lean_dec_ref(v_a_1683_);
v_a_1705_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1692_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1692_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1713_, lean_object* v_declName_1714_, lean_object* v_levelParams_1715_, lean_object* v___x_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
uint8_t v___x_22343__boxed_1722_; lean_object* v_res_1723_; 
v___x_22343__boxed_1722_ = lean_unbox(v___x_1716_);
v_res_1723_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1713_, v_declName_1714_, v_levelParams_1715_, v___x_22343__boxed_1722_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1724_, lean_object* v_a_1725_){
_start:
{
if (lean_obj_tag(v_a_1724_) == 0)
{
lean_object* v___x_1726_; 
v___x_1726_ = l_List_reverse___redArg(v_a_1725_);
return v___x_1726_;
}
else
{
lean_object* v_head_1727_; lean_object* v_tail_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1737_; 
v_head_1727_ = lean_ctor_get(v_a_1724_, 0);
v_tail_1728_ = lean_ctor_get(v_a_1724_, 1);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_a_1724_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1730_ = v_a_1724_;
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_tail_1728_);
lean_inc(v_head_1727_);
lean_dec(v_a_1724_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1737_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1732_ = l_Lean_mkLevelParam(v_head_1727_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 1, v_a_1725_);
lean_ctor_set(v___x_1730_, 0, v___x_1732_);
v___x_1734_ = v___x_1730_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_a_1725_);
v___x_1734_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
v_a_1724_ = v_tail_1728_;
v_a_1725_ = v___x_1734_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object* v_msgData_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; lean_object* v_env_1745_; lean_object* v___x_1746_; lean_object* v_mctx_1747_; lean_object* v_lctx_1748_; lean_object* v_options_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1744_ = lean_st_ref_get(v___y_1742_);
v_env_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc_ref(v_env_1745_);
lean_dec(v___x_1744_);
v___x_1746_ = lean_st_ref_get(v___y_1740_);
v_mctx_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_ref(v_mctx_1747_);
lean_dec(v___x_1746_);
v_lctx_1748_ = lean_ctor_get(v___y_1739_, 2);
v_options_1749_ = lean_ctor_get(v___y_1741_, 2);
lean_inc_ref(v_options_1749_);
lean_inc_ref(v_lctx_1748_);
v___x_1750_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1750_, 0, v_env_1745_);
lean_ctor_set(v___x_1750_, 1, v_mctx_1747_);
lean_ctor_set(v___x_1750_, 2, v_lctx_1748_);
lean_ctor_set(v___x_1750_, 3, v_options_1749_);
v___x_1751_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v_msgData_1738_);
v___x_1752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1752_, 0, v___x_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v_ref_1766_; lean_object* v___x_1767_; lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1776_; 
v_ref_1766_ = lean_ctor_get(v___y_1763_, 5);
v___x_1767_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1776_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1776_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1772_; lean_object* v___x_1774_; 
lean_inc(v_ref_1766_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_ref_1766_);
lean_ctor_set(v___x_1772_, 1, v_a_1768_);
if (v_isShared_1771_ == 0)
{
lean_ctor_set_tag(v___x_1770_, 1);
lean_ctor_set(v___x_1770_, 0, v___x_1772_);
v___x_1774_ = v___x_1770_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1784_, lean_object* v_msg_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v_fileName_1791_; lean_object* v_fileMap_1792_; lean_object* v_options_1793_; lean_object* v_currRecDepth_1794_; lean_object* v_maxRecDepth_1795_; lean_object* v_ref_1796_; lean_object* v_currNamespace_1797_; lean_object* v_openDecls_1798_; lean_object* v_initHeartbeats_1799_; lean_object* v_maxHeartbeats_1800_; lean_object* v_quotContext_1801_; lean_object* v_currMacroScope_1802_; uint8_t v_diag_1803_; lean_object* v_cancelTk_x3f_1804_; uint8_t v_suppressElabErrors_1805_; lean_object* v_inheritedTraceOptions_1806_; lean_object* v_ref_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v_fileName_1791_ = lean_ctor_get(v___y_1788_, 0);
v_fileMap_1792_ = lean_ctor_get(v___y_1788_, 1);
v_options_1793_ = lean_ctor_get(v___y_1788_, 2);
v_currRecDepth_1794_ = lean_ctor_get(v___y_1788_, 3);
v_maxRecDepth_1795_ = lean_ctor_get(v___y_1788_, 4);
v_ref_1796_ = lean_ctor_get(v___y_1788_, 5);
v_currNamespace_1797_ = lean_ctor_get(v___y_1788_, 6);
v_openDecls_1798_ = lean_ctor_get(v___y_1788_, 7);
v_initHeartbeats_1799_ = lean_ctor_get(v___y_1788_, 8);
v_maxHeartbeats_1800_ = lean_ctor_get(v___y_1788_, 9);
v_quotContext_1801_ = lean_ctor_get(v___y_1788_, 10);
v_currMacroScope_1802_ = lean_ctor_get(v___y_1788_, 11);
v_diag_1803_ = lean_ctor_get_uint8(v___y_1788_, sizeof(void*)*14);
v_cancelTk_x3f_1804_ = lean_ctor_get(v___y_1788_, 12);
v_suppressElabErrors_1805_ = lean_ctor_get_uint8(v___y_1788_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1806_ = lean_ctor_get(v___y_1788_, 13);
v_ref_1807_ = l_Lean_replaceRef(v_ref_1784_, v_ref_1796_);
lean_inc_ref(v_inheritedTraceOptions_1806_);
lean_inc(v_cancelTk_x3f_1804_);
lean_inc(v_currMacroScope_1802_);
lean_inc(v_quotContext_1801_);
lean_inc(v_maxHeartbeats_1800_);
lean_inc(v_initHeartbeats_1799_);
lean_inc(v_openDecls_1798_);
lean_inc(v_currNamespace_1797_);
lean_inc(v_maxRecDepth_1795_);
lean_inc(v_currRecDepth_1794_);
lean_inc_ref(v_options_1793_);
lean_inc_ref(v_fileMap_1792_);
lean_inc_ref(v_fileName_1791_);
v___x_1808_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1808_, 0, v_fileName_1791_);
lean_ctor_set(v___x_1808_, 1, v_fileMap_1792_);
lean_ctor_set(v___x_1808_, 2, v_options_1793_);
lean_ctor_set(v___x_1808_, 3, v_currRecDepth_1794_);
lean_ctor_set(v___x_1808_, 4, v_maxRecDepth_1795_);
lean_ctor_set(v___x_1808_, 5, v_ref_1807_);
lean_ctor_set(v___x_1808_, 6, v_currNamespace_1797_);
lean_ctor_set(v___x_1808_, 7, v_openDecls_1798_);
lean_ctor_set(v___x_1808_, 8, v_initHeartbeats_1799_);
lean_ctor_set(v___x_1808_, 9, v_maxHeartbeats_1800_);
lean_ctor_set(v___x_1808_, 10, v_quotContext_1801_);
lean_ctor_set(v___x_1808_, 11, v_currMacroScope_1802_);
lean_ctor_set(v___x_1808_, 12, v_cancelTk_x3f_1804_);
lean_ctor_set(v___x_1808_, 13, v_inheritedTraceOptions_1806_);
lean_ctor_set_uint8(v___x_1808_, sizeof(void*)*14, v_diag_1803_);
lean_ctor_set_uint8(v___x_1808_, sizeof(void*)*14 + 1, v_suppressElabErrors_1805_);
v___x_1809_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1785_, v___y_1786_, v___y_1787_, v___x_1808_, v___y_1789_);
lean_dec_ref_known(v___x_1808_, 14);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1810_, lean_object* v_msg_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1810_, v_msg_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
lean_dec(v_ref_1810_);
return v_res_1817_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1818_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
lean_ctor_set(v___x_1823_, 2, v___x_1822_);
lean_ctor_set(v___x_1823_, 3, v___x_1822_);
lean_ctor_set(v___x_1823_, 4, v___x_1821_);
lean_ctor_set(v___x_1823_, 5, v___x_1821_);
lean_ctor_set(v___x_1823_, 6, v___x_1821_);
lean_ctor_set(v___x_1823_, 7, v___x_1821_);
lean_ctor_set(v___x_1823_, 8, v___x_1821_);
lean_ctor_set(v___x_1823_, 9, v___x_1821_);
return v___x_1823_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = lean_unsigned_to_nat(32u);
v___x_1825_ = lean_mk_empty_array_with_capacity(v___x_1824_);
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1827_ = ((size_t)5ULL);
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = lean_unsigned_to_nat(32u);
v___x_1830_ = lean_mk_empty_array_with_capacity(v___x_1829_);
v___x_1831_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1832_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1832_, 0, v___x_1831_);
lean_ctor_set(v___x_1832_, 1, v___x_1830_);
lean_ctor_set(v___x_1832_, 2, v___x_1828_);
lean_ctor_set(v___x_1832_, 3, v___x_1828_);
lean_ctor_set_usize(v___x_1832_, 4, v___x_1827_);
return v___x_1832_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1833_ = lean_box(1);
v___x_1834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1835_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v___x_1834_);
lean_ctor_set(v___x_1836_, 2, v___x_1833_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6));
v___x_1839_ = l_Lean_stringToMessageData(v___x_1838_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1841_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8));
v___x_1842_ = l_Lean_stringToMessageData(v___x_1841_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10));
v___x_1845_ = l_Lean_stringToMessageData(v___x_1844_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1847_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12));
v___x_1848_ = l_Lean_stringToMessageData(v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14));
v___x_1851_ = l_Lean_stringToMessageData(v___x_1850_);
return v___x_1851_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16));
v___x_1854_ = l_Lean_stringToMessageData(v___x_1853_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1856_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18));
v___x_1857_ = l_Lean_stringToMessageData(v___x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1858_, lean_object* v_declHint_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; lean_object* v_env_1863_; uint8_t v___x_1864_; 
v___x_1862_ = lean_st_ref_get(v___y_1860_);
v_env_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc_ref(v_env_1863_);
lean_dec(v___x_1862_);
v___x_1864_ = l_Lean_Name_isAnonymous(v_declHint_1859_);
if (v___x_1864_ == 0)
{
uint8_t v_isExporting_1865_; 
v_isExporting_1865_ = lean_ctor_get_uint8(v_env_1863_, sizeof(void*)*8);
if (v_isExporting_1865_ == 0)
{
lean_object* v___x_1866_; 
lean_dec_ref(v_env_1863_);
lean_dec(v_declHint_1859_);
v___x_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_msg_1858_);
return v___x_1866_;
}
else
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
lean_inc_ref(v_env_1863_);
v___x_1867_ = l_Lean_Environment_setExporting(v_env_1863_, v___x_1864_);
lean_inc(v_declHint_1859_);
lean_inc_ref(v___x_1867_);
v___x_1868_ = l_Lean_Environment_contains(v___x_1867_, v_declHint_1859_, v_isExporting_1865_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; 
lean_dec_ref(v___x_1867_);
lean_dec_ref(v_env_1863_);
lean_dec(v_declHint_1859_);
v___x_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1869_, 0, v_msg_1858_);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v_c_1875_; lean_object* v___x_1876_; 
v___x_1870_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5);
v___x_1872_ = l_Lean_Options_empty;
v___x_1873_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1867_);
lean_ctor_set(v___x_1873_, 1, v___x_1870_);
lean_ctor_set(v___x_1873_, 2, v___x_1871_);
lean_ctor_set(v___x_1873_, 3, v___x_1872_);
lean_inc(v_declHint_1859_);
v___x_1874_ = l_Lean_MessageData_ofConstName(v_declHint_1859_, v___x_1864_);
v_c_1875_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1875_, 0, v___x_1873_);
lean_ctor_set(v_c_1875_, 1, v___x_1874_);
v___x_1876_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1863_, v_declHint_1859_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
lean_dec_ref(v_env_1863_);
lean_dec(v_declHint_1859_);
v___x_1877_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v_c_1875_);
v___x_1879_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9);
v___x_1880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = l_Lean_MessageData_note(v___x_1880_);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_msg_1858_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
else
{
lean_object* v_val_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1919_; 
v_val_1884_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1886_ = v___x_1876_;
v_isShared_1887_ = v_isSharedCheck_1919_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_val_1884_);
lean_dec(v___x_1876_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1919_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v_mod_1891_; uint8_t v___x_1892_; 
v___x_1888_ = lean_box(0);
v___x_1889_ = l_Lean_Environment_header(v_env_1863_);
lean_dec_ref(v_env_1863_);
v___x_1890_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1889_);
v_mod_1891_ = lean_array_get(v___x_1888_, v___x_1890_, v_val_1884_);
lean_dec(v_val_1884_);
lean_dec_ref(v___x_1890_);
v___x_1892_ = l_Lean_isPrivateName(v_declHint_1859_);
lean_dec(v_declHint_1859_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1893_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
lean_ctor_set(v___x_1894_, 1, v_c_1875_);
v___x_1895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = l_Lean_MessageData_ofName(v_mod_1891_);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = l_Lean_MessageData_note(v___x_1900_);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v_msg_1858_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1902_);
v___x_1904_ = v___x_1886_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
else
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
lean_ctor_set(v___x_1907_, 1, v_c_1875_);
v___x_1908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = l_Lean_MessageData_ofName(v_mod_1891_);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = l_Lean_MessageData_note(v___x_1913_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v_msg_1858_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1915_);
v___x_1917_ = v___x_1886_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1920_; 
lean_dec_ref(v_env_1863_);
lean_dec(v_declHint_1859_);
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v_msg_1858_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1921_, lean_object* v_declHint_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1921_, v_declHint_1922_, v___y_1923_);
lean_dec(v___y_1923_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1926_, lean_object* v_declHint_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v___x_1933_; lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1943_; 
v___x_1933_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1926_, v_declHint_1927_, v___y_1931_);
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1936_ = v___x_1933_;
v_isShared_1937_ = v_isSharedCheck_1943_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1933_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1943_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1938_ = l_Lean_unknownIdentifierMessageTag;
v___x_1939_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v_a_1934_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set(v___x_1936_, 0, v___x_1939_);
v___x_1941_ = v___x_1936_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1944_, lean_object* v_declHint_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1944_, v_declHint_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
lean_dec(v___y_1949_);
lean_dec_ref(v___y_1948_);
lean_dec(v___y_1947_);
lean_dec_ref(v___y_1946_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1952_, lean_object* v_msg_1953_, lean_object* v_declHint_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v___x_1960_; lean_object* v_a_1961_; lean_object* v___x_1962_; 
v___x_1960_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1953_, v_declHint_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref(v___x_1960_);
v___x_1962_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1952_, v_a_1961_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1963_, lean_object* v_msg_1964_, lean_object* v_declHint_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1963_, v_msg_1964_, v_declHint_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v_ref_1963_);
return v_res_1971_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_1974_ = l_Lean_stringToMessageData(v___x_1973_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_1977_ = l_Lean_stringToMessageData(v___x_1976_);
return v___x_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_1978_, lean_object* v_constName_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v___x_1985_; uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1985_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_1986_ = 0;
lean_inc(v_constName_1979_);
v___x_1987_ = l_Lean_MessageData_ofConstName(v_constName_1979_, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1985_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
v___x_1991_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1978_, v___x_1990_, v_constName_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_1992_, lean_object* v_constName_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1992_, v_constName_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
lean_dec(v_ref_1992_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v_ref_2006_; lean_object* v___x_2007_; 
v_ref_2006_ = lean_ctor_get(v___y_2003_, 5);
v___x_2007_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2006_, v_constName_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
lean_dec(v___y_2012_);
lean_dec_ref(v___y_2011_);
lean_dec(v___y_2010_);
lean_dec_ref(v___y_2009_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; lean_object* v_env_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; 
v___x_2021_ = lean_st_ref_get(v___y_2019_);
v_env_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc_ref(v_env_2022_);
lean_dec(v___x_2021_);
v___x_2023_ = 0;
lean_inc(v_constName_2015_);
v___x_2024_ = l_Lean_Environment_findConstVal_x3f(v_env_2022_, v_constName_2015_, v___x_2023_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2025_;
}
else
{
lean_object* v_val_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2033_; 
lean_dec(v_constName_2015_);
v_val_2026_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2028_ = v___x_2024_;
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_val_2026_);
lean_dec(v___x_2024_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2033_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 0);
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_val_2026_);
v___x_2031_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
return v___x_2031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_){
_start:
{
lean_object* v_res_2040_; 
v_res_2040_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2034_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
lean_dec(v___y_2038_);
lean_dec_ref(v___y_2037_);
lean_dec(v___y_2036_);
lean_dec_ref(v___y_2035_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2041_, uint8_t v_s_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v___x_2046_; lean_object* v_env_2047_; lean_object* v_nextMacroScope_2048_; lean_object* v_ngen_2049_; lean_object* v_auxDeclNGen_2050_; lean_object* v_traceState_2051_; lean_object* v_messages_2052_; lean_object* v_infoState_2053_; lean_object* v_snapshotTasks_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2083_; 
v___x_2046_ = lean_st_ref_take(v___y_2044_);
v_env_2047_ = lean_ctor_get(v___x_2046_, 0);
v_nextMacroScope_2048_ = lean_ctor_get(v___x_2046_, 1);
v_ngen_2049_ = lean_ctor_get(v___x_2046_, 2);
v_auxDeclNGen_2050_ = lean_ctor_get(v___x_2046_, 3);
v_traceState_2051_ = lean_ctor_get(v___x_2046_, 4);
v_messages_2052_ = lean_ctor_get(v___x_2046_, 6);
v_infoState_2053_ = lean_ctor_get(v___x_2046_, 7);
v_snapshotTasks_2054_ = lean_ctor_get(v___x_2046_, 8);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v___x_2046_, 5);
lean_dec(v_unused_2084_);
v___x_2056_ = v___x_2046_;
v_isShared_2057_ = v_isSharedCheck_2083_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_snapshotTasks_2054_);
lean_inc(v_infoState_2053_);
lean_inc(v_messages_2052_);
lean_inc(v_traceState_2051_);
lean_inc(v_auxDeclNGen_2050_);
lean_inc(v_ngen_2049_);
lean_inc(v_nextMacroScope_2048_);
lean_inc(v_env_2047_);
lean_dec(v___x_2046_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2083_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
uint8_t v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
v___x_2058_ = 0;
v___x_2059_ = lean_box(0);
v___x_2060_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2047_, v_declName_2041_, v_s_2042_, v___x_2058_, v___x_2059_);
v___x_2061_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 5, v___x_2061_);
lean_ctor_set(v___x_2056_, 0, v___x_2060_);
v___x_2063_ = v___x_2056_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_nextMacroScope_2048_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_ngen_2049_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v_auxDeclNGen_2050_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v_traceState_2051_);
lean_ctor_set(v_reuseFailAlloc_2082_, 5, v___x_2061_);
lean_ctor_set(v_reuseFailAlloc_2082_, 6, v_messages_2052_);
lean_ctor_set(v_reuseFailAlloc_2082_, 7, v_infoState_2053_);
lean_ctor_set(v_reuseFailAlloc_2082_, 8, v_snapshotTasks_2054_);
v___x_2063_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v_mctx_2066_; lean_object* v_zetaDeltaFVarIds_2067_; lean_object* v_postponed_2068_; lean_object* v_diag_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2080_; 
v___x_2064_ = lean_st_ref_set(v___y_2044_, v___x_2063_);
v___x_2065_ = lean_st_ref_take(v___y_2043_);
v_mctx_2066_ = lean_ctor_get(v___x_2065_, 0);
v_zetaDeltaFVarIds_2067_ = lean_ctor_get(v___x_2065_, 2);
v_postponed_2068_ = lean_ctor_get(v___x_2065_, 3);
v_diag_2069_ = lean_ctor_get(v___x_2065_, 4);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v___x_2065_, 1);
lean_dec(v_unused_2081_);
v___x_2071_ = v___x_2065_;
v_isShared_2072_ = v_isSharedCheck_2080_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_diag_2069_);
lean_inc(v_postponed_2068_);
lean_inc(v_zetaDeltaFVarIds_2067_);
lean_inc(v_mctx_2066_);
lean_dec(v___x_2065_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2080_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 1, v___x_2073_);
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_mctx_2066_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_zetaDeltaFVarIds_2067_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_postponed_2068_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_diag_2069_);
v___x_2075_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_st_ref_set(v___y_2043_, v___x_2075_);
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
return v___x_2078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2085_, lean_object* v_s_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
uint8_t v_s_boxed_2090_; lean_object* v_res_2091_; 
v_s_boxed_2090_ = lean_unbox(v_s_2086_);
v_res_2091_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2085_, v_s_boxed_2090_, v___y_2087_, v___y_2088_);
lean_dec(v___y_2088_);
lean_dec(v___y_2087_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
uint8_t v___x_2098_; lean_object* v___x_2099_; 
v___x_2098_ = 0;
v___x_2099_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2092_, v___x_2098_, v___y_2094_, v___y_2096_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2106_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2109_ = l_Lean_stringToMessageData(v___x_2108_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2112_ = l_Lean_stringToMessageData(v___x_2111_);
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2115_ = l_Lean_stringToMessageData(v___x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2116_, lean_object* v_declName_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2123_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2124_ = l_Lean_MessageData_ofName(v_attrName_2116_);
v___x_2125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = 0;
v___x_2129_ = l_Lean_MessageData_ofConstName(v_declName_2117_, v___x_2128_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2127_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2132_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2134_, lean_object* v_declName_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2134_, v_declName_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v_res_2141_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; 
v___x_2143_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2144_ = l_Lean_stringToMessageData(v___x_2143_);
return v___x_2144_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2147_ = l_Lean_stringToMessageData(v___x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2148_, lean_object* v_declName_2149_, lean_object* v_asyncPrefix_x3f_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v___y_2157_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2150_) == 0)
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_MessageData_nil;
v___y_2157_ = v___x_2170_;
goto v___jp_2156_;
}
else
{
lean_object* v_val_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_val_2171_ = lean_ctor_get(v_asyncPrefix_x3f_2150_, 0);
lean_inc(v_val_2171_);
lean_dec_ref_known(v_asyncPrefix_x3f_2150_, 1);
v___x_2172_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2173_ = l_Lean_MessageData_ofName(v_val_2171_);
v___x_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2172_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___y_2157_ = v___x_2176_;
goto v___jp_2156_;
}
v___jp_2156_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; uint8_t v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2158_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2159_ = l_Lean_MessageData_ofName(v_attrName_2148_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2158_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = 0;
v___x_2164_ = l_Lean_MessageData_ofConstName(v_declName_2149_, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2162_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
lean_ctor_set(v___x_2168_, 1, v___y_2157_);
v___x_2169_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2168_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
return v___x_2169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2177_, lean_object* v_declName_2178_, lean_object* v_asyncPrefix_x3f_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2177_, v_declName_2178_, v_asyncPrefix_x3f_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2186_, lean_object* v_decl_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___x_2236_; lean_object* v_env_2237_; lean_object* v___y_2239_; lean_object* v___y_2240_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___x_2252_; 
v___x_2236_ = lean_st_ref_get(v___y_2191_);
v_env_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc_ref(v_env_2237_);
lean_dec(v___x_2236_);
v___x_2252_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2237_, v_decl_2187_);
if (lean_obj_tag(v___x_2252_) == 0)
{
v___y_2239_ = v___y_2188_;
v___y_2240_ = v___y_2189_;
v___y_2241_ = v___y_2190_;
v___y_2242_ = v___y_2191_;
goto v___jp_2238_;
}
else
{
lean_object* v_attr_2253_; lean_object* v_toAttributeImplCore_2254_; lean_object* v_name_2255_; lean_object* v___x_2256_; 
lean_dec_ref_known(v___x_2252_, 1);
lean_dec_ref(v_env_2237_);
v_attr_2253_ = lean_ctor_get(v_attr_2186_, 0);
lean_inc_ref(v_attr_2253_);
lean_dec_ref(v_attr_2186_);
v_toAttributeImplCore_2254_ = lean_ctor_get(v_attr_2253_, 0);
lean_inc_ref(v_toAttributeImplCore_2254_);
lean_dec_ref(v_attr_2253_);
v_name_2255_ = lean_ctor_get(v_toAttributeImplCore_2254_, 1);
lean_inc(v_name_2255_);
lean_dec_ref(v_toAttributeImplCore_2254_);
v___x_2256_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2255_, v_decl_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
return v___x_2256_;
}
v___jp_2193_:
{
lean_object* v___x_2196_; lean_object* v_ext_2197_; lean_object* v_toEnvExtension_2198_; lean_object* v_env_2199_; lean_object* v_nextMacroScope_2200_; lean_object* v_ngen_2201_; lean_object* v_auxDeclNGen_2202_; lean_object* v_traceState_2203_; lean_object* v_messages_2204_; lean_object* v_infoState_2205_; lean_object* v_snapshotTasks_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2234_; 
v___x_2196_ = lean_st_ref_take(v___y_2195_);
v_ext_2197_ = lean_ctor_get(v_attr_2186_, 1);
lean_inc_ref(v_ext_2197_);
lean_dec_ref(v_attr_2186_);
v_toEnvExtension_2198_ = lean_ctor_get(v_ext_2197_, 0);
v_env_2199_ = lean_ctor_get(v___x_2196_, 0);
v_nextMacroScope_2200_ = lean_ctor_get(v___x_2196_, 1);
v_ngen_2201_ = lean_ctor_get(v___x_2196_, 2);
v_auxDeclNGen_2202_ = lean_ctor_get(v___x_2196_, 3);
v_traceState_2203_ = lean_ctor_get(v___x_2196_, 4);
v_messages_2204_ = lean_ctor_get(v___x_2196_, 6);
v_infoState_2205_ = lean_ctor_get(v___x_2196_, 7);
v_snapshotTasks_2206_ = lean_ctor_get(v___x_2196_, 8);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v___x_2196_, 5);
lean_dec(v_unused_2235_);
v___x_2208_ = v___x_2196_;
v_isShared_2209_ = v_isSharedCheck_2234_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_snapshotTasks_2206_);
lean_inc(v_infoState_2205_);
lean_inc(v_messages_2204_);
lean_inc(v_traceState_2203_);
lean_inc(v_auxDeclNGen_2202_);
lean_inc(v_ngen_2201_);
lean_inc(v_nextMacroScope_2200_);
lean_inc(v_env_2199_);
lean_dec(v___x_2196_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2234_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v_asyncMode_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2214_; 
v_asyncMode_2210_ = lean_ctor_get(v_toEnvExtension_2198_, 2);
lean_inc(v_asyncMode_2210_);
lean_inc(v_decl_2187_);
v___x_2211_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2197_, v_env_2199_, v_decl_2187_, v_asyncMode_2210_, v_decl_2187_);
lean_dec(v_asyncMode_2210_);
v___x_2212_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 5, v___x_2212_);
lean_ctor_set(v___x_2208_, 0, v___x_2211_);
v___x_2214_ = v___x_2208_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2233_, 1, v_nextMacroScope_2200_);
lean_ctor_set(v_reuseFailAlloc_2233_, 2, v_ngen_2201_);
lean_ctor_set(v_reuseFailAlloc_2233_, 3, v_auxDeclNGen_2202_);
lean_ctor_set(v_reuseFailAlloc_2233_, 4, v_traceState_2203_);
lean_ctor_set(v_reuseFailAlloc_2233_, 5, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2233_, 6, v_messages_2204_);
lean_ctor_set(v_reuseFailAlloc_2233_, 7, v_infoState_2205_);
lean_ctor_set(v_reuseFailAlloc_2233_, 8, v_snapshotTasks_2206_);
v___x_2214_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v_mctx_2217_; lean_object* v_zetaDeltaFVarIds_2218_; lean_object* v_postponed_2219_; lean_object* v_diag_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2231_; 
v___x_2215_ = lean_st_ref_set(v___y_2195_, v___x_2214_);
v___x_2216_ = lean_st_ref_take(v___y_2194_);
v_mctx_2217_ = lean_ctor_get(v___x_2216_, 0);
v_zetaDeltaFVarIds_2218_ = lean_ctor_get(v___x_2216_, 2);
v_postponed_2219_ = lean_ctor_get(v___x_2216_, 3);
v_diag_2220_ = lean_ctor_get(v___x_2216_, 4);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; 
v_unused_2232_ = lean_ctor_get(v___x_2216_, 1);
lean_dec(v_unused_2232_);
v___x_2222_ = v___x_2216_;
v_isShared_2223_ = v_isSharedCheck_2231_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_diag_2220_);
lean_inc(v_postponed_2219_);
lean_inc(v_zetaDeltaFVarIds_2218_);
lean_inc(v_mctx_2217_);
lean_dec(v___x_2216_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2231_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 1, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_mctx_2217_);
lean_ctor_set(v_reuseFailAlloc_2230_, 1, v___x_2224_);
lean_ctor_set(v_reuseFailAlloc_2230_, 2, v_zetaDeltaFVarIds_2218_);
lean_ctor_set(v_reuseFailAlloc_2230_, 3, v_postponed_2219_);
lean_ctor_set(v_reuseFailAlloc_2230_, 4, v_diag_2220_);
v___x_2226_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2227_ = lean_st_ref_set(v___y_2194_, v___x_2226_);
v___x_2228_ = lean_box(0);
v___x_2229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
}
}
}
}
v___jp_2238_:
{
lean_object* v_ext_2243_; lean_object* v_toEnvExtension_2244_; lean_object* v_attr_2245_; lean_object* v_asyncMode_2246_; uint8_t v___x_2247_; 
v_ext_2243_ = lean_ctor_get(v_attr_2186_, 1);
v_toEnvExtension_2244_ = lean_ctor_get(v_ext_2243_, 0);
v_attr_2245_ = lean_ctor_get(v_attr_2186_, 0);
v_asyncMode_2246_ = lean_ctor_get(v_toEnvExtension_2244_, 2);
lean_inc(v_decl_2187_);
lean_inc_ref(v_env_2237_);
v___x_2247_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2237_, v_decl_2187_, v_asyncMode_2246_);
if (v___x_2247_ == 0)
{
lean_object* v_toAttributeImplCore_2248_; lean_object* v_name_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
lean_inc_ref(v_attr_2245_);
lean_dec_ref(v_attr_2186_);
v_toAttributeImplCore_2248_ = lean_ctor_get(v_attr_2245_, 0);
lean_inc_ref(v_toAttributeImplCore_2248_);
lean_dec_ref(v_attr_2245_);
v_name_2249_ = lean_ctor_get(v_toAttributeImplCore_2248_, 1);
lean_inc(v_name_2249_);
lean_dec_ref(v_toAttributeImplCore_2248_);
v___x_2250_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2237_);
v___x_2251_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2249_, v_decl_2187_, v___x_2250_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
return v___x_2251_;
}
else
{
lean_dec_ref(v_env_2237_);
v___y_2194_ = v___y_2240_;
v___y_2195_ = v___y_2242_;
goto v___jp_2193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2257_, lean_object* v_decl_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2257_, v_decl_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; lean_object* v_env_2272_; uint8_t v___x_2273_; lean_object* v___x_2274_; 
v___x_2271_ = lean_st_ref_get(v___y_2269_);
v_env_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc_ref(v_env_2272_);
lean_dec(v___x_2271_);
v___x_2273_ = 0;
lean_inc(v_constName_2265_);
v___x_2274_ = l_Lean_Environment_find_x3f(v_env_2272_, v_constName_2265_, v___x_2273_);
if (lean_obj_tag(v___x_2274_) == 0)
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2275_;
}
else
{
lean_object* v_val_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v_constName_2265_);
v_val_2276_ = lean_ctor_get(v___x_2274_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2274_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2274_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_val_2276_);
lean_dec(v___x_2274_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
lean_ctor_set_tag(v___x_2278_, 0);
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_val_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_res_2290_; 
v_res_2290_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2290_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2294_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2295_ = lean_unsigned_to_nat(58u);
v___x_2296_ = lean_unsigned_to_nat(33u);
v___x_2297_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2298_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2299_ = l_mkPanicMessageWithDecl(v___x_2298_, v___x_2297_, v___x_2296_, v___x_2295_, v___x_2294_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2301_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2302_ = lean_unsigned_to_nat(60u);
v___x_2303_ = lean_unsigned_to_nat(30u);
v___x_2304_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2305_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2306_ = l_mkPanicMessageWithDecl(v___x_2305_, v___x_2304_, v___x_2303_, v___x_2302_, v___x_2301_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2307_, lean_object* v_indName_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2314_; 
lean_inc(v_indName_2308_);
v___x_2314_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2308_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
if (lean_obj_tag(v_a_2315_) == 5)
{
lean_object* v_val_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2502_; 
v_val_2316_ = lean_ctor_get(v_a_2315_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v_a_2315_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2318_ = v_a_2315_;
v_isShared_2319_ = v_isSharedCheck_2502_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_val_2316_);
lean_dec(v_a_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2502_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_inc(v_indName_2308_);
v___x_2320_ = l_Lean_mkCasesOnName(v_indName_2308_);
lean_inc(v___x_2320_);
v___x_2321_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2320_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v_name_2323_; lean_object* v_levelParams_2324_; lean_object* v_type_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v_name_2323_ = lean_ctor_get(v_a_2322_, 0);
lean_inc(v_name_2323_);
v_levelParams_2324_ = lean_ctor_get(v_a_2322_, 1);
lean_inc_n(v_levelParams_2324_, 2);
v_type_2325_ = lean_ctor_get(v_a_2322_, 2);
lean_inc_ref(v_type_2325_);
lean_dec(v_a_2322_);
v___x_2326_ = lean_box(0);
v___x_2327_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2324_, v___x_2326_);
if (lean_obj_tag(v___x_2327_) == 1)
{
lean_object* v_head_2328_; lean_object* v_tail_2329_; lean_object* v_numParams_2330_; lean_object* v_numIndices_2331_; lean_object* v_ctors_2332_; lean_object* v___f_2333_; lean_object* v___x_2335_; 
v_head_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_head_2328_);
v_tail_2329_ = lean_ctor_get(v___x_2327_, 1);
lean_inc(v_tail_2329_);
v_numParams_2330_ = lean_ctor_get(v_val_2316_, 1);
lean_inc_n(v_numParams_2330_, 2);
v_numIndices_2331_ = lean_ctor_get(v_val_2316_, 2);
lean_inc(v_numIndices_2331_);
v_ctors_2332_ = lean_ctor_get(v_val_2316_, 4);
lean_inc(v_ctors_2332_);
v___f_2333_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2333_, 0, v_numIndices_2331_);
lean_closure_set(v___f_2333_, 1, v_head_2328_);
lean_closure_set(v___f_2333_, 2, v_ctors_2332_);
lean_closure_set(v___f_2333_, 3, v_tail_2329_);
lean_closure_set(v___f_2333_, 4, v_numParams_2330_);
lean_closure_set(v___f_2333_, 5, v_indName_2308_);
lean_closure_set(v___f_2333_, 6, v_val_2316_);
lean_closure_set(v___f_2333_, 7, v___x_2327_);
lean_closure_set(v___f_2333_, 8, v___x_2320_);
lean_closure_set(v___f_2333_, 9, v_name_2323_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set_tag(v___x_2318_, 1);
lean_ctor_set(v___x_2318_, 0, v_numParams_2330_);
v___x_2335_ = v___x_2318_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_numParams_2330_);
v___x_2335_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
uint8_t v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = 0;
v___x_2337_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2325_, v___x_2335_, v___f_2333_, v___x_2336_, v___x_2336_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; lean_object* v___f_2340_; uint8_t v___y_2342_; uint8_t v___x_2481_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = lean_box(v___x_2336_);
lean_inc(v_declName_2307_);
v___f_2340_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2340_, 0, v_a_2338_);
lean_closure_set(v___f_2340_, 1, v_declName_2307_);
lean_closure_set(v___f_2340_, 2, v_levelParams_2324_);
lean_closure_set(v___f_2340_, 3, v___x_2339_);
v___x_2481_ = l_Lean_isPrivateName(v_declName_2307_);
if (v___x_2481_ == 0)
{
uint8_t v___x_2482_; 
v___x_2482_ = 1;
v___y_2342_ = v___x_2482_;
goto v___jp_2341_;
}
else
{
v___y_2342_ = v___x_2336_;
goto v___jp_2341_;
}
v___jp_2341_:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2340_, v___y_2342_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v___x_2344_; lean_object* v_env_2345_; lean_object* v_nextMacroScope_2346_; lean_object* v_ngen_2347_; lean_object* v_auxDeclNGen_2348_; lean_object* v_traceState_2349_; lean_object* v_messages_2350_; lean_object* v_infoState_2351_; lean_object* v_snapshotTasks_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref_known(v___x_2343_, 1);
v___x_2344_ = lean_st_ref_take(v_a_2312_);
v_env_2345_ = lean_ctor_get(v___x_2344_, 0);
v_nextMacroScope_2346_ = lean_ctor_get(v___x_2344_, 1);
v_ngen_2347_ = lean_ctor_get(v___x_2344_, 2);
v_auxDeclNGen_2348_ = lean_ctor_get(v___x_2344_, 3);
v_traceState_2349_ = lean_ctor_get(v___x_2344_, 4);
v_messages_2350_ = lean_ctor_get(v___x_2344_, 6);
v_infoState_2351_ = lean_ctor_get(v___x_2344_, 7);
v_snapshotTasks_2352_ = lean_ctor_get(v___x_2344_, 8);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; 
v_unused_2480_ = lean_ctor_get(v___x_2344_, 5);
lean_dec(v_unused_2480_);
v___x_2354_ = v___x_2344_;
v_isShared_2355_ = v_isSharedCheck_2479_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_snapshotTasks_2352_);
lean_inc(v_infoState_2351_);
lean_inc(v_messages_2350_);
lean_inc(v_traceState_2349_);
lean_inc(v_auxDeclNGen_2348_);
lean_inc(v_ngen_2347_);
lean_inc(v_nextMacroScope_2346_);
lean_inc(v_env_2345_);
lean_dec(v___x_2344_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2479_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2359_; 
lean_inc(v_declName_2307_);
v___x_2356_ = l_Lean_Meta_markMatcherLike(v_env_2345_, v_declName_2307_);
v___x_2357_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 5, v___x_2357_);
lean_ctor_set(v___x_2354_, 0, v___x_2356_);
v___x_2359_ = v___x_2354_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_nextMacroScope_2346_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v_ngen_2347_);
lean_ctor_set(v_reuseFailAlloc_2478_, 3, v_auxDeclNGen_2348_);
lean_ctor_set(v_reuseFailAlloc_2478_, 4, v_traceState_2349_);
lean_ctor_set(v_reuseFailAlloc_2478_, 5, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2478_, 6, v_messages_2350_);
lean_ctor_set(v_reuseFailAlloc_2478_, 7, v_infoState_2351_);
lean_ctor_set(v_reuseFailAlloc_2478_, 8, v_snapshotTasks_2352_);
v___x_2359_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v_mctx_2362_; lean_object* v_zetaDeltaFVarIds_2363_; lean_object* v_postponed_2364_; lean_object* v_diag_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2476_; 
v___x_2360_ = lean_st_ref_set(v_a_2312_, v___x_2359_);
v___x_2361_ = lean_st_ref_take(v_a_2310_);
v_mctx_2362_ = lean_ctor_get(v___x_2361_, 0);
v_zetaDeltaFVarIds_2363_ = lean_ctor_get(v___x_2361_, 2);
v_postponed_2364_ = lean_ctor_get(v___x_2361_, 3);
v_diag_2365_ = lean_ctor_get(v___x_2361_, 4);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2361_, 1);
lean_dec(v_unused_2477_);
v___x_2367_ = v___x_2361_;
v_isShared_2368_ = v_isSharedCheck_2476_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_diag_2365_);
lean_inc(v_postponed_2364_);
lean_inc(v_zetaDeltaFVarIds_2363_);
lean_inc(v_mctx_2362_);
lean_dec(v___x_2361_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2476_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2369_; lean_object* v___x_2371_; 
v___x_2369_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 1, v___x_2369_);
v___x_2371_ = v___x_2367_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_mctx_2362_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_zetaDeltaFVarIds_2363_);
lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_postponed_2364_);
lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_diag_2365_);
v___x_2371_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v_env_2374_; lean_object* v_nextMacroScope_2375_; lean_object* v_ngen_2376_; lean_object* v_auxDeclNGen_2377_; lean_object* v_traceState_2378_; lean_object* v_messages_2379_; lean_object* v_infoState_2380_; lean_object* v_snapshotTasks_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2473_; 
v___x_2372_ = lean_st_ref_set(v_a_2310_, v___x_2371_);
v___x_2373_ = lean_st_ref_take(v_a_2312_);
v_env_2374_ = lean_ctor_get(v___x_2373_, 0);
v_nextMacroScope_2375_ = lean_ctor_get(v___x_2373_, 1);
v_ngen_2376_ = lean_ctor_get(v___x_2373_, 2);
v_auxDeclNGen_2377_ = lean_ctor_get(v___x_2373_, 3);
v_traceState_2378_ = lean_ctor_get(v___x_2373_, 4);
v_messages_2379_ = lean_ctor_get(v___x_2373_, 6);
v_infoState_2380_ = lean_ctor_get(v___x_2373_, 7);
v_snapshotTasks_2381_ = lean_ctor_get(v___x_2373_, 8);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2473_ == 0)
{
lean_object* v_unused_2474_; 
v_unused_2474_ = lean_ctor_get(v___x_2373_, 5);
lean_dec(v_unused_2474_);
v___x_2383_ = v___x_2373_;
v_isShared_2384_ = v_isSharedCheck_2473_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_snapshotTasks_2381_);
lean_inc(v_infoState_2380_);
lean_inc(v_messages_2379_);
lean_inc(v_traceState_2378_);
lean_inc(v_auxDeclNGen_2377_);
lean_inc(v_ngen_2376_);
lean_inc(v_nextMacroScope_2375_);
lean_inc(v_env_2374_);
lean_dec(v___x_2373_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2473_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___x_2387_; 
lean_inc(v_declName_2307_);
v___x_2385_ = l_Lean_markAuxRecursor(v_env_2374_, v_declName_2307_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 5, v___x_2357_);
lean_ctor_set(v___x_2383_, 0, v___x_2385_);
v___x_2387_ = v___x_2383_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2385_);
lean_ctor_set(v_reuseFailAlloc_2472_, 1, v_nextMacroScope_2375_);
lean_ctor_set(v_reuseFailAlloc_2472_, 2, v_ngen_2376_);
lean_ctor_set(v_reuseFailAlloc_2472_, 3, v_auxDeclNGen_2377_);
lean_ctor_set(v_reuseFailAlloc_2472_, 4, v_traceState_2378_);
lean_ctor_set(v_reuseFailAlloc_2472_, 5, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2472_, 6, v_messages_2379_);
lean_ctor_set(v_reuseFailAlloc_2472_, 7, v_infoState_2380_);
lean_ctor_set(v_reuseFailAlloc_2472_, 8, v_snapshotTasks_2381_);
v___x_2387_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v_mctx_2390_; lean_object* v_zetaDeltaFVarIds_2391_; lean_object* v_postponed_2392_; lean_object* v_diag_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2470_; 
v___x_2388_ = lean_st_ref_set(v_a_2312_, v___x_2387_);
v___x_2389_ = lean_st_ref_take(v_a_2310_);
v_mctx_2390_ = lean_ctor_get(v___x_2389_, 0);
v_zetaDeltaFVarIds_2391_ = lean_ctor_get(v___x_2389_, 2);
v_postponed_2392_ = lean_ctor_get(v___x_2389_, 3);
v_diag_2393_ = lean_ctor_get(v___x_2389_, 4);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v___x_2389_, 1);
lean_dec(v_unused_2471_);
v___x_2395_ = v___x_2389_;
v_isShared_2396_ = v_isSharedCheck_2470_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_diag_2393_);
lean_inc(v_postponed_2392_);
lean_inc(v_zetaDeltaFVarIds_2391_);
lean_inc(v_mctx_2390_);
lean_dec(v___x_2389_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2470_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 1, v___x_2369_);
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_mctx_2390_);
lean_ctor_set(v_reuseFailAlloc_2469_, 1, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2469_, 2, v_zetaDeltaFVarIds_2391_);
lean_ctor_set(v_reuseFailAlloc_2469_, 3, v_postponed_2392_);
lean_ctor_set(v_reuseFailAlloc_2469_, 4, v_diag_2393_);
v___x_2398_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v_env_2401_; lean_object* v_nextMacroScope_2402_; lean_object* v_ngen_2403_; lean_object* v_auxDeclNGen_2404_; lean_object* v_traceState_2405_; lean_object* v_messages_2406_; lean_object* v_infoState_2407_; lean_object* v_snapshotTasks_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2467_; 
v___x_2399_ = lean_st_ref_set(v_a_2310_, v___x_2398_);
v___x_2400_ = lean_st_ref_take(v_a_2312_);
v_env_2401_ = lean_ctor_get(v___x_2400_, 0);
v_nextMacroScope_2402_ = lean_ctor_get(v___x_2400_, 1);
v_ngen_2403_ = lean_ctor_get(v___x_2400_, 2);
v_auxDeclNGen_2404_ = lean_ctor_get(v___x_2400_, 3);
v_traceState_2405_ = lean_ctor_get(v___x_2400_, 4);
v_messages_2406_ = lean_ctor_get(v___x_2400_, 6);
v_infoState_2407_ = lean_ctor_get(v___x_2400_, 7);
v_snapshotTasks_2408_ = lean_ctor_get(v___x_2400_, 8);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; 
v_unused_2468_ = lean_ctor_get(v___x_2400_, 5);
lean_dec(v_unused_2468_);
v___x_2410_ = v___x_2400_;
v_isShared_2411_ = v_isSharedCheck_2467_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_snapshotTasks_2408_);
lean_inc(v_infoState_2407_);
lean_inc(v_messages_2406_);
lean_inc(v_traceState_2405_);
lean_inc(v_auxDeclNGen_2404_);
lean_inc(v_ngen_2403_);
lean_inc(v_nextMacroScope_2402_);
lean_inc(v_env_2401_);
lean_dec(v___x_2400_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2467_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
lean_inc(v_declName_2307_);
v___x_2412_ = l_Lean_Meta_addToCompletionBlackList(v_env_2401_, v_declName_2307_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 5, v___x_2357_);
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2414_ = v___x_2410_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_nextMacroScope_2402_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v_ngen_2403_);
lean_ctor_set(v_reuseFailAlloc_2466_, 3, v_auxDeclNGen_2404_);
lean_ctor_set(v_reuseFailAlloc_2466_, 4, v_traceState_2405_);
lean_ctor_set(v_reuseFailAlloc_2466_, 5, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2466_, 6, v_messages_2406_);
lean_ctor_set(v_reuseFailAlloc_2466_, 7, v_infoState_2407_);
lean_ctor_set(v_reuseFailAlloc_2466_, 8, v_snapshotTasks_2408_);
v___x_2414_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v_mctx_2417_; lean_object* v_zetaDeltaFVarIds_2418_; lean_object* v_postponed_2419_; lean_object* v_diag_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2464_; 
v___x_2415_ = lean_st_ref_set(v_a_2312_, v___x_2414_);
v___x_2416_ = lean_st_ref_take(v_a_2310_);
v_mctx_2417_ = lean_ctor_get(v___x_2416_, 0);
v_zetaDeltaFVarIds_2418_ = lean_ctor_get(v___x_2416_, 2);
v_postponed_2419_ = lean_ctor_get(v___x_2416_, 3);
v_diag_2420_ = lean_ctor_get(v___x_2416_, 4);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2416_);
if (v_isSharedCheck_2464_ == 0)
{
lean_object* v_unused_2465_; 
v_unused_2465_ = lean_ctor_get(v___x_2416_, 1);
lean_dec(v_unused_2465_);
v___x_2422_ = v___x_2416_;
v_isShared_2423_ = v_isSharedCheck_2464_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_diag_2420_);
lean_inc(v_postponed_2419_);
lean_inc(v_zetaDeltaFVarIds_2418_);
lean_inc(v_mctx_2417_);
lean_dec(v___x_2416_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2464_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___x_2369_);
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_mctx_2417_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2463_, 2, v_zetaDeltaFVarIds_2418_);
lean_ctor_set(v_reuseFailAlloc_2463_, 3, v_postponed_2419_);
lean_ctor_set(v_reuseFailAlloc_2463_, 4, v_diag_2420_);
v___x_2425_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v_env_2428_; lean_object* v_nextMacroScope_2429_; lean_object* v_ngen_2430_; lean_object* v_auxDeclNGen_2431_; lean_object* v_traceState_2432_; lean_object* v_messages_2433_; lean_object* v_infoState_2434_; lean_object* v_snapshotTasks_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2461_; 
v___x_2426_ = lean_st_ref_set(v_a_2310_, v___x_2425_);
v___x_2427_ = lean_st_ref_take(v_a_2312_);
v_env_2428_ = lean_ctor_get(v___x_2427_, 0);
v_nextMacroScope_2429_ = lean_ctor_get(v___x_2427_, 1);
v_ngen_2430_ = lean_ctor_get(v___x_2427_, 2);
v_auxDeclNGen_2431_ = lean_ctor_get(v___x_2427_, 3);
v_traceState_2432_ = lean_ctor_get(v___x_2427_, 4);
v_messages_2433_ = lean_ctor_get(v___x_2427_, 6);
v_infoState_2434_ = lean_ctor_get(v___x_2427_, 7);
v_snapshotTasks_2435_ = lean_ctor_get(v___x_2427_, 8);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v___x_2427_, 5);
lean_dec(v_unused_2462_);
v___x_2437_ = v___x_2427_;
v_isShared_2438_ = v_isSharedCheck_2461_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_snapshotTasks_2435_);
lean_inc(v_infoState_2434_);
lean_inc(v_messages_2433_);
lean_inc(v_traceState_2432_);
lean_inc(v_auxDeclNGen_2431_);
lean_inc(v_ngen_2430_);
lean_inc(v_nextMacroScope_2429_);
lean_inc(v_env_2428_);
lean_dec(v___x_2427_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2461_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_inc(v_declName_2307_);
v___x_2439_ = l_Lean_addProtected(v_env_2428_, v_declName_2307_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 5, v___x_2357_);
lean_ctor_set(v___x_2437_, 0, v___x_2439_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_nextMacroScope_2429_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_ngen_2430_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v_auxDeclNGen_2431_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v_traceState_2432_);
lean_ctor_set(v_reuseFailAlloc_2460_, 5, v___x_2357_);
lean_ctor_set(v_reuseFailAlloc_2460_, 6, v_messages_2433_);
lean_ctor_set(v_reuseFailAlloc_2460_, 7, v_infoState_2434_);
lean_ctor_set(v_reuseFailAlloc_2460_, 8, v_snapshotTasks_2435_);
v___x_2441_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_mctx_2444_; lean_object* v_zetaDeltaFVarIds_2445_; lean_object* v_postponed_2446_; lean_object* v_diag_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2458_; 
v___x_2442_ = lean_st_ref_set(v_a_2312_, v___x_2441_);
v___x_2443_ = lean_st_ref_take(v_a_2310_);
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
lean_ctor_set(v___x_2449_, 1, v___x_2369_);
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_mctx_2444_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_zetaDeltaFVarIds_2445_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_postponed_2446_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_diag_2447_);
v___x_2452_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = lean_st_ref_set(v_a_2310_, v___x_2452_);
v___x_2454_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2307_);
v___x_2455_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2454_, v_declName_2307_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v___x_2456_; 
lean_dec_ref_known(v___x_2455_, 1);
v___x_2456_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2307_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
return v___x_2456_;
}
else
{
lean_dec(v_declName_2307_);
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
lean_dec(v_declName_2307_);
return v___x_2343_;
}
}
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_levelParams_2324_);
lean_dec(v_declName_2307_);
v_a_2483_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2337_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2337_);
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
lean_dec(v___x_2327_);
lean_dec_ref(v_type_2325_);
lean_dec(v_levelParams_2324_);
lean_dec(v_name_2323_);
lean_dec(v___x_2320_);
lean_del_object(v___x_2318_);
lean_dec_ref(v_val_2316_);
lean_dec(v_indName_2308_);
lean_dec(v_declName_2307_);
v___x_2492_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2493_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2492_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
return v___x_2493_;
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v___x_2320_);
lean_del_object(v___x_2318_);
lean_dec_ref(v_val_2316_);
lean_dec(v_indName_2308_);
lean_dec(v_declName_2307_);
v_a_2494_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2321_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2321_);
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
lean_dec(v_a_2315_);
lean_dec(v_indName_2308_);
lean_dec(v_declName_2307_);
v___x_2503_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2504_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2503_, v_a_2309_, v_a_2310_, v_a_2311_, v_a_2312_);
return v___x_2504_;
}
}
else
{
lean_object* v_a_2505_; lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
lean_dec(v_indName_2308_);
lean_dec(v_declName_2307_);
v_a_2505_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2512_ == 0)
{
v___x_2507_ = v___x_2314_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_inc(v_a_2505_);
lean_dec(v___x_2314_);
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
v___x_2794_ = lean_st_ref_set(v___y_2775_, v___x_2793_);
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
lean_object* v___x_2822_; lean_object* v_env_2823_; lean_object* v_nextMacroScope_2824_; lean_object* v_ngen_2825_; lean_object* v_auxDeclNGen_2826_; lean_object* v_traceState_2827_; lean_object* v_messages_2828_; lean_object* v_infoState_2829_; lean_object* v_snapshotTasks_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2857_; 
v___x_2822_ = lean_st_ref_take(v___y_2820_);
v_env_2823_ = lean_ctor_get(v___x_2822_, 0);
v_nextMacroScope_2824_ = lean_ctor_get(v___x_2822_, 1);
v_ngen_2825_ = lean_ctor_get(v___x_2822_, 2);
v_auxDeclNGen_2826_ = lean_ctor_get(v___x_2822_, 3);
v_traceState_2827_ = lean_ctor_get(v___x_2822_, 4);
v_messages_2828_ = lean_ctor_get(v___x_2822_, 6);
v_infoState_2829_ = lean_ctor_get(v___x_2822_, 7);
v_snapshotTasks_2830_ = lean_ctor_get(v___x_2822_, 8);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v___x_2822_, 5);
lean_dec(v_unused_2858_);
v___x_2832_ = v___x_2822_;
v_isShared_2833_ = v_isSharedCheck_2857_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_snapshotTasks_2830_);
lean_inc(v_infoState_2829_);
lean_inc(v_messages_2828_);
lean_inc(v_traceState_2827_);
lean_inc(v_auxDeclNGen_2826_);
lean_inc(v_ngen_2825_);
lean_inc(v_nextMacroScope_2824_);
lean_inc(v_env_2823_);
lean_dec(v___x_2822_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2857_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v___x_2834_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2823_, v_matcherName_2817_, v_info_2818_);
v___x_2835_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 5, v___x_2835_);
lean_ctor_set(v___x_2832_, 0, v___x_2834_);
v___x_2837_ = v___x_2832_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_nextMacroScope_2824_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_ngen_2825_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_auxDeclNGen_2826_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v_traceState_2827_);
lean_ctor_set(v_reuseFailAlloc_2856_, 5, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2856_, 6, v_messages_2828_);
lean_ctor_set(v_reuseFailAlloc_2856_, 7, v_infoState_2829_);
lean_ctor_set(v_reuseFailAlloc_2856_, 8, v_snapshotTasks_2830_);
v___x_2837_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v_mctx_2840_; lean_object* v_zetaDeltaFVarIds_2841_; lean_object* v_postponed_2842_; lean_object* v_diag_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2854_; 
v___x_2838_ = lean_st_ref_set(v___y_2820_, v___x_2837_);
v___x_2839_ = lean_st_ref_take(v___y_2819_);
v_mctx_2840_ = lean_ctor_get(v___x_2839_, 0);
v_zetaDeltaFVarIds_2841_ = lean_ctor_get(v___x_2839_, 2);
v_postponed_2842_ = lean_ctor_get(v___x_2839_, 3);
v_diag_2843_ = lean_ctor_get(v___x_2839_, 4);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; 
v_unused_2855_ = lean_ctor_get(v___x_2839_, 1);
lean_dec(v_unused_2855_);
v___x_2845_ = v___x_2839_;
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_diag_2843_);
lean_inc(v_postponed_2842_);
lean_inc(v_zetaDeltaFVarIds_2841_);
lean_inc(v_mctx_2840_);
lean_dec(v___x_2839_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2847_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v___x_2847_);
v___x_2849_ = v___x_2845_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_mctx_2840_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_zetaDeltaFVarIds_2841_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_postponed_2842_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_diag_2843_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = lean_st_ref_set(v___y_2819_, v___x_2849_);
v___x_2851_ = lean_box(0);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2859_, lean_object* v_info_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2859_, v_info_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec(v___y_2861_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2865_, lean_object* v_info_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2865_, v_info_2866_, v___y_2868_, v___y_2870_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2873_, lean_object* v_info_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2873_, v_info_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2881_, lean_object* v___x_2882_, lean_object* v_newEqs1_2883_, uint8_t v___x_2884_, uint8_t v___x_2885_, uint8_t v___x_2886_, lean_object* v_ism1_x27_2887_, lean_object* v_ism2_x27_2888_, lean_object* v_newRefls1_2889_, lean_object* v_newEqs2_2890_, lean_object* v_newRefls2_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2897_ = l_Lean_mkAppN(v_motive_2881_, v___x_2882_);
v___x_2898_ = l_Array_append___redArg(v_newEqs1_2883_, v_newEqs2_2890_);
v___x_2899_ = l_Lean_Meta_mkForallFVars(v___x_2898_, v___x_2897_, v___x_2884_, v___x_2885_, v___x_2885_, v___x_2886_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec_ref(v___x_2898_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 1);
v___x_2901_ = l_Array_append___redArg(v_ism1_x27_2887_, v_ism2_x27_2888_);
v___x_2902_ = l_Lean_Meta_mkLambdaFVars(v___x_2901_, v_a_2900_, v___x_2884_, v___x_2885_, v___x_2884_, v___x_2885_, v___x_2886_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
lean_dec_ref(v___x_2901_);
if (lean_obj_tag(v___x_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2912_; 
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2912_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2912_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2910_; 
v___x_2907_ = l_Array_append___redArg(v_newRefls1_2889_, v_newRefls2_2891_);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_a_2903_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 0, v___x_2908_);
v___x_2910_ = v___x_2905_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v_newRefls1_2889_);
v_a_2913_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2902_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2902_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v_newRefls1_2889_);
lean_dec_ref(v_ism1_x27_2887_);
v_a_2921_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2899_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2899_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2929_, lean_object* v___x_2930_, lean_object* v_newEqs1_2931_, lean_object* v___x_2932_, lean_object* v___x_2933_, lean_object* v___x_2934_, lean_object* v_ism1_x27_2935_, lean_object* v_ism2_x27_2936_, lean_object* v_newRefls1_2937_, lean_object* v_newEqs2_2938_, lean_object* v_newRefls2_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
uint8_t v___x_15166__boxed_2945_; uint8_t v___x_15167__boxed_2946_; uint8_t v___x_15168__boxed_2947_; lean_object* v_res_2948_; 
v___x_15166__boxed_2945_ = lean_unbox(v___x_2932_);
v___x_15167__boxed_2946_ = lean_unbox(v___x_2933_);
v___x_15168__boxed_2947_ = lean_unbox(v___x_2934_);
v_res_2948_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2929_, v___x_2930_, v_newEqs1_2931_, v___x_15166__boxed_2945_, v___x_15167__boxed_2946_, v___x_15168__boxed_2947_, v_ism1_x27_2935_, v_ism2_x27_2936_, v_newRefls1_2937_, v_newEqs2_2938_, v_newRefls2_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
lean_dec_ref(v_newRefls2_2939_);
lean_dec_ref(v_newEqs2_2938_);
lean_dec_ref(v_ism2_x27_2936_);
lean_dec_ref(v___x_2930_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2949_, lean_object* v___x_2950_, uint8_t v___x_2951_, uint8_t v___x_2952_, uint8_t v___x_2953_, lean_object* v_ism1_x27_2954_, lean_object* v_ism2_x27_2955_, lean_object* v_is_2956_, lean_object* v___x_2957_, lean_object* v_newEqs1_2958_, lean_object* v_newRefls1_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___f_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2965_ = lean_box(v___x_2951_);
v___x_2966_ = lean_box(v___x_2952_);
v___x_2967_ = lean_box(v___x_2953_);
lean_inc_ref(v_ism2_x27_2955_);
v___f_2968_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2968_, 0, v_motive_2949_);
lean_closure_set(v___f_2968_, 1, v___x_2950_);
lean_closure_set(v___f_2968_, 2, v_newEqs1_2958_);
lean_closure_set(v___f_2968_, 3, v___x_2965_);
lean_closure_set(v___f_2968_, 4, v___x_2966_);
lean_closure_set(v___f_2968_, 5, v___x_2967_);
lean_closure_set(v___f_2968_, 6, v_ism1_x27_2954_);
lean_closure_set(v___f_2968_, 7, v_ism2_x27_2955_);
lean_closure_set(v___f_2968_, 8, v_newRefls1_2959_);
v___x_2969_ = lean_array_push(v_is_2956_, v___x_2957_);
v___x_2970_ = l_Lean_Meta_withNewEqs___redArg(v___x_2969_, v_ism2_x27_2955_, v___f_2968_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2971_, lean_object* v___x_2972_, lean_object* v___x_2973_, lean_object* v___x_2974_, lean_object* v___x_2975_, lean_object* v_ism1_x27_2976_, lean_object* v_ism2_x27_2977_, lean_object* v_is_2978_, lean_object* v___x_2979_, lean_object* v_newEqs1_2980_, lean_object* v_newRefls1_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
uint8_t v___x_15257__boxed_2987_; uint8_t v___x_15258__boxed_2988_; uint8_t v___x_15259__boxed_2989_; lean_object* v_res_2990_; 
v___x_15257__boxed_2987_ = lean_unbox(v___x_2973_);
v___x_15258__boxed_2988_ = lean_unbox(v___x_2974_);
v___x_15259__boxed_2989_ = lean_unbox(v___x_2975_);
v_res_2990_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2971_, v___x_2972_, v___x_15257__boxed_2987_, v___x_15258__boxed_2988_, v___x_15259__boxed_2989_, v_ism1_x27_2976_, v_ism2_x27_2977_, v_is_2978_, v___x_2979_, v_newEqs1_2980_, v_newRefls1_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_2991_, uint8_t v___x_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; 
v___x_2998_ = l_Lean_addDecl(v___x_2991_, v___x_2992_, v___y_2995_, v___y_2996_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_2999_, lean_object* v___x_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
uint8_t v___x_15299__boxed_3006_; lean_object* v_res_3007_; 
v___x_15299__boxed_3006_ = lean_unbox(v___x_3000_);
v_res_3007_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_2999_, v___x_15299__boxed_3006_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
lean_dec(v___y_3002_);
lean_dec_ref(v___y_3001_);
return v_res_3007_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3010_ = l_Lean_stringToMessageData(v___x_3009_);
return v___x_3010_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3013_ = l_Lean_stringToMessageData(v___x_3012_);
return v___x_3013_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3019_ = lean_box(0);
v___x_3020_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3021_ = l_Lean_mkConst(v___x_3020_, v___x_3019_);
return v___x_3021_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3023_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3024_ = l_Lean_stringToMessageData(v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3025_, lean_object* v_a_3026_, lean_object* v___x_3027_, lean_object* v_zs1_3028_, lean_object* v_snd_3029_, uint8_t v___x_3030_, uint8_t v___x_3031_, uint8_t v___x_3032_, lean_object* v_alts_3033_, lean_object* v_zs2_3034_, lean_object* v___ctorRet2_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3041_ = lean_array_get_borrowed(v___x_3025_, v_a_3026_, v___x_3027_);
lean_inc_ref(v_zs1_3028_);
v___x_3042_ = l_Array_append___redArg(v_zs1_3028_, v_zs2_3034_);
lean_inc(v___x_3041_);
v___x_3043_ = l_Lean_Meta_instantiateForall(v___x_3041_, v___x_3042_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
lean_inc(v_a_3044_);
lean_dec_ref_known(v___x_3043_, 1);
v___x_3045_ = lean_box(0);
v___x_3046_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3044_, v___x_3045_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v_a_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v_a_3047_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_a_3047_);
lean_dec_ref_known(v___x_3046_, 1);
v___x_3048_ = l_Lean_Expr_mvarId_x21(v_a_3047_);
v___x_3049_ = lean_array_get_size(v_snd_3029_);
v___x_3050_ = lean_box(0);
v___x_3051_ = lean_box(0);
lean_inc_ref(v___y_3038_);
v___x_3052_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3049_, v___x_3048_, v___x_3050_, v___x_3051_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
if (lean_obj_tag(v_a_3053_) == 1)
{
lean_object* v_val_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3101_; 
v_val_3054_ = lean_ctor_get(v_a_3053_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_a_3053_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3056_ = v_a_3053_;
v_isShared_3057_ = v_isSharedCheck_3101_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_val_3054_);
lean_dec(v_a_3053_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3101_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v_fst_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3099_; 
v_fst_3058_ = lean_ctor_get(v_val_3054_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v_val_3054_);
if (v_isSharedCheck_3099_ == 0)
{
lean_object* v_unused_3100_; 
v_unused_3100_ = lean_ctor_get(v_val_3054_, 1);
lean_dec(v_unused_3100_);
v___x_3060_ = v_val_3054_;
v_isShared_3061_ = v_isSharedCheck_3099_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_fst_3058_);
lean_dec(v_val_3054_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3099_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___y_3063_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; uint8_t v___x_3094_; 
v___x_3091_ = lean_array_get_borrowed(v___x_3025_, v_alts_3033_, v___x_3027_);
v___x_3092_ = lean_array_get_size(v_zs1_3028_);
lean_dec_ref(v_zs1_3028_);
v___x_3093_ = lean_unsigned_to_nat(0u);
v___x_3094_ = lean_nat_dec_eq(v___x_3092_, v___x_3093_);
if (v___x_3094_ == 0)
{
lean_inc(v___x_3091_);
v___y_3063_ = v___x_3091_;
goto v___jp_3062_;
}
else
{
lean_object* v___x_3095_; uint8_t v___x_3096_; 
v___x_3095_ = lean_array_get_size(v_zs2_3034_);
v___x_3096_ = lean_nat_dec_eq(v___x_3095_, v___x_3093_);
if (v___x_3096_ == 0)
{
lean_inc(v___x_3091_);
v___y_3063_ = v___x_3091_;
goto v___jp_3062_;
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3091_);
v___x_3098_ = l_Lean_Expr_app___override(v___x_3091_, v___x_3097_);
v___y_3063_ = v___x_3098_;
goto v___jp_3062_;
}
}
v___jp_3062_:
{
uint8_t v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3064_ = 0;
v___x_3065_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3065_, 0, v___x_3064_);
lean_ctor_set_uint8(v___x_3065_, 1, v___x_3030_);
lean_ctor_set_uint8(v___x_3065_, 2, v___x_3031_);
lean_ctor_set_uint8(v___x_3065_, 3, v___x_3030_);
lean_inc_ref(v___y_3063_);
lean_inc(v_fst_3058_);
v___x_3066_ = l_Lean_MVarId_apply(v_fst_3058_, v___y_3063_, v___x_3065_, v___x_3051_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3066_, 1);
if (lean_obj_tag(v_a_3067_) == 0)
{
lean_object* v___x_3068_; 
lean_dec_ref(v___y_3063_);
lean_del_object(v___x_3060_);
lean_dec(v_fst_3058_);
lean_del_object(v___x_3056_);
v___x_3068_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3047_, v___y_3037_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; lean_object* v___x_3070_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v___x_3068_, 1);
v___x_3070_ = l_Lean_Meta_mkLambdaFVars(v___x_3042_, v_a_3069_, v___x_3031_, v___x_3030_, v___x_3031_, v___x_3030_, v___x_3032_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
lean_dec_ref(v___x_3042_);
return v___x_3070_;
}
else
{
lean_dec_ref(v___x_3042_);
return v___x_3068_;
}
}
else
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3074_; 
lean_dec(v_a_3067_);
lean_dec(v_a_3047_);
lean_dec_ref(v___x_3042_);
v___x_3071_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3072_ = l_Lean_MessageData_ofExpr(v___y_3063_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set_tag(v___x_3060_, 7);
lean_ctor_set(v___x_3060_, 1, v___x_3072_);
lean_ctor_set(v___x_3060_, 0, v___x_3071_);
v___x_3074_ = v___x_3060_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3082_, 1, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
v___x_3075_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3074_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v_fst_3058_);
v___x_3078_ = v___x_3056_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_fst_3058_);
v___x_3078_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3079_, 0, v___x_3076_);
lean_ctor_set(v___x_3079_, 1, v___x_3078_);
v___x_3080_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3079_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
return v___x_3080_;
}
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3090_; 
lean_dec_ref(v___y_3063_);
lean_del_object(v___x_3060_);
lean_dec(v_fst_3058_);
lean_del_object(v___x_3056_);
lean_dec(v_a_3047_);
lean_dec_ref(v___x_3042_);
v_a_3083_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3085_ = v___x_3066_;
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3066_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3090_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3083_);
v___x_3088_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
return v___x_3088_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_dec(v_a_3053_);
lean_dec(v_a_3047_);
lean_dec_ref(v___x_3042_);
lean_dec_ref(v_zs1_3028_);
v___x_3102_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3103_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3102_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
return v___x_3103_;
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_a_3047_);
lean_dec_ref(v___x_3042_);
lean_dec_ref(v_zs1_3028_);
v_a_3104_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3052_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3052_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_dec_ref(v___x_3042_);
lean_dec_ref(v_zs1_3028_);
return v___x_3046_;
}
}
else
{
lean_dec_ref(v___x_3042_);
lean_dec_ref(v_zs1_3028_);
return v___x_3043_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3112_, lean_object* v_a_3113_, lean_object* v___x_3114_, lean_object* v_zs1_3115_, lean_object* v_snd_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v___x_3119_, lean_object* v_alts_3120_, lean_object* v_zs2_3121_, lean_object* v___ctorRet2_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
uint8_t v___x_15359__boxed_3128_; uint8_t v___x_15360__boxed_3129_; uint8_t v___x_15361__boxed_3130_; lean_object* v_res_3131_; 
v___x_15359__boxed_3128_ = lean_unbox(v___x_3117_);
v___x_15360__boxed_3129_ = lean_unbox(v___x_3118_);
v___x_15361__boxed_3130_ = lean_unbox(v___x_3119_);
v_res_3131_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3112_, v_a_3113_, v___x_3114_, v_zs1_3115_, v_snd_3116_, v___x_15359__boxed_3128_, v___x_15360__boxed_3129_, v___x_15361__boxed_3130_, v_alts_3120_, v_zs2_3121_, v___ctorRet2_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec_ref(v___ctorRet2_3122_);
lean_dec_ref(v_zs2_3121_);
lean_dec_ref(v_alts_3120_);
lean_dec_ref(v_snd_3116_);
lean_dec(v___x_3114_);
lean_dec_ref(v_a_3113_);
lean_dec_ref(v___x_3112_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3132_, lean_object* v_a_3133_, lean_object* v___x_3134_, lean_object* v_snd_3135_, uint8_t v___x_3136_, uint8_t v___x_3137_, uint8_t v___x_3138_, lean_object* v_alts_3139_, lean_object* v_a_3140_, lean_object* v_zs1_3141_, lean_object* v___ctorRet1_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___f_3151_; lean_object* v___x_3152_; 
v___x_3148_ = lean_box(v___x_3136_);
v___x_3149_ = lean_box(v___x_3137_);
v___x_3150_ = lean_box(v___x_3138_);
v___f_3151_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3151_, 0, v___x_3132_);
lean_closure_set(v___f_3151_, 1, v_a_3133_);
lean_closure_set(v___f_3151_, 2, v___x_3134_);
lean_closure_set(v___f_3151_, 3, v_zs1_3141_);
lean_closure_set(v___f_3151_, 4, v_snd_3135_);
lean_closure_set(v___f_3151_, 5, v___x_3148_);
lean_closure_set(v___f_3151_, 6, v___x_3149_);
lean_closure_set(v___f_3151_, 7, v___x_3150_);
lean_closure_set(v___f_3151_, 8, v_alts_3139_);
v___x_3152_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3140_, v___f_3151_, v___x_3137_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3153_, lean_object* v_a_3154_, lean_object* v___x_3155_, lean_object* v_snd_3156_, lean_object* v___x_3157_, lean_object* v___x_3158_, lean_object* v___x_3159_, lean_object* v_alts_3160_, lean_object* v_a_3161_, lean_object* v_zs1_3162_, lean_object* v___ctorRet1_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
uint8_t v___x_15558__boxed_3169_; uint8_t v___x_15559__boxed_3170_; uint8_t v___x_15560__boxed_3171_; lean_object* v_res_3172_; 
v___x_15558__boxed_3169_ = lean_unbox(v___x_3157_);
v___x_15559__boxed_3170_ = lean_unbox(v___x_3158_);
v___x_15560__boxed_3171_ = lean_unbox(v___x_3159_);
v_res_3172_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3153_, v_a_3154_, v___x_3155_, v_snd_3156_, v___x_15558__boxed_3169_, v___x_15559__boxed_3170_, v___x_15560__boxed_3171_, v_alts_3160_, v_a_3161_, v_zs1_3162_, v___ctorRet1_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec_ref(v___ctorRet1_3163_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3173_, lean_object* v_params_3174_, lean_object* v_a_3175_, lean_object* v_snd_3176_, lean_object* v_alts_3177_, size_t v_sz_3178_, size_t v_i_3179_, lean_object* v_bs_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_usize_dec_lt(v_i_3179_, v_sz_3178_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; 
lean_dec_ref(v_alts_3177_);
lean_dec_ref(v_snd_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_tail_3173_);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v_bs_3180_);
return v___x_3187_;
}
else
{
lean_object* v_v_3188_; lean_object* v___x_3189_; lean_object* v_bs_x27_3190_; lean_object* v___y_3192_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_v_3188_ = lean_array_uget(v_bs_3180_, v_i_3179_);
v___x_3189_ = lean_unsigned_to_nat(0u);
v_bs_x27_3190_ = lean_array_uset(v_bs_3180_, v_i_3179_, v___x_3189_);
lean_inc(v_tail_3173_);
v___x_3206_ = l_Lean_mkConst(v_v_3188_, v_tail_3173_);
v___x_3207_ = l_Lean_mkAppN(v___x_3206_, v_params_3174_);
lean_inc(v___y_3184_);
lean_inc_ref(v___y_3183_);
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
v___x_3208_ = lean_infer_type(v___x_3207_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; uint8_t v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___f_3217_; lean_object* v___x_3218_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc_n(v_a_3209_, 2);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3210_ = l_Lean_instInhabitedExpr;
v___x_3211_ = 0;
v___x_3212_ = 1;
v___x_3213_ = lean_usize_to_nat(v_i_3179_);
v___x_3214_ = lean_box(v___x_3186_);
v___x_3215_ = lean_box(v___x_3211_);
v___x_3216_ = lean_box(v___x_3212_);
lean_inc_ref(v_alts_3177_);
lean_inc_ref(v_snd_3176_);
lean_inc_ref(v_a_3175_);
v___f_3217_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3217_, 0, v___x_3210_);
lean_closure_set(v___f_3217_, 1, v_a_3175_);
lean_closure_set(v___f_3217_, 2, v___x_3213_);
lean_closure_set(v___f_3217_, 3, v_snd_3176_);
lean_closure_set(v___f_3217_, 4, v___x_3214_);
lean_closure_set(v___f_3217_, 5, v___x_3215_);
lean_closure_set(v___f_3217_, 6, v___x_3216_);
lean_closure_set(v___f_3217_, 7, v_alts_3177_);
lean_closure_set(v___f_3217_, 8, v_a_3209_);
v___x_3218_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3209_, v___f_3217_, v___x_3211_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
v___y_3192_ = v___x_3218_;
goto v___jp_3191_;
}
else
{
v___y_3192_ = v___x_3208_;
goto v___jp_3191_;
}
v___jp_3191_:
{
if (lean_obj_tag(v___y_3192_) == 0)
{
lean_object* v_a_3193_; size_t v___x_3194_; size_t v___x_3195_; lean_object* v___x_3196_; 
v_a_3193_ = lean_ctor_get(v___y_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___y_3192_, 1);
v___x_3194_ = ((size_t)1ULL);
v___x_3195_ = lean_usize_add(v_i_3179_, v___x_3194_);
v___x_3196_ = lean_array_uset(v_bs_x27_3190_, v_i_3179_, v_a_3193_);
v_i_3179_ = v___x_3195_;
v_bs_3180_ = v___x_3196_;
goto _start;
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec_ref(v_bs_x27_3190_);
lean_dec_ref(v_alts_3177_);
lean_dec_ref(v_snd_3176_);
lean_dec_ref(v_a_3175_);
lean_dec(v_tail_3173_);
v_a_3198_ = lean_ctor_get(v___y_3192_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___y_3192_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___y_3192_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___y_3192_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3219_, lean_object* v_params_3220_, lean_object* v_a_3221_, lean_object* v_snd_3222_, lean_object* v_alts_3223_, lean_object* v_sz_3224_, lean_object* v_i_3225_, lean_object* v_bs_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
size_t v_sz_boxed_3232_; size_t v_i_boxed_3233_; lean_object* v_res_3234_; 
v_sz_boxed_3232_ = lean_unbox_usize(v_sz_3224_);
lean_dec(v_sz_3224_);
v_i_boxed_3233_ = lean_unbox_usize(v_i_3225_);
lean_dec(v_i_3225_);
v_res_3234_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3219_, v_params_3220_, v_a_3221_, v_snd_3222_, v_alts_3223_, v_sz_boxed_3232_, v_i_boxed_3233_, v_bs_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec_ref(v_params_3220_);
return v_res_3234_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = lean_box(0);
v___x_3236_ = lean_unsigned_to_nat(16u);
v___x_3237_ = lean_mk_array(v___x_3236_, v___x_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3238_, lean_object* v___x_3239_, uint8_t v___x_3240_, uint8_t v___x_3241_, uint8_t v___x_3242_, lean_object* v_ism1_x27_3243_, lean_object* v_is_3244_, lean_object* v___x_3245_, lean_object* v___x_3246_, lean_object* v___x_3247_, lean_object* v___x_3248_, lean_object* v_params_3249_, lean_object* v___x_3250_, lean_object* v___x_3251_, lean_object* v_heq_3252_, lean_object* v_val_3253_, lean_object* v_tail_3254_, lean_object* v_alts_3255_, size_t v_sz_3256_, size_t v___x_3257_, lean_object* v___x_3258_, lean_object* v___x_3259_, lean_object* v_declName_3260_, lean_object* v_levelParams_3261_, lean_object* v_numIndices_3262_, lean_object* v___x_3263_, lean_object* v___x_3264_, lean_object* v_numParams_3265_, lean_object* v_snd_3266_, lean_object* v_ism2_x27_3267_, lean_object* v_x_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___f_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3274_ = lean_box(v___x_3240_);
v___x_3275_ = lean_box(v___x_3241_);
v___x_3276_ = lean_box(v___x_3242_);
lean_inc_ref(v___x_3245_);
lean_inc_ref_n(v_is_3244_, 2);
lean_inc_ref(v_ism1_x27_3243_);
lean_inc_ref(v_motive_3238_);
v___f_3277_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3277_, 0, v_motive_3238_);
lean_closure_set(v___f_3277_, 1, v___x_3239_);
lean_closure_set(v___f_3277_, 2, v___x_3274_);
lean_closure_set(v___f_3277_, 3, v___x_3275_);
lean_closure_set(v___f_3277_, 4, v___x_3276_);
lean_closure_set(v___f_3277_, 5, v_ism1_x27_3243_);
lean_closure_set(v___f_3277_, 6, v_ism2_x27_3267_);
lean_closure_set(v___f_3277_, 7, v_is_3244_);
lean_closure_set(v___f_3277_, 8, v___x_3245_);
lean_inc_ref(v___x_3246_);
v___x_3278_ = lean_array_push(v_is_3244_, v___x_3246_);
v___x_3279_ = l_Lean_Meta_withNewEqs___redArg(v___x_3278_, v_ism1_x27_3243_, v___f_3277_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v_a_3280_; lean_object* v_fst_3281_; lean_object* v_snd_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3383_; 
v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3279_, 1);
v_fst_3281_ = lean_ctor_get(v_a_3280_, 0);
v_snd_3282_ = lean_ctor_get(v_a_3280_, 1);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_a_3280_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3284_ = v_a_3280_;
v_isShared_3285_ = v_isSharedCheck_3383_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_snd_3282_);
lean_inc(v_fst_3281_);
lean_dec(v_a_3280_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3383_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; 
v___x_3286_ = l_Lean_mkConst(v___x_3247_, v___x_3248_);
v___x_3287_ = l_Lean_mkAppN(v___x_3286_, v_params_3249_);
v___x_3288_ = l_Lean_Expr_app___override(v___x_3287_, v_fst_3281_);
lean_inc_ref(v_is_3244_);
v___x_3289_ = l_Array_append___redArg(v_is_3244_, v___x_3250_);
v___x_3290_ = l_Array_append___redArg(v___x_3289_, v_is_3244_);
v___x_3291_ = l_Array_append___redArg(v___x_3290_, v___x_3251_);
v___x_3292_ = l_Lean_mkAppN(v___x_3288_, v___x_3291_);
lean_dec_ref(v___x_3291_);
lean_inc_ref(v_heq_3252_);
v___x_3293_ = l_Lean_Expr_app___override(v___x_3292_, v_heq_3252_);
v___x_3294_ = l_Lean_InductiveVal_numCtors(v_val_3253_);
lean_inc_ref(v___x_3293_);
v___x_3295_ = l_Lean_Meta_inferArgumentTypesN(v___x_3294_, v___x_3293_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; lean_object* v___x_3297_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3296_);
lean_dec_ref_known(v___x_3295_, 1);
lean_inc_ref(v_alts_3255_);
lean_inc(v_snd_3282_);
v___x_3297_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3254_, v_params_3249_, v_a_3296_, v_snd_3282_, v_alts_3255_, v_sz_3256_, v___x_3257_, v___x_3258_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v___x_3299_ = l_Lean_mkAppN(v___x_3293_, v_a_3298_);
lean_dec(v_a_3298_);
v___x_3300_ = l_Lean_mkAppN(v___x_3299_, v_snd_3282_);
lean_dec(v_snd_3282_);
lean_inc_ref(v___x_3259_);
v___x_3301_ = lean_array_push(v___x_3259_, v_motive_3238_);
v___x_3302_ = l_Array_append___redArg(v_params_3249_, v___x_3301_);
lean_dec_ref(v___x_3301_);
v___x_3303_ = l_Array_append___redArg(v___x_3302_, v_is_3244_);
lean_dec_ref(v_is_3244_);
v___x_3304_ = lean_unsigned_to_nat(2u);
v___x_3305_ = lean_mk_empty_array_with_capacity(v___x_3304_);
v___x_3306_ = lean_array_push(v___x_3305_, v___x_3246_);
v___x_3307_ = lean_array_push(v___x_3306_, v___x_3245_);
v___x_3308_ = l_Array_append___redArg(v___x_3303_, v___x_3307_);
lean_dec_ref(v___x_3307_);
v___x_3309_ = lean_array_push(v___x_3259_, v_heq_3252_);
v___x_3310_ = l_Array_append___redArg(v___x_3308_, v___x_3309_);
lean_dec_ref(v___x_3309_);
v___x_3311_ = l_Array_append___redArg(v___x_3310_, v_alts_3255_);
lean_dec_ref(v_alts_3255_);
v___x_3312_ = l_Lean_Meta_mkLambdaFVars(v___x_3311_, v___x_3300_, v___x_3240_, v___x_3241_, v___x_3240_, v___x_3241_, v___x_3242_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec_ref(v___x_3311_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v_a_3313_; lean_object* v___x_3314_; 
v_a_3313_ = lean_ctor_get(v___x_3312_, 0);
lean_inc_n(v_a_3313_, 2);
lean_dec_ref_known(v___x_3312_, 1);
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3271_);
lean_inc(v___y_3270_);
lean_inc_ref(v___y_3269_);
v___x_3314_ = lean_infer_type(v_a_3313_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3350_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_a_3315_);
lean_dec_ref_known(v___x_3314_, 1);
v___x_3316_ = lean_box(1);
lean_inc(v_declName_3260_);
v___x_3317_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3260_, v_levelParams_3261_, v_a_3315_, v_a_3313_, v___x_3316_, v___y_3272_);
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3320_ = v___x_3317_;
v_isShared_3321_ = v_isSharedCheck_3350_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3350_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
lean_ctor_set_tag(v___x_3320_, 1);
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
lean_object* v___x_3324_; lean_object* v___f_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3324_ = lean_box(v___x_3240_);
lean_inc_ref(v___x_3323_);
v___f_3325_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3325_, 0, v___x_3323_);
lean_closure_set(v___f_3325_, 1, v___x_3324_);
v___x_3326_ = lean_nat_add(v_numIndices_3262_, v___x_3263_);
lean_inc(v___x_3264_);
v___x_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3264_);
v___x_3328_ = lean_box(0);
v___x_3329_ = lean_mk_empty_array_with_capacity(v___x_3263_);
v___x_3330_ = lean_array_push(v___x_3329_, v___x_3328_);
v___x_3331_ = lean_array_push(v___x_3330_, v___x_3328_);
v___x_3332_ = lean_array_push(v___x_3331_, v___x_3328_);
v___x_3333_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v___x_3333_);
lean_ctor_set(v___x_3284_, 0, v___x_3264_);
v___x_3335_ = v___x_3284_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v___x_3264_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3336_; uint8_t v___y_3338_; uint8_t v___x_3347_; 
v___x_3336_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3336_, 0, v_numParams_3265_);
lean_ctor_set(v___x_3336_, 1, v___x_3326_);
lean_ctor_set(v___x_3336_, 2, v_snd_3266_);
lean_ctor_set(v___x_3336_, 3, v___x_3327_);
lean_ctor_set(v___x_3336_, 4, v___x_3332_);
lean_ctor_set(v___x_3336_, 5, v___x_3335_);
v___x_3347_ = l_Lean_isPrivateName(v_declName_3260_);
if (v___x_3347_ == 0)
{
v___y_3338_ = v___x_3241_;
goto v___jp_3337_;
}
else
{
v___y_3338_ = v___x_3240_;
goto v___jp_3337_;
}
v___jp_3337_:
{
lean_object* v___x_3339_; 
v___x_3339_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3325_, v___y_3338_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3339_) == 0)
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_dec_ref_known(v___x_3339_, 1);
v___x_3340_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3260_);
v___x_3341_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3340_, v_declName_3260_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v___x_3342_; uint8_t v___x_3343_; lean_object* v___x_3344_; 
lean_dec_ref_known(v___x_3341_, 1);
lean_inc_n(v_declName_3260_, 2);
v___x_3342_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3260_, v___x_3336_, v___y_3270_, v___y_3272_);
lean_dec_ref(v___x_3342_);
v___x_3343_ = 0;
v___x_3344_ = l_Lean_Meta_setInlineAttribute(v_declName_3260_, v___x_3343_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3345_; 
lean_dec_ref_known(v___x_3344_, 1);
v___x_3345_ = l_Lean_enableRealizationsForConst(v_declName_3260_, v___y_3271_, v___y_3272_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v___x_3346_; 
lean_dec_ref_known(v___x_3345_, 1);
v___x_3346_ = l_Lean_compileDecl(v___x_3323_, v___x_3241_, v___y_3271_, v___y_3272_);
return v___x_3346_;
}
else
{
lean_dec_ref(v___x_3323_);
return v___x_3345_;
}
}
else
{
lean_dec_ref(v___x_3323_);
lean_dec(v_declName_3260_);
return v___x_3344_;
}
}
else
{
lean_dec_ref_known(v___x_3336_, 6);
lean_dec_ref(v___x_3323_);
lean_dec(v_declName_3260_);
return v___x_3341_;
}
}
else
{
lean_dec_ref_known(v___x_3336_, 6);
lean_dec_ref(v___x_3323_);
lean_dec(v_declName_3260_);
return v___x_3339_;
}
}
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v_a_3313_);
lean_del_object(v___x_3284_);
lean_dec_ref(v_snd_3266_);
lean_dec(v_numParams_3265_);
lean_dec(v___x_3264_);
lean_dec(v_levelParams_3261_);
lean_dec(v_declName_3260_);
v_a_3351_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3314_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3314_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_del_object(v___x_3284_);
lean_dec_ref(v_snd_3266_);
lean_dec(v_numParams_3265_);
lean_dec(v___x_3264_);
lean_dec(v_levelParams_3261_);
lean_dec(v_declName_3260_);
v_a_3359_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3312_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3312_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v_a_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3374_; 
lean_dec_ref(v___x_3293_);
lean_del_object(v___x_3284_);
lean_dec(v_snd_3282_);
lean_dec_ref(v_snd_3266_);
lean_dec(v_numParams_3265_);
lean_dec(v___x_3264_);
lean_dec(v_levelParams_3261_);
lean_dec(v_declName_3260_);
lean_dec_ref(v___x_3259_);
lean_dec_ref(v_alts_3255_);
lean_dec_ref(v_heq_3252_);
lean_dec_ref(v_params_3249_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v_is_3244_);
lean_dec_ref(v_motive_3238_);
v_a_3367_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3297_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3297_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3372_; 
if (v_isShared_3370_ == 0)
{
v___x_3372_ = v___x_3369_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3367_);
v___x_3372_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
return v___x_3372_;
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_dec_ref(v___x_3293_);
lean_del_object(v___x_3284_);
lean_dec(v_snd_3282_);
lean_dec_ref(v_snd_3266_);
lean_dec(v_numParams_3265_);
lean_dec(v___x_3264_);
lean_dec(v_levelParams_3261_);
lean_dec(v_declName_3260_);
lean_dec_ref(v___x_3259_);
lean_dec_ref(v___x_3258_);
lean_dec_ref(v_alts_3255_);
lean_dec(v_tail_3254_);
lean_dec_ref(v_heq_3252_);
lean_dec_ref(v_params_3249_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v_is_3244_);
lean_dec_ref(v_motive_3238_);
v_a_3375_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3295_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3295_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
else
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3391_; 
lean_dec_ref(v_snd_3266_);
lean_dec(v_numParams_3265_);
lean_dec(v___x_3264_);
lean_dec(v_levelParams_3261_);
lean_dec(v_declName_3260_);
lean_dec_ref(v___x_3259_);
lean_dec_ref(v___x_3258_);
lean_dec_ref(v_alts_3255_);
lean_dec(v_tail_3254_);
lean_dec_ref(v_heq_3252_);
lean_dec_ref(v_params_3249_);
lean_dec(v___x_3248_);
lean_dec(v___x_3247_);
lean_dec_ref(v___x_3246_);
lean_dec_ref(v___x_3245_);
lean_dec_ref(v_is_3244_);
lean_dec_ref(v_motive_3238_);
v_a_3384_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3391_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3391_ == 0)
{
v___x_3386_ = v___x_3279_;
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3279_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3391_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3389_; 
if (v_isShared_3387_ == 0)
{
v___x_3389_ = v___x_3386_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3390_; 
v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_a_3384_);
v___x_3389_ = v_reuseFailAlloc_3390_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
return v___x_3389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3392_ = _args[0];
lean_object* v___x_3393_ = _args[1];
lean_object* v___x_3394_ = _args[2];
lean_object* v___x_3395_ = _args[3];
lean_object* v___x_3396_ = _args[4];
lean_object* v_ism1_x27_3397_ = _args[5];
lean_object* v_is_3398_ = _args[6];
lean_object* v___x_3399_ = _args[7];
lean_object* v___x_3400_ = _args[8];
lean_object* v___x_3401_ = _args[9];
lean_object* v___x_3402_ = _args[10];
lean_object* v_params_3403_ = _args[11];
lean_object* v___x_3404_ = _args[12];
lean_object* v___x_3405_ = _args[13];
lean_object* v_heq_3406_ = _args[14];
lean_object* v_val_3407_ = _args[15];
lean_object* v_tail_3408_ = _args[16];
lean_object* v_alts_3409_ = _args[17];
lean_object* v_sz_3410_ = _args[18];
lean_object* v___x_3411_ = _args[19];
lean_object* v___x_3412_ = _args[20];
lean_object* v___x_3413_ = _args[21];
lean_object* v_declName_3414_ = _args[22];
lean_object* v_levelParams_3415_ = _args[23];
lean_object* v_numIndices_3416_ = _args[24];
lean_object* v___x_3417_ = _args[25];
lean_object* v___x_3418_ = _args[26];
lean_object* v_numParams_3419_ = _args[27];
lean_object* v_snd_3420_ = _args[28];
lean_object* v_ism2_x27_3421_ = _args[29];
lean_object* v_x_3422_ = _args[30];
lean_object* v___y_3423_ = _args[31];
lean_object* v___y_3424_ = _args[32];
lean_object* v___y_3425_ = _args[33];
lean_object* v___y_3426_ = _args[34];
lean_object* v___y_3427_ = _args[35];
_start:
{
uint8_t v___x_15697__boxed_3428_; uint8_t v___x_15698__boxed_3429_; uint8_t v___x_15699__boxed_3430_; size_t v_sz_boxed_3431_; size_t v___x_15708__boxed_3432_; lean_object* v_res_3433_; 
v___x_15697__boxed_3428_ = lean_unbox(v___x_3394_);
v___x_15698__boxed_3429_ = lean_unbox(v___x_3395_);
v___x_15699__boxed_3430_ = lean_unbox(v___x_3396_);
v_sz_boxed_3431_ = lean_unbox_usize(v_sz_3410_);
lean_dec(v_sz_3410_);
v___x_15708__boxed_3432_ = lean_unbox_usize(v___x_3411_);
lean_dec(v___x_3411_);
v_res_3433_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3392_, v___x_3393_, v___x_15697__boxed_3428_, v___x_15698__boxed_3429_, v___x_15699__boxed_3430_, v_ism1_x27_3397_, v_is_3398_, v___x_3399_, v___x_3400_, v___x_3401_, v___x_3402_, v_params_3403_, v___x_3404_, v___x_3405_, v_heq_3406_, v_val_3407_, v_tail_3408_, v_alts_3409_, v_sz_boxed_3431_, v___x_15708__boxed_3432_, v___x_3412_, v___x_3413_, v_declName_3414_, v_levelParams_3415_, v_numIndices_3416_, v___x_3417_, v___x_3418_, v_numParams_3419_, v_snd_3420_, v_ism2_x27_3421_, v_x_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec_ref(v_x_3422_);
lean_dec(v___x_3417_);
lean_dec(v_numIndices_3416_);
lean_dec_ref(v_val_3407_);
lean_dec_ref(v___x_3405_);
lean_dec_ref(v___x_3404_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3434_, lean_object* v___x_3435_, uint8_t v___x_3436_, uint8_t v___x_3437_, uint8_t v___x_3438_, lean_object* v_is_3439_, lean_object* v___x_3440_, lean_object* v___x_3441_, lean_object* v___x_3442_, lean_object* v___x_3443_, lean_object* v_params_3444_, lean_object* v___x_3445_, lean_object* v___x_3446_, lean_object* v_heq_3447_, lean_object* v_val_3448_, lean_object* v_tail_3449_, lean_object* v_alts_3450_, size_t v_sz_3451_, size_t v___x_3452_, lean_object* v___x_3453_, lean_object* v___x_3454_, lean_object* v_declName_3455_, lean_object* v_levelParams_3456_, lean_object* v_numIndices_3457_, lean_object* v___x_3458_, lean_object* v___x_3459_, lean_object* v_numParams_3460_, lean_object* v_snd_3461_, lean_object* v___x_3462_, lean_object* v___x_3463_, lean_object* v_ism1_x27_3464_, lean_object* v_x_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___f_3476_; lean_object* v___x_3477_; 
v___x_3471_ = lean_box(v___x_3436_);
v___x_3472_ = lean_box(v___x_3437_);
v___x_3473_ = lean_box(v___x_3438_);
v___x_3474_ = lean_box_usize(v_sz_3451_);
v___x_3475_ = lean_box_usize(v___x_3452_);
v___f_3476_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3476_, 0, v_motive_3434_);
lean_closure_set(v___f_3476_, 1, v___x_3435_);
lean_closure_set(v___f_3476_, 2, v___x_3471_);
lean_closure_set(v___f_3476_, 3, v___x_3472_);
lean_closure_set(v___f_3476_, 4, v___x_3473_);
lean_closure_set(v___f_3476_, 5, v_ism1_x27_3464_);
lean_closure_set(v___f_3476_, 6, v_is_3439_);
lean_closure_set(v___f_3476_, 7, v___x_3440_);
lean_closure_set(v___f_3476_, 8, v___x_3441_);
lean_closure_set(v___f_3476_, 9, v___x_3442_);
lean_closure_set(v___f_3476_, 10, v___x_3443_);
lean_closure_set(v___f_3476_, 11, v_params_3444_);
lean_closure_set(v___f_3476_, 12, v___x_3445_);
lean_closure_set(v___f_3476_, 13, v___x_3446_);
lean_closure_set(v___f_3476_, 14, v_heq_3447_);
lean_closure_set(v___f_3476_, 15, v_val_3448_);
lean_closure_set(v___f_3476_, 16, v_tail_3449_);
lean_closure_set(v___f_3476_, 17, v_alts_3450_);
lean_closure_set(v___f_3476_, 18, v___x_3474_);
lean_closure_set(v___f_3476_, 19, v___x_3475_);
lean_closure_set(v___f_3476_, 20, v___x_3453_);
lean_closure_set(v___f_3476_, 21, v___x_3454_);
lean_closure_set(v___f_3476_, 22, v_declName_3455_);
lean_closure_set(v___f_3476_, 23, v_levelParams_3456_);
lean_closure_set(v___f_3476_, 24, v_numIndices_3457_);
lean_closure_set(v___f_3476_, 25, v___x_3458_);
lean_closure_set(v___f_3476_, 26, v___x_3459_);
lean_closure_set(v___f_3476_, 27, v_numParams_3460_);
lean_closure_set(v___f_3476_, 28, v_snd_3461_);
v___x_3477_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3462_, v___x_3463_, v___f_3476_, v___x_3436_, v___x_3436_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3478_ = _args[0];
lean_object* v___x_3479_ = _args[1];
lean_object* v___x_3480_ = _args[2];
lean_object* v___x_3481_ = _args[3];
lean_object* v___x_3482_ = _args[4];
lean_object* v_is_3483_ = _args[5];
lean_object* v___x_3484_ = _args[6];
lean_object* v___x_3485_ = _args[7];
lean_object* v___x_3486_ = _args[8];
lean_object* v___x_3487_ = _args[9];
lean_object* v_params_3488_ = _args[10];
lean_object* v___x_3489_ = _args[11];
lean_object* v___x_3490_ = _args[12];
lean_object* v_heq_3491_ = _args[13];
lean_object* v_val_3492_ = _args[14];
lean_object* v_tail_3493_ = _args[15];
lean_object* v_alts_3494_ = _args[16];
lean_object* v_sz_3495_ = _args[17];
lean_object* v___x_3496_ = _args[18];
lean_object* v___x_3497_ = _args[19];
lean_object* v___x_3498_ = _args[20];
lean_object* v_declName_3499_ = _args[21];
lean_object* v_levelParams_3500_ = _args[22];
lean_object* v_numIndices_3501_ = _args[23];
lean_object* v___x_3502_ = _args[24];
lean_object* v___x_3503_ = _args[25];
lean_object* v_numParams_3504_ = _args[26];
lean_object* v_snd_3505_ = _args[27];
lean_object* v___x_3506_ = _args[28];
lean_object* v___x_3507_ = _args[29];
lean_object* v_ism1_x27_3508_ = _args[30];
lean_object* v_x_3509_ = _args[31];
lean_object* v___y_3510_ = _args[32];
lean_object* v___y_3511_ = _args[33];
lean_object* v___y_3512_ = _args[34];
lean_object* v___y_3513_ = _args[35];
lean_object* v___y_3514_ = _args[36];
_start:
{
uint8_t v___x_16019__boxed_3515_; uint8_t v___x_16020__boxed_3516_; uint8_t v___x_16021__boxed_3517_; size_t v_sz_boxed_3518_; size_t v___x_16030__boxed_3519_; lean_object* v_res_3520_; 
v___x_16019__boxed_3515_ = lean_unbox(v___x_3480_);
v___x_16020__boxed_3516_ = lean_unbox(v___x_3481_);
v___x_16021__boxed_3517_ = lean_unbox(v___x_3482_);
v_sz_boxed_3518_ = lean_unbox_usize(v_sz_3495_);
lean_dec(v_sz_3495_);
v___x_16030__boxed_3519_ = lean_unbox_usize(v___x_3496_);
lean_dec(v___x_3496_);
v_res_3520_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3478_, v___x_3479_, v___x_16019__boxed_3515_, v___x_16020__boxed_3516_, v___x_16021__boxed_3517_, v_is_3483_, v___x_3484_, v___x_3485_, v___x_3486_, v___x_3487_, v_params_3488_, v___x_3489_, v___x_3490_, v_heq_3491_, v_val_3492_, v_tail_3493_, v_alts_3494_, v_sz_boxed_3518_, v___x_16030__boxed_3519_, v___x_3497_, v___x_3498_, v_declName_3499_, v_levelParams_3500_, v_numIndices_3501_, v___x_3502_, v___x_3503_, v_numParams_3504_, v_snd_3505_, v___x_3506_, v___x_3507_, v_ism1_x27_3508_, v_x_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec_ref(v_x_3509_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3521_, lean_object* v___x_3522_, lean_object* v_motive_3523_, lean_object* v___x_3524_, uint8_t v___x_3525_, uint8_t v___x_3526_, uint8_t v___x_3527_, lean_object* v_is_3528_, lean_object* v___x_3529_, lean_object* v___x_3530_, lean_object* v___x_3531_, lean_object* v___x_3532_, lean_object* v_params_3533_, lean_object* v___x_3534_, lean_object* v___x_3535_, lean_object* v_heq_3536_, lean_object* v_val_3537_, lean_object* v_tail_3538_, size_t v_sz_3539_, size_t v___x_3540_, lean_object* v___x_3541_, lean_object* v___x_3542_, lean_object* v_declName_3543_, lean_object* v_levelParams_3544_, lean_object* v___x_3545_, lean_object* v___x_3546_, lean_object* v_numParams_3547_, lean_object* v_snd_3548_, lean_object* v___x_3549_, lean_object* v_alts_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___f_3563_; lean_object* v___x_3564_; 
v___x_3556_ = lean_nat_add(v_numIndices_3521_, v___x_3522_);
v___x_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
v___x_3558_ = lean_box(v___x_3525_);
v___x_3559_ = lean_box(v___x_3526_);
v___x_3560_ = lean_box(v___x_3527_);
v___x_3561_ = lean_box_usize(v_sz_3539_);
v___x_3562_ = lean_box_usize(v___x_3540_);
lean_inc_ref(v___x_3557_);
lean_inc_ref(v___x_3549_);
v___f_3563_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3563_, 0, v_motive_3523_);
lean_closure_set(v___f_3563_, 1, v___x_3524_);
lean_closure_set(v___f_3563_, 2, v___x_3558_);
lean_closure_set(v___f_3563_, 3, v___x_3559_);
lean_closure_set(v___f_3563_, 4, v___x_3560_);
lean_closure_set(v___f_3563_, 5, v_is_3528_);
lean_closure_set(v___f_3563_, 6, v___x_3529_);
lean_closure_set(v___f_3563_, 7, v___x_3530_);
lean_closure_set(v___f_3563_, 8, v___x_3531_);
lean_closure_set(v___f_3563_, 9, v___x_3532_);
lean_closure_set(v___f_3563_, 10, v_params_3533_);
lean_closure_set(v___f_3563_, 11, v___x_3534_);
lean_closure_set(v___f_3563_, 12, v___x_3535_);
lean_closure_set(v___f_3563_, 13, v_heq_3536_);
lean_closure_set(v___f_3563_, 14, v_val_3537_);
lean_closure_set(v___f_3563_, 15, v_tail_3538_);
lean_closure_set(v___f_3563_, 16, v_alts_3550_);
lean_closure_set(v___f_3563_, 17, v___x_3561_);
lean_closure_set(v___f_3563_, 18, v___x_3562_);
lean_closure_set(v___f_3563_, 19, v___x_3541_);
lean_closure_set(v___f_3563_, 20, v___x_3542_);
lean_closure_set(v___f_3563_, 21, v_declName_3543_);
lean_closure_set(v___f_3563_, 22, v_levelParams_3544_);
lean_closure_set(v___f_3563_, 23, v_numIndices_3521_);
lean_closure_set(v___f_3563_, 24, v___x_3545_);
lean_closure_set(v___f_3563_, 25, v___x_3546_);
lean_closure_set(v___f_3563_, 26, v_numParams_3547_);
lean_closure_set(v___f_3563_, 27, v_snd_3548_);
lean_closure_set(v___f_3563_, 28, v___x_3549_);
lean_closure_set(v___f_3563_, 29, v___x_3557_);
v___x_3564_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3549_, v___x_3557_, v___f_3563_, v___x_3525_, v___x_3525_, v___y_3551_, v___y_3552_, v___y_3553_, v___y_3554_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3565_ = _args[0];
lean_object* v___x_3566_ = _args[1];
lean_object* v_motive_3567_ = _args[2];
lean_object* v___x_3568_ = _args[3];
lean_object* v___x_3569_ = _args[4];
lean_object* v___x_3570_ = _args[5];
lean_object* v___x_3571_ = _args[6];
lean_object* v_is_3572_ = _args[7];
lean_object* v___x_3573_ = _args[8];
lean_object* v___x_3574_ = _args[9];
lean_object* v___x_3575_ = _args[10];
lean_object* v___x_3576_ = _args[11];
lean_object* v_params_3577_ = _args[12];
lean_object* v___x_3578_ = _args[13];
lean_object* v___x_3579_ = _args[14];
lean_object* v_heq_3580_ = _args[15];
lean_object* v_val_3581_ = _args[16];
lean_object* v_tail_3582_ = _args[17];
lean_object* v_sz_3583_ = _args[18];
lean_object* v___x_3584_ = _args[19];
lean_object* v___x_3585_ = _args[20];
lean_object* v___x_3586_ = _args[21];
lean_object* v_declName_3587_ = _args[22];
lean_object* v_levelParams_3588_ = _args[23];
lean_object* v___x_3589_ = _args[24];
lean_object* v___x_3590_ = _args[25];
lean_object* v_numParams_3591_ = _args[26];
lean_object* v_snd_3592_ = _args[27];
lean_object* v___x_3593_ = _args[28];
lean_object* v_alts_3594_ = _args[29];
lean_object* v___y_3595_ = _args[30];
lean_object* v___y_3596_ = _args[31];
lean_object* v___y_3597_ = _args[32];
lean_object* v___y_3598_ = _args[33];
lean_object* v___y_3599_ = _args[34];
_start:
{
uint8_t v___x_16112__boxed_3600_; uint8_t v___x_16113__boxed_3601_; uint8_t v___x_16114__boxed_3602_; size_t v_sz_boxed_3603_; size_t v___x_16123__boxed_3604_; lean_object* v_res_3605_; 
v___x_16112__boxed_3600_ = lean_unbox(v___x_3569_);
v___x_16113__boxed_3601_ = lean_unbox(v___x_3570_);
v___x_16114__boxed_3602_ = lean_unbox(v___x_3571_);
v_sz_boxed_3603_ = lean_unbox_usize(v_sz_3583_);
lean_dec(v_sz_3583_);
v___x_16123__boxed_3604_ = lean_unbox_usize(v___x_3584_);
lean_dec(v___x_3584_);
v_res_3605_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3565_, v___x_3566_, v_motive_3567_, v___x_3568_, v___x_16112__boxed_3600_, v___x_16113__boxed_3601_, v___x_16114__boxed_3602_, v_is_3572_, v___x_3573_, v___x_3574_, v___x_3575_, v___x_3576_, v_params_3577_, v___x_3578_, v___x_3579_, v_heq_3580_, v_val_3581_, v_tail_3582_, v_sz_boxed_3603_, v___x_16123__boxed_3604_, v___x_3585_, v___x_3586_, v_declName_3587_, v_levelParams_3588_, v___x_3589_, v___x_3590_, v_numParams_3591_, v_snd_3592_, v___x_3593_, v_alts_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___x_3566_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3606_, lean_object* v_declInfos_3607_, lean_object* v_k_3608_, lean_object* v_kind_3609_, lean_object* v_x_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
uint8_t v_kind_boxed_3616_; lean_object* v_res_3617_; 
v_kind_boxed_3616_ = lean_unbox(v_kind_3609_);
v_res_3617_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3606_, v_declInfos_3607_, v_k_3608_, v_kind_boxed_3616_, v_x_3610_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3618_, lean_object* v_k_3619_, uint8_t v_kind_3620_, lean_object* v_acc_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v___x_3627_; lean_object* v_toApplicative_3628_; lean_object* v_toFunctor_3629_; lean_object* v_toSeq_3630_; lean_object* v_toSeqLeft_3631_; lean_object* v_toSeqRight_3632_; lean_object* v___f_3633_; lean_object* v___f_3634_; lean_object* v___f_3635_; lean_object* v___f_3636_; lean_object* v___x_3637_; lean_object* v___f_3638_; lean_object* v___f_3639_; lean_object* v___f_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v_toApplicative_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3701_; 
v___x_3627_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3628_ = lean_ctor_get(v___x_3627_, 0);
v_toFunctor_3629_ = lean_ctor_get(v_toApplicative_3628_, 0);
v_toSeq_3630_ = lean_ctor_get(v_toApplicative_3628_, 2);
v_toSeqLeft_3631_ = lean_ctor_get(v_toApplicative_3628_, 3);
v_toSeqRight_3632_ = lean_ctor_get(v_toApplicative_3628_, 4);
v___f_3633_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3634_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3629_, 2);
v___f_3635_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3635_, 0, v_toFunctor_3629_);
v___f_3636_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3636_, 0, v_toFunctor_3629_);
v___x_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___f_3635_);
lean_ctor_set(v___x_3637_, 1, v___f_3636_);
lean_inc(v_toSeqRight_3632_);
v___f_3638_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3638_, 0, v_toSeqRight_3632_);
lean_inc(v_toSeqLeft_3631_);
v___f_3639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3639_, 0, v_toSeqLeft_3631_);
lean_inc(v_toSeq_3630_);
v___f_3640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3640_, 0, v_toSeq_3630_);
v___x_3641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3637_);
lean_ctor_set(v___x_3641_, 1, v___f_3633_);
lean_ctor_set(v___x_3641_, 2, v___f_3640_);
lean_ctor_set(v___x_3641_, 3, v___f_3639_);
lean_ctor_set(v___x_3641_, 4, v___f_3638_);
v___x_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set(v___x_3642_, 1, v___f_3634_);
v___x_3643_ = l_StateRefT_x27_instMonad___redArg(v___x_3642_);
v_toApplicative_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v___x_3643_, 1);
lean_dec(v_unused_3702_);
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3701_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_toApplicative_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3701_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v_toFunctor_3648_; lean_object* v_toSeq_3649_; lean_object* v_toSeqLeft_3650_; lean_object* v_toSeqRight_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3699_; 
v_toFunctor_3648_ = lean_ctor_get(v_toApplicative_3644_, 0);
v_toSeq_3649_ = lean_ctor_get(v_toApplicative_3644_, 2);
v_toSeqLeft_3650_ = lean_ctor_get(v_toApplicative_3644_, 3);
v_toSeqRight_3651_ = lean_ctor_get(v_toApplicative_3644_, 4);
v_isSharedCheck_3699_ = !lean_is_exclusive(v_toApplicative_3644_);
if (v_isSharedCheck_3699_ == 0)
{
lean_object* v_unused_3700_; 
v_unused_3700_ = lean_ctor_get(v_toApplicative_3644_, 1);
lean_dec(v_unused_3700_);
v___x_3653_ = v_toApplicative_3644_;
v_isShared_3654_ = v_isSharedCheck_3699_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_toSeqRight_3651_);
lean_inc(v_toSeqLeft_3650_);
lean_inc(v_toSeq_3649_);
lean_inc(v_toFunctor_3648_);
lean_dec(v_toApplicative_3644_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3699_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___f_3655_; lean_object* v___f_3656_; lean_object* v___f_3657_; lean_object* v___f_3658_; lean_object* v___x_3659_; lean_object* v___f_3660_; lean_object* v___f_3661_; lean_object* v___f_3662_; lean_object* v___x_3664_; 
v___f_3655_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3656_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3648_);
v___f_3657_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3657_, 0, v_toFunctor_3648_);
v___f_3658_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3658_, 0, v_toFunctor_3648_);
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___f_3657_);
lean_ctor_set(v___x_3659_, 1, v___f_3658_);
v___f_3660_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3660_, 0, v_toSeqRight_3651_);
v___f_3661_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3661_, 0, v_toSeqLeft_3650_);
v___f_3662_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3662_, 0, v_toSeq_3649_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 4, v___f_3660_);
lean_ctor_set(v___x_3653_, 3, v___f_3661_);
lean_ctor_set(v___x_3653_, 2, v___f_3662_);
lean_ctor_set(v___x_3653_, 1, v___f_3655_);
lean_ctor_set(v___x_3653_, 0, v___x_3659_);
v___x_3664_ = v___x_3653_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v___f_3655_);
lean_ctor_set(v_reuseFailAlloc_3698_, 2, v___f_3662_);
lean_ctor_set(v_reuseFailAlloc_3698_, 3, v___f_3661_);
lean_ctor_set(v_reuseFailAlloc_3698_, 4, v___f_3660_);
v___x_3664_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 1, v___f_3656_);
lean_ctor_set(v___x_3646_, 0, v___x_3664_);
v___x_3666_ = v___x_3646_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3664_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v___f_3656_);
v___x_3666_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v___x_3667_ = lean_array_get_size(v_acc_3621_);
v___x_3668_ = lean_array_get_size(v_declInfos_3618_);
v___x_3669_ = lean_nat_dec_lt(v___x_3667_, v___x_3668_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; 
lean_dec_ref(v___x_3666_);
lean_dec_ref(v_declInfos_3618_);
lean_inc(v___y_3625_);
lean_inc_ref(v___y_3624_);
lean_inc(v___y_3623_);
lean_inc_ref(v___y_3622_);
v___x_3670_ = lean_apply_6(v_k_3619_, v_acc_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, lean_box(0));
return v___x_3670_;
}
else
{
lean_object* v___f_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; lean_object* v___f_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v_snd_3679_; lean_object* v_fst_3680_; lean_object* v_fst_3681_; lean_object* v_snd_3682_; lean_object* v___x_3683_; 
v___f_3671_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3671_, 0, v___x_3666_);
v___x_3672_ = lean_box(0);
v___x_3673_ = 0;
v___f_3674_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3674_, 0, v___f_3671_);
v___x_3675_ = lean_box(v___x_3673_);
v___x_3676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
lean_ctor_set(v___x_3676_, 1, v___f_3674_);
v___x_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3672_);
lean_ctor_set(v___x_3677_, 1, v___x_3676_);
v___x_3678_ = lean_array_get(v___x_3677_, v_declInfos_3618_, v___x_3667_);
lean_dec_ref_known(v___x_3677_, 2);
v_snd_3679_ = lean_ctor_get(v___x_3678_, 1);
lean_inc(v_snd_3679_);
v_fst_3680_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_fst_3680_);
lean_dec(v___x_3678_);
v_fst_3681_ = lean_ctor_get(v_snd_3679_, 0);
lean_inc(v_fst_3681_);
v_snd_3682_ = lean_ctor_get(v_snd_3679_, 1);
lean_inc(v_snd_3682_);
lean_dec(v_snd_3679_);
lean_inc(v___y_3625_);
lean_inc_ref(v___y_3624_);
lean_inc(v___y_3623_);
lean_inc_ref(v___y_3622_);
lean_inc_ref(v_acc_3621_);
v___x_3683_ = lean_apply_6(v_snd_3682_, v_acc_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, lean_box(0));
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3685_; lean_object* v___f_3686_; uint8_t v___x_3687_; lean_object* v___x_3688_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
v___x_3685_ = lean_box(v_kind_3620_);
v___f_3686_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3686_, 0, v_acc_3621_);
lean_closure_set(v___f_3686_, 1, v_declInfos_3618_);
lean_closure_set(v___f_3686_, 2, v_k_3619_);
lean_closure_set(v___f_3686_, 3, v___x_3685_);
v___x_3687_ = lean_unbox(v_fst_3681_);
lean_dec(v_fst_3681_);
v___x_3688_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3680_, v___x_3687_, v_a_3684_, v___f_3686_, v_kind_3620_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
return v___x_3688_;
}
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_dec(v_fst_3681_);
lean_dec(v_fst_3680_);
lean_dec_ref(v_acc_3621_);
lean_dec_ref(v_k_3619_);
lean_dec_ref(v_declInfos_3618_);
v_a_3689_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3683_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3683_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3703_, lean_object* v_declInfos_3704_, lean_object* v_k_3705_, uint8_t v_kind_3706_, lean_object* v_x_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3713_ = lean_array_push(v_acc_3703_, v_x_3707_);
v___x_3714_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3704_, v_k_3705_, v_kind_3706_, v___x_3713_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3715_, lean_object* v_k_3716_, lean_object* v_kind_3717_, lean_object* v_acc_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
uint8_t v_kind_boxed_3724_; lean_object* v_res_3725_; 
v_kind_boxed_3724_ = lean_unbox(v_kind_3717_);
v_res_3725_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3715_, v_k_3716_, v_kind_boxed_3724_, v_acc_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3726_, lean_object* v_k_3727_, uint8_t v_kind_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3734_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3735_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3726_, v_k_3727_, v_kind_3728_, v___x_3734_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3736_, lean_object* v_k_3737_, lean_object* v_kind_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
uint8_t v_kind_boxed_3744_; lean_object* v_res_3745_; 
v_kind_boxed_3744_ = lean_unbox(v_kind_3738_);
v_res_3745_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3736_, v_k_3737_, v_kind_boxed_3744_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
return v_res_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3746_, lean_object* v_k_3747_, uint8_t v_kind_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_){
_start:
{
size_t v_sz_3754_; size_t v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
v_sz_3754_ = lean_array_size(v_declInfos_3746_);
v___x_3755_ = ((size_t)0ULL);
v___x_3756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3754_, v___x_3755_, v_declInfos_3746_);
v___x_3757_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3756_, v_k_3747_, v_kind_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3758_, lean_object* v_k_3759_, lean_object* v_kind_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
uint8_t v_kind_boxed_3766_; lean_object* v_res_3767_; 
v_kind_boxed_3766_ = lean_unbox(v_kind_3760_);
v_res_3767_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3758_, v_k_3759_, v_kind_boxed_3766_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3768_, lean_object* v_k_3769_, uint8_t v_kind_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
size_t v_sz_3776_; size_t v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v_sz_3776_ = lean_array_size(v_declInfos_3768_);
v___x_3777_ = ((size_t)0ULL);
v___x_3778_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3776_, v___x_3777_, v_declInfos_3768_);
v___x_3779_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3778_, v_k_3769_, v_kind_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
return v___x_3779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3780_, lean_object* v_k_3781_, lean_object* v_kind_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_){
_start:
{
uint8_t v_kind_boxed_3788_; lean_object* v_res_3789_; 
v_kind_boxed_3788_ = lean_unbox(v_kind_3782_);
v_res_3789_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3780_, v_k_3781_, v_kind_boxed_3788_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
return v_res_3789_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3792_ = lean_box(0);
v___x_3793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3794_ = l_Lean_mkConst(v___x_3793_, v___x_3792_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3795_, lean_object* v___x_3796_, lean_object* v_motive_3797_, uint8_t v___x_3798_, uint8_t v___x_3799_, uint8_t v___x_3800_, lean_object* v___x_3801_, lean_object* v_v_3802_, lean_object* v___x_3803_, lean_object* v_zs12_3804_, lean_object* v_is_3805_, lean_object* v_fields1_3806_, lean_object* v_fields2_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v_e_3823_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_inc(v___x_3795_);
v___x_3833_ = l_Lean_mkNatLit(v___x_3795_);
v___x_3834_ = l_Lean_Meta_mkEqRefl(v___x_3833_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v___x_3834_, 1);
lean_inc_ref(v___x_3796_);
v___x_3836_ = l_Lean_mkAppN(v___x_3796_, v_fields1_3806_);
v___x_3837_ = l_Lean_mkAppN(v___x_3796_, v_fields2_3807_);
v___x_3838_ = lean_unsigned_to_nat(3u);
v___x_3839_ = lean_mk_empty_array_with_capacity(v___x_3838_);
v___x_3840_ = lean_array_push(v___x_3839_, v___x_3836_);
v___x_3841_ = lean_array_push(v___x_3840_, v___x_3837_);
v___x_3842_ = lean_array_push(v___x_3841_, v_a_3835_);
v___x_3843_ = l_Array_append___redArg(v_is_3805_, v___x_3842_);
lean_dec_ref(v___x_3842_);
v___x_3844_ = l_Lean_mkAppN(v_motive_3797_, v___x_3843_);
lean_dec_ref(v___x_3843_);
v___x_3845_ = l_Lean_Meta_mkForallFVars(v_zs12_3804_, v___x_3844_, v___x_3798_, v___x_3799_, v___x_3799_, v___x_3800_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v___x_3847_ = lean_array_get_size(v_zs12_3804_);
v___x_3848_ = lean_nat_dec_eq(v___x_3847_, v___x_3801_);
if (v___x_3848_ == 0)
{
v_e_3823_ = v_a_3846_;
goto v___jp_3822_;
}
else
{
lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3849_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3850_ = l_Lean_mkArrow(v___x_3849_, v_a_3846_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v_a_3851_; 
v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_a_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v_e_3823_ = v_a_3851_;
goto v___jp_3822_;
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_dec(v_v_3802_);
lean_dec(v___x_3801_);
lean_dec(v___x_3795_);
v_a_3852_ = lean_ctor_get(v___x_3850_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3850_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3850_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3850_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec(v_v_3802_);
lean_dec(v___x_3801_);
lean_dec(v___x_3795_);
v_a_3860_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3845_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3845_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec_ref(v_is_3805_);
lean_dec(v_v_3802_);
lean_dec(v___x_3801_);
lean_dec_ref(v_motive_3797_);
lean_dec_ref(v___x_3796_);
lean_dec(v___x_3795_);
v_a_3868_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3834_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3834_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
v___jp_3813_:
{
lean_object* v___x_3816_; uint8_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3816_ = lean_array_get_size(v_zs12_3804_);
v___x_3817_ = lean_nat_dec_eq(v___x_3816_, v___x_3801_);
v___x_3818_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3818_, 0, v___x_3816_);
lean_ctor_set(v___x_3818_, 1, v___x_3801_);
lean_ctor_set_uint8(v___x_3818_, sizeof(void*)*2, v___x_3817_);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___y_3815_);
lean_ctor_set(v___x_3819_, 1, v___y_3814_);
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3819_);
lean_ctor_set(v___x_3820_, 1, v___x_3818_);
v___x_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
return v___x_3821_;
}
v___jp_3822_:
{
if (lean_obj_tag(v_v_3802_) == 1)
{
lean_object* v_str_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
lean_dec(v___x_3795_);
v_str_3824_ = lean_ctor_get(v_v_3802_, 1);
lean_inc_ref(v_str_3824_);
lean_dec_ref_known(v_v_3802_, 2);
v___x_3825_ = lean_box(0);
v___x_3826_ = l_Lean_Name_str___override(v___x_3825_, v_str_3824_);
v___y_3814_ = v_e_3823_;
v___y_3815_ = v___x_3826_;
goto v___jp_3813_;
}
else
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
lean_dec(v_v_3802_);
v___x_3827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3828_ = lean_nat_add(v___x_3795_, v___x_3803_);
lean_dec(v___x_3795_);
v___x_3829_ = l_Nat_reprFast(v___x_3828_);
v___x_3830_ = lean_string_append(v___x_3827_, v___x_3829_);
lean_dec_ref(v___x_3829_);
v___x_3831_ = lean_box(0);
v___x_3832_ = l_Lean_Name_str___override(v___x_3831_, v___x_3830_);
v___y_3814_ = v_e_3823_;
v___y_3815_ = v___x_3832_;
goto v___jp_3813_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3876_ = _args[0];
lean_object* v___x_3877_ = _args[1];
lean_object* v_motive_3878_ = _args[2];
lean_object* v___x_3879_ = _args[3];
lean_object* v___x_3880_ = _args[4];
lean_object* v___x_3881_ = _args[5];
lean_object* v___x_3882_ = _args[6];
lean_object* v_v_3883_ = _args[7];
lean_object* v___x_3884_ = _args[8];
lean_object* v_zs12_3885_ = _args[9];
lean_object* v_is_3886_ = _args[10];
lean_object* v_fields1_3887_ = _args[11];
lean_object* v_fields2_3888_ = _args[12];
lean_object* v___y_3889_ = _args[13];
lean_object* v___y_3890_ = _args[14];
lean_object* v___y_3891_ = _args[15];
lean_object* v___y_3892_ = _args[16];
lean_object* v___y_3893_ = _args[17];
_start:
{
uint8_t v___x_16455__boxed_3894_; uint8_t v___x_16456__boxed_3895_; uint8_t v___x_16457__boxed_3896_; lean_object* v_res_3897_; 
v___x_16455__boxed_3894_ = lean_unbox(v___x_3879_);
v___x_16456__boxed_3895_ = lean_unbox(v___x_3880_);
v___x_16457__boxed_3896_ = lean_unbox(v___x_3881_);
v_res_3897_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3876_, v___x_3877_, v_motive_3878_, v___x_16455__boxed_3894_, v___x_16456__boxed_3895_, v___x_16457__boxed_3896_, v___x_3882_, v_v_3883_, v___x_3884_, v_zs12_3885_, v_is_3886_, v_fields1_3887_, v_fields2_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec_ref(v_fields2_3888_);
lean_dec_ref(v_fields1_3887_);
lean_dec_ref(v_zs12_3885_);
lean_dec(v___x_3884_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3898_, lean_object* v_params_3899_, lean_object* v_motive_3900_, size_t v_sz_3901_, size_t v_i_3902_, lean_object* v_bs_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
uint8_t v___x_3909_; 
v___x_3909_ = lean_usize_dec_lt(v_i_3902_, v_sz_3901_);
if (v___x_3909_ == 0)
{
lean_object* v___x_3910_; 
lean_dec_ref(v_motive_3900_);
lean_dec(v_tail_3898_);
v___x_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3910_, 0, v_bs_3903_);
return v___x_3910_;
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; uint8_t v___x_3914_; lean_object* v_v_3915_; lean_object* v_bs_x27_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___f_3923_; lean_object* v___x_3924_; 
v___x_3911_ = lean_unsigned_to_nat(0u);
v___x_3912_ = lean_unsigned_to_nat(1u);
v___x_3913_ = 0;
v___x_3914_ = 1;
v_v_3915_ = lean_array_uget(v_bs_3903_, v_i_3902_);
v_bs_x27_3916_ = lean_array_uset(v_bs_3903_, v_i_3902_, v___x_3911_);
v___x_3917_ = lean_usize_to_nat(v_i_3902_);
lean_inc(v_tail_3898_);
lean_inc(v_v_3915_);
v___x_3918_ = l_Lean_mkConst(v_v_3915_, v_tail_3898_);
v___x_3919_ = l_Lean_mkAppN(v___x_3918_, v_params_3899_);
v___x_3920_ = lean_box(v___x_3913_);
v___x_3921_ = lean_box(v___x_3909_);
v___x_3922_ = lean_box(v___x_3914_);
lean_inc_ref(v_motive_3900_);
lean_inc_ref(v___x_3919_);
v___f_3923_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3923_, 0, v___x_3917_);
lean_closure_set(v___f_3923_, 1, v___x_3919_);
lean_closure_set(v___f_3923_, 2, v_motive_3900_);
lean_closure_set(v___f_3923_, 3, v___x_3920_);
lean_closure_set(v___f_3923_, 4, v___x_3921_);
lean_closure_set(v___f_3923_, 5, v___x_3922_);
lean_closure_set(v___f_3923_, 6, v___x_3911_);
lean_closure_set(v___f_3923_, 7, v_v_3915_);
lean_closure_set(v___f_3923_, 8, v___x_3912_);
v___x_3924_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3919_, v___f_3923_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; size_t v___x_3926_; size_t v___x_3927_; lean_object* v___x_3928_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v___x_3926_ = ((size_t)1ULL);
v___x_3927_ = lean_usize_add(v_i_3902_, v___x_3926_);
v___x_3928_ = lean_array_uset(v_bs_x27_3916_, v_i_3902_, v_a_3925_);
v_i_3902_ = v___x_3927_;
v_bs_3903_ = v___x_3928_;
goto _start;
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec_ref(v_bs_x27_3916_);
lean_dec_ref(v_motive_3900_);
lean_dec(v_tail_3898_);
v_a_3930_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3924_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3924_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3938_, lean_object* v_params_3939_, lean_object* v_motive_3940_, lean_object* v_sz_3941_, lean_object* v_i_3942_, lean_object* v_bs_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
size_t v_sz_boxed_3949_; size_t v_i_boxed_3950_; lean_object* v_res_3951_; 
v_sz_boxed_3949_ = lean_unbox_usize(v_sz_3941_);
lean_dec(v_sz_3941_);
v_i_boxed_3950_ = lean_unbox_usize(v_i_3942_);
lean_dec(v_i_3942_);
v_res_3951_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3938_, v_params_3939_, v_motive_3940_, v_sz_boxed_3949_, v_i_boxed_3950_, v_bs_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec_ref(v_params_3939_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3954_, lean_object* v_tail_3955_, lean_object* v_params_3956_, lean_object* v_numIndices_3957_, lean_object* v___x_3958_, lean_object* v___x_3959_, uint8_t v___x_3960_, uint8_t v___x_3961_, uint8_t v___x_3962_, lean_object* v_is_3963_, lean_object* v___x_3964_, lean_object* v___x_3965_, lean_object* v___x_3966_, lean_object* v___x_3967_, lean_object* v___x_3968_, lean_object* v___x_3969_, lean_object* v_heq_3970_, lean_object* v_val_3971_, lean_object* v___x_3972_, lean_object* v_declName_3973_, lean_object* v_levelParams_3974_, lean_object* v___x_3975_, lean_object* v___x_3976_, lean_object* v_numParams_3977_, lean_object* v___x_3978_, lean_object* v_motive_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
lean_object* v___x_3985_; size_t v_sz_3986_; size_t v___x_3987_; lean_object* v___x_3988_; 
v___x_3985_ = lean_array_mk(v_ctors_3954_);
v_sz_3986_ = lean_array_size(v___x_3985_);
v___x_3987_ = ((size_t)0ULL);
lean_inc_ref(v___x_3985_);
lean_inc_ref(v_motive_3979_);
lean_inc(v_tail_3955_);
v___x_3988_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3955_, v_params_3956_, v_motive_3979_, v_sz_3986_, v___x_3987_, v___x_3985_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v_a_3989_; lean_object* v___x_3990_; lean_object* v_fst_3991_; lean_object* v_snd_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___f_3998_; uint8_t v___x_3999_; lean_object* v___x_4000_; 
v_a_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc(v_a_3989_);
lean_dec_ref_known(v___x_3988_, 1);
v___x_3990_ = l_Array_unzip___redArg(v_a_3989_);
lean_dec(v_a_3989_);
v_fst_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc(v_fst_3991_);
v_snd_3992_ = lean_ctor_get(v___x_3990_, 1);
lean_inc(v_snd_3992_);
lean_dec_ref(v___x_3990_);
v___x_3993_ = lean_box(v___x_3960_);
v___x_3994_ = lean_box(v___x_3961_);
v___x_3995_ = lean_box(v___x_3962_);
v___x_3996_ = lean_box_usize(v_sz_3986_);
v___x_3997_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_3998_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_3998_, 0, v_numIndices_3957_);
lean_closure_set(v___f_3998_, 1, v___x_3958_);
lean_closure_set(v___f_3998_, 2, v_motive_3979_);
lean_closure_set(v___f_3998_, 3, v___x_3959_);
lean_closure_set(v___f_3998_, 4, v___x_3993_);
lean_closure_set(v___f_3998_, 5, v___x_3994_);
lean_closure_set(v___f_3998_, 6, v___x_3995_);
lean_closure_set(v___f_3998_, 7, v_is_3963_);
lean_closure_set(v___f_3998_, 8, v___x_3964_);
lean_closure_set(v___f_3998_, 9, v___x_3965_);
lean_closure_set(v___f_3998_, 10, v___x_3966_);
lean_closure_set(v___f_3998_, 11, v___x_3967_);
lean_closure_set(v___f_3998_, 12, v_params_3956_);
lean_closure_set(v___f_3998_, 13, v___x_3968_);
lean_closure_set(v___f_3998_, 14, v___x_3969_);
lean_closure_set(v___f_3998_, 15, v_heq_3970_);
lean_closure_set(v___f_3998_, 16, v_val_3971_);
lean_closure_set(v___f_3998_, 17, v_tail_3955_);
lean_closure_set(v___f_3998_, 18, v___x_3996_);
lean_closure_set(v___f_3998_, 19, v___x_3997_);
lean_closure_set(v___f_3998_, 20, v___x_3985_);
lean_closure_set(v___f_3998_, 21, v___x_3972_);
lean_closure_set(v___f_3998_, 22, v_declName_3973_);
lean_closure_set(v___f_3998_, 23, v_levelParams_3974_);
lean_closure_set(v___f_3998_, 24, v___x_3975_);
lean_closure_set(v___f_3998_, 25, v___x_3976_);
lean_closure_set(v___f_3998_, 26, v_numParams_3977_);
lean_closure_set(v___f_3998_, 27, v_snd_3992_);
lean_closure_set(v___f_3998_, 28, v___x_3978_);
v___x_3999_ = 0;
v___x_4000_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_3991_, v___f_3998_, v___x_3999_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
return v___x_4000_;
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec_ref(v___x_3985_);
lean_dec_ref(v_motive_3979_);
lean_dec_ref(v___x_3978_);
lean_dec(v_numParams_3977_);
lean_dec(v___x_3976_);
lean_dec(v___x_3975_);
lean_dec(v_levelParams_3974_);
lean_dec(v_declName_3973_);
lean_dec_ref(v___x_3972_);
lean_dec_ref(v_val_3971_);
lean_dec_ref(v_heq_3970_);
lean_dec_ref(v___x_3969_);
lean_dec_ref(v___x_3968_);
lean_dec(v___x_3967_);
lean_dec(v___x_3966_);
lean_dec_ref(v___x_3965_);
lean_dec_ref(v___x_3964_);
lean_dec_ref(v_is_3963_);
lean_dec_ref(v___x_3959_);
lean_dec(v___x_3958_);
lean_dec(v_numIndices_3957_);
lean_dec_ref(v_params_3956_);
lean_dec(v_tail_3955_);
v_a_4001_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3988_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3988_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4009_ = _args[0];
lean_object* v_tail_4010_ = _args[1];
lean_object* v_params_4011_ = _args[2];
lean_object* v_numIndices_4012_ = _args[3];
lean_object* v___x_4013_ = _args[4];
lean_object* v___x_4014_ = _args[5];
lean_object* v___x_4015_ = _args[6];
lean_object* v___x_4016_ = _args[7];
lean_object* v___x_4017_ = _args[8];
lean_object* v_is_4018_ = _args[9];
lean_object* v___x_4019_ = _args[10];
lean_object* v___x_4020_ = _args[11];
lean_object* v___x_4021_ = _args[12];
lean_object* v___x_4022_ = _args[13];
lean_object* v___x_4023_ = _args[14];
lean_object* v___x_4024_ = _args[15];
lean_object* v_heq_4025_ = _args[16];
lean_object* v_val_4026_ = _args[17];
lean_object* v___x_4027_ = _args[18];
lean_object* v_declName_4028_ = _args[19];
lean_object* v_levelParams_4029_ = _args[20];
lean_object* v___x_4030_ = _args[21];
lean_object* v___x_4031_ = _args[22];
lean_object* v_numParams_4032_ = _args[23];
lean_object* v___x_4033_ = _args[24];
lean_object* v_motive_4034_ = _args[25];
lean_object* v___y_4035_ = _args[26];
lean_object* v___y_4036_ = _args[27];
lean_object* v___y_4037_ = _args[28];
lean_object* v___y_4038_ = _args[29];
lean_object* v___y_4039_ = _args[30];
_start:
{
uint8_t v___x_16694__boxed_4040_; uint8_t v___x_16695__boxed_4041_; uint8_t v___x_16696__boxed_4042_; lean_object* v_res_4043_; 
v___x_16694__boxed_4040_ = lean_unbox(v___x_4015_);
v___x_16695__boxed_4041_ = lean_unbox(v___x_4016_);
v___x_16696__boxed_4042_ = lean_unbox(v___x_4017_);
v_res_4043_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4009_, v_tail_4010_, v_params_4011_, v_numIndices_4012_, v___x_4013_, v___x_4014_, v___x_16694__boxed_4040_, v___x_16695__boxed_4041_, v___x_16696__boxed_4042_, v_is_4018_, v___x_4019_, v___x_4020_, v___x_4021_, v___x_4022_, v___x_4023_, v___x_4024_, v_heq_4025_, v_val_4026_, v___x_4027_, v_declName_4028_, v_levelParams_4029_, v___x_4030_, v___x_4031_, v_numParams_4032_, v___x_4033_, v_motive_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4044_, lean_object* v___x_4045_, lean_object* v_is_4046_, lean_object* v_head_4047_, lean_object* v_ctors_4048_, lean_object* v_tail_4049_, lean_object* v_params_4050_, lean_object* v_numIndices_4051_, lean_object* v___x_4052_, lean_object* v___x_4053_, lean_object* v___x_4054_, lean_object* v___x_4055_, lean_object* v___x_4056_, lean_object* v_val_4057_, lean_object* v___x_4058_, lean_object* v_declName_4059_, lean_object* v_levelParams_4060_, lean_object* v___x_4061_, lean_object* v_numParams_4062_, lean_object* v___x_4063_, lean_object* v_heq_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; uint8_t v___x_4078_; uint8_t v___x_4079_; lean_object* v___x_4080_; 
v___x_4070_ = lean_unsigned_to_nat(3u);
v___x_4071_ = lean_mk_empty_array_with_capacity(v___x_4070_);
lean_inc_ref(v___x_4044_);
v___x_4072_ = lean_array_push(v___x_4071_, v___x_4044_);
lean_inc_ref(v___x_4045_);
v___x_4073_ = lean_array_push(v___x_4072_, v___x_4045_);
lean_inc_ref(v_heq_4064_);
v___x_4074_ = lean_array_push(v___x_4073_, v_heq_4064_);
lean_inc_ref(v_is_4046_);
v___x_4075_ = l_Array_append___redArg(v_is_4046_, v___x_4074_);
lean_dec_ref(v___x_4074_);
v___x_4076_ = l_Lean_mkSort(v_head_4047_);
v___x_4077_ = 0;
v___x_4078_ = 1;
v___x_4079_ = 1;
v___x_4080_ = l_Lean_Meta_mkForallFVars(v___x_4075_, v___x_4076_, v___x_4077_, v___x_4078_, v___x_4078_, v___x_4079_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___f_4085_; lean_object* v___x_4086_; uint8_t v___x_4087_; lean_object* v___x_4088_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v___x_4080_, 1);
v___x_4082_ = lean_box(v___x_4077_);
v___x_4083_ = lean_box(v___x_4078_);
v___x_4084_ = lean_box(v___x_4079_);
v___f_4085_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4085_, 0, v_ctors_4048_);
lean_closure_set(v___f_4085_, 1, v_tail_4049_);
lean_closure_set(v___f_4085_, 2, v_params_4050_);
lean_closure_set(v___f_4085_, 3, v_numIndices_4051_);
lean_closure_set(v___f_4085_, 4, v___x_4052_);
lean_closure_set(v___f_4085_, 5, v___x_4075_);
lean_closure_set(v___f_4085_, 6, v___x_4082_);
lean_closure_set(v___f_4085_, 7, v___x_4083_);
lean_closure_set(v___f_4085_, 8, v___x_4084_);
lean_closure_set(v___f_4085_, 9, v_is_4046_);
lean_closure_set(v___f_4085_, 10, v___x_4045_);
lean_closure_set(v___f_4085_, 11, v___x_4044_);
lean_closure_set(v___f_4085_, 12, v___x_4053_);
lean_closure_set(v___f_4085_, 13, v___x_4054_);
lean_closure_set(v___f_4085_, 14, v___x_4055_);
lean_closure_set(v___f_4085_, 15, v___x_4056_);
lean_closure_set(v___f_4085_, 16, v_heq_4064_);
lean_closure_set(v___f_4085_, 17, v_val_4057_);
lean_closure_set(v___f_4085_, 18, v___x_4058_);
lean_closure_set(v___f_4085_, 19, v_declName_4059_);
lean_closure_set(v___f_4085_, 20, v_levelParams_4060_);
lean_closure_set(v___f_4085_, 21, v___x_4070_);
lean_closure_set(v___f_4085_, 22, v___x_4061_);
lean_closure_set(v___f_4085_, 23, v_numParams_4062_);
lean_closure_set(v___f_4085_, 24, v___x_4063_);
v___x_4086_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4087_ = 0;
v___x_4088_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4086_, v___x_4079_, v_a_4081_, v___f_4085_, v___x_4087_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
return v___x_4088_;
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec_ref(v___x_4075_);
lean_dec_ref(v_heq_4064_);
lean_dec_ref(v___x_4063_);
lean_dec(v_numParams_4062_);
lean_dec(v___x_4061_);
lean_dec(v_levelParams_4060_);
lean_dec(v_declName_4059_);
lean_dec_ref(v___x_4058_);
lean_dec_ref(v_val_4057_);
lean_dec_ref(v___x_4056_);
lean_dec_ref(v___x_4055_);
lean_dec(v___x_4054_);
lean_dec(v___x_4053_);
lean_dec(v___x_4052_);
lean_dec(v_numIndices_4051_);
lean_dec_ref(v_params_4050_);
lean_dec(v_tail_4049_);
lean_dec(v_ctors_4048_);
lean_dec_ref(v_is_4046_);
lean_dec_ref(v___x_4045_);
lean_dec_ref(v___x_4044_);
v_a_4089_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4080_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4080_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4097_ = _args[0];
lean_object* v___x_4098_ = _args[1];
lean_object* v_is_4099_ = _args[2];
lean_object* v_head_4100_ = _args[3];
lean_object* v_ctors_4101_ = _args[4];
lean_object* v_tail_4102_ = _args[5];
lean_object* v_params_4103_ = _args[6];
lean_object* v_numIndices_4104_ = _args[7];
lean_object* v___x_4105_ = _args[8];
lean_object* v___x_4106_ = _args[9];
lean_object* v___x_4107_ = _args[10];
lean_object* v___x_4108_ = _args[11];
lean_object* v___x_4109_ = _args[12];
lean_object* v_val_4110_ = _args[13];
lean_object* v___x_4111_ = _args[14];
lean_object* v_declName_4112_ = _args[15];
lean_object* v_levelParams_4113_ = _args[16];
lean_object* v___x_4114_ = _args[17];
lean_object* v_numParams_4115_ = _args[18];
lean_object* v___x_4116_ = _args[19];
lean_object* v_heq_4117_ = _args[20];
lean_object* v___y_4118_ = _args[21];
lean_object* v___y_4119_ = _args[22];
lean_object* v___y_4120_ = _args[23];
lean_object* v___y_4121_ = _args[24];
lean_object* v___y_4122_ = _args[25];
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4097_, v___x_4098_, v_is_4099_, v_head_4100_, v_ctors_4101_, v_tail_4102_, v_params_4103_, v_numIndices_4104_, v___x_4105_, v___x_4106_, v___x_4107_, v___x_4108_, v___x_4109_, v_val_4110_, v___x_4111_, v_declName_4112_, v_levelParams_4113_, v___x_4114_, v_numParams_4115_, v___x_4116_, v_heq_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4124_, lean_object* v_x1_4125_, lean_object* v_indName_4126_, lean_object* v_tail_4127_, lean_object* v_params_4128_, lean_object* v_is_4129_, lean_object* v___x_4130_, lean_object* v_head_4131_, lean_object* v_ctors_4132_, lean_object* v_numIndices_4133_, lean_object* v___x_4134_, lean_object* v___x_4135_, lean_object* v_val_4136_, lean_object* v_declName_4137_, lean_object* v_levelParams_4138_, lean_object* v_numParams_4139_, lean_object* v___x_4140_, lean_object* v_x2_4141_, lean_object* v_x_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; 
v___x_4148_ = lean_unsigned_to_nat(0u);
v___x_4149_ = lean_array_get_borrowed(v___x_4124_, v_x1_4125_, v___x_4148_);
v___x_4150_ = lean_array_get_borrowed(v___x_4124_, v_x2_4141_, v___x_4148_);
v___x_4151_ = l_Lean_mkCtorIdxName(v_indName_4126_);
lean_inc(v_tail_4127_);
v___x_4152_ = l_Lean_mkConst(v___x_4151_, v_tail_4127_);
lean_inc_ref(v_params_4128_);
v___x_4153_ = l_Array_append___redArg(v_params_4128_, v_is_4129_);
v___x_4154_ = lean_mk_empty_array_with_capacity(v___x_4130_);
lean_inc(v___x_4149_);
lean_inc_ref_n(v___x_4154_, 2);
v___x_4155_ = lean_array_push(v___x_4154_, v___x_4149_);
lean_inc_ref(v___x_4153_);
v___x_4156_ = l_Array_append___redArg(v___x_4153_, v___x_4155_);
lean_inc_ref(v___x_4152_);
v___x_4157_ = l_Lean_mkAppN(v___x_4152_, v___x_4156_);
lean_dec_ref(v___x_4156_);
lean_inc(v___x_4150_);
v___x_4158_ = lean_array_push(v___x_4154_, v___x_4150_);
v___x_4159_ = l_Array_append___redArg(v___x_4153_, v___x_4158_);
v___x_4160_ = l_Lean_mkAppN(v___x_4152_, v___x_4159_);
lean_dec_ref(v___x_4159_);
v___x_4161_ = l_Lean_Meta_mkEq(v___x_4157_, v___x_4160_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
if (lean_obj_tag(v___x_4161_) == 0)
{
lean_object* v_a_4162_; lean_object* v___f_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
lean_inc(v_a_4162_);
lean_dec_ref_known(v___x_4161_, 1);
lean_inc(v___x_4150_);
lean_inc(v___x_4149_);
v___f_4163_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4163_, 0, v___x_4149_);
lean_closure_set(v___f_4163_, 1, v___x_4150_);
lean_closure_set(v___f_4163_, 2, v_is_4129_);
lean_closure_set(v___f_4163_, 3, v_head_4131_);
lean_closure_set(v___f_4163_, 4, v_ctors_4132_);
lean_closure_set(v___f_4163_, 5, v_tail_4127_);
lean_closure_set(v___f_4163_, 6, v_params_4128_);
lean_closure_set(v___f_4163_, 7, v_numIndices_4133_);
lean_closure_set(v___f_4163_, 8, v___x_4130_);
lean_closure_set(v___f_4163_, 9, v___x_4134_);
lean_closure_set(v___f_4163_, 10, v___x_4135_);
lean_closure_set(v___f_4163_, 11, v___x_4155_);
lean_closure_set(v___f_4163_, 12, v___x_4158_);
lean_closure_set(v___f_4163_, 13, v_val_4136_);
lean_closure_set(v___f_4163_, 14, v___x_4154_);
lean_closure_set(v___f_4163_, 15, v_declName_4137_);
lean_closure_set(v___f_4163_, 16, v_levelParams_4138_);
lean_closure_set(v___f_4163_, 17, v___x_4148_);
lean_closure_set(v___f_4163_, 18, v_numParams_4139_);
lean_closure_set(v___f_4163_, 19, v___x_4140_);
v___x_4164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4165_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4164_, v_a_4162_, v___f_4163_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
return v___x_4165_;
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec_ref(v___x_4158_);
lean_dec_ref(v___x_4155_);
lean_dec_ref(v___x_4154_);
lean_dec_ref(v___x_4140_);
lean_dec(v_numParams_4139_);
lean_dec(v_levelParams_4138_);
lean_dec(v_declName_4137_);
lean_dec_ref(v_val_4136_);
lean_dec(v___x_4135_);
lean_dec(v___x_4134_);
lean_dec(v_numIndices_4133_);
lean_dec(v_ctors_4132_);
lean_dec(v_head_4131_);
lean_dec(v___x_4130_);
lean_dec_ref(v_is_4129_);
lean_dec_ref(v_params_4128_);
lean_dec(v_tail_4127_);
v_a_4166_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4161_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4161_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4174_ = _args[0];
lean_object* v_x1_4175_ = _args[1];
lean_object* v_indName_4176_ = _args[2];
lean_object* v_tail_4177_ = _args[3];
lean_object* v_params_4178_ = _args[4];
lean_object* v_is_4179_ = _args[5];
lean_object* v___x_4180_ = _args[6];
lean_object* v_head_4181_ = _args[7];
lean_object* v_ctors_4182_ = _args[8];
lean_object* v_numIndices_4183_ = _args[9];
lean_object* v___x_4184_ = _args[10];
lean_object* v___x_4185_ = _args[11];
lean_object* v_val_4186_ = _args[12];
lean_object* v_declName_4187_ = _args[13];
lean_object* v_levelParams_4188_ = _args[14];
lean_object* v_numParams_4189_ = _args[15];
lean_object* v___x_4190_ = _args[16];
lean_object* v_x2_4191_ = _args[17];
lean_object* v_x_4192_ = _args[18];
lean_object* v___y_4193_ = _args[19];
lean_object* v___y_4194_ = _args[20];
lean_object* v___y_4195_ = _args[21];
lean_object* v___y_4196_ = _args[22];
lean_object* v___y_4197_ = _args[23];
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4174_, v_x1_4175_, v_indName_4176_, v_tail_4177_, v_params_4178_, v_is_4179_, v___x_4180_, v_head_4181_, v_ctors_4182_, v_numIndices_4183_, v___x_4184_, v___x_4185_, v_val_4186_, v_declName_4187_, v_levelParams_4188_, v_numParams_4189_, v___x_4190_, v_x2_4191_, v_x_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec_ref(v_x_4192_);
lean_dec_ref(v_x2_4191_);
lean_dec_ref(v_x1_4175_);
lean_dec_ref(v___x_4174_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4199_, lean_object* v_indName_4200_, lean_object* v_tail_4201_, lean_object* v_params_4202_, lean_object* v_is_4203_, lean_object* v___x_4204_, lean_object* v_head_4205_, lean_object* v_ctors_4206_, lean_object* v_numIndices_4207_, lean_object* v___x_4208_, lean_object* v___x_4209_, lean_object* v_val_4210_, lean_object* v_declName_4211_, lean_object* v_levelParams_4212_, lean_object* v_numParams_4213_, lean_object* v___x_4214_, lean_object* v_t_4215_, lean_object* v___x_4216_, lean_object* v_x1_4217_, lean_object* v_x_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v___f_4224_; uint8_t v___x_4225_; lean_object* v___x_4226_; 
v___f_4224_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4224_, 0, v___x_4199_);
lean_closure_set(v___f_4224_, 1, v_x1_4217_);
lean_closure_set(v___f_4224_, 2, v_indName_4200_);
lean_closure_set(v___f_4224_, 3, v_tail_4201_);
lean_closure_set(v___f_4224_, 4, v_params_4202_);
lean_closure_set(v___f_4224_, 5, v_is_4203_);
lean_closure_set(v___f_4224_, 6, v___x_4204_);
lean_closure_set(v___f_4224_, 7, v_head_4205_);
lean_closure_set(v___f_4224_, 8, v_ctors_4206_);
lean_closure_set(v___f_4224_, 9, v_numIndices_4207_);
lean_closure_set(v___f_4224_, 10, v___x_4208_);
lean_closure_set(v___f_4224_, 11, v___x_4209_);
lean_closure_set(v___f_4224_, 12, v_val_4210_);
lean_closure_set(v___f_4224_, 13, v_declName_4211_);
lean_closure_set(v___f_4224_, 14, v_levelParams_4212_);
lean_closure_set(v___f_4224_, 15, v_numParams_4213_);
lean_closure_set(v___f_4224_, 16, v___x_4214_);
v___x_4225_ = 0;
v___x_4226_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4215_, v___x_4216_, v___f_4224_, v___x_4225_, v___x_4225_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4227_ = _args[0];
lean_object* v_indName_4228_ = _args[1];
lean_object* v_tail_4229_ = _args[2];
lean_object* v_params_4230_ = _args[3];
lean_object* v_is_4231_ = _args[4];
lean_object* v___x_4232_ = _args[5];
lean_object* v_head_4233_ = _args[6];
lean_object* v_ctors_4234_ = _args[7];
lean_object* v_numIndices_4235_ = _args[8];
lean_object* v___x_4236_ = _args[9];
lean_object* v___x_4237_ = _args[10];
lean_object* v_val_4238_ = _args[11];
lean_object* v_declName_4239_ = _args[12];
lean_object* v_levelParams_4240_ = _args[13];
lean_object* v_numParams_4241_ = _args[14];
lean_object* v___x_4242_ = _args[15];
lean_object* v_t_4243_ = _args[16];
lean_object* v___x_4244_ = _args[17];
lean_object* v_x1_4245_ = _args[18];
lean_object* v_x_4246_ = _args[19];
lean_object* v___y_4247_ = _args[20];
lean_object* v___y_4248_ = _args[21];
lean_object* v___y_4249_ = _args[22];
lean_object* v___y_4250_ = _args[23];
lean_object* v___y_4251_ = _args[24];
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4227_, v_indName_4228_, v_tail_4229_, v_params_4230_, v_is_4231_, v___x_4232_, v_head_4233_, v_ctors_4234_, v_numIndices_4235_, v___x_4236_, v___x_4237_, v_val_4238_, v_declName_4239_, v_levelParams_4240_, v_numParams_4241_, v___x_4242_, v_t_4243_, v___x_4244_, v_x1_4245_, v_x_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec_ref(v_x_4246_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4253_, lean_object* v_indName_4254_, lean_object* v_tail_4255_, lean_object* v_params_4256_, lean_object* v_head_4257_, lean_object* v_ctors_4258_, lean_object* v_numIndices_4259_, lean_object* v___x_4260_, lean_object* v___x_4261_, lean_object* v_val_4262_, lean_object* v_declName_4263_, lean_object* v_levelParams_4264_, lean_object* v_numParams_4265_, lean_object* v___x_4266_, lean_object* v_is_4267_, lean_object* v_t_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___f_4276_; uint8_t v___x_4277_; lean_object* v___x_4278_; 
v___x_4274_ = lean_unsigned_to_nat(1u);
v___x_4275_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4268_);
v___f_4276_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4276_, 0, v___x_4253_);
lean_closure_set(v___f_4276_, 1, v_indName_4254_);
lean_closure_set(v___f_4276_, 2, v_tail_4255_);
lean_closure_set(v___f_4276_, 3, v_params_4256_);
lean_closure_set(v___f_4276_, 4, v_is_4267_);
lean_closure_set(v___f_4276_, 5, v___x_4274_);
lean_closure_set(v___f_4276_, 6, v_head_4257_);
lean_closure_set(v___f_4276_, 7, v_ctors_4258_);
lean_closure_set(v___f_4276_, 8, v_numIndices_4259_);
lean_closure_set(v___f_4276_, 9, v___x_4260_);
lean_closure_set(v___f_4276_, 10, v___x_4261_);
lean_closure_set(v___f_4276_, 11, v_val_4262_);
lean_closure_set(v___f_4276_, 12, v_declName_4263_);
lean_closure_set(v___f_4276_, 13, v_levelParams_4264_);
lean_closure_set(v___f_4276_, 14, v_numParams_4265_);
lean_closure_set(v___f_4276_, 15, v___x_4266_);
lean_closure_set(v___f_4276_, 16, v_t_4268_);
lean_closure_set(v___f_4276_, 17, v___x_4275_);
v___x_4277_ = 0;
v___x_4278_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4268_, v___x_4275_, v___f_4276_, v___x_4277_, v___x_4277_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
return v___x_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4279_ = _args[0];
lean_object* v_indName_4280_ = _args[1];
lean_object* v_tail_4281_ = _args[2];
lean_object* v_params_4282_ = _args[3];
lean_object* v_head_4283_ = _args[4];
lean_object* v_ctors_4284_ = _args[5];
lean_object* v_numIndices_4285_ = _args[6];
lean_object* v___x_4286_ = _args[7];
lean_object* v___x_4287_ = _args[8];
lean_object* v_val_4288_ = _args[9];
lean_object* v_declName_4289_ = _args[10];
lean_object* v_levelParams_4290_ = _args[11];
lean_object* v_numParams_4291_ = _args[12];
lean_object* v___x_4292_ = _args[13];
lean_object* v_is_4293_ = _args[14];
lean_object* v_t_4294_ = _args[15];
lean_object* v___y_4295_ = _args[16];
lean_object* v___y_4296_ = _args[17];
lean_object* v___y_4297_ = _args[18];
lean_object* v___y_4298_ = _args[19];
lean_object* v___y_4299_ = _args[20];
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4279_, v_indName_4280_, v_tail_4281_, v_params_4282_, v_head_4283_, v_ctors_4284_, v_numIndices_4285_, v___x_4286_, v___x_4287_, v_val_4288_, v_declName_4289_, v_levelParams_4290_, v_numParams_4291_, v___x_4292_, v_is_4293_, v_t_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4301_, lean_object* v_indName_4302_, lean_object* v_tail_4303_, lean_object* v_head_4304_, lean_object* v_ctors_4305_, lean_object* v_numIndices_4306_, lean_object* v___x_4307_, lean_object* v___x_4308_, lean_object* v_val_4309_, lean_object* v_declName_4310_, lean_object* v_levelParams_4311_, lean_object* v_numParams_4312_, lean_object* v_params_4313_, lean_object* v_t_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
lean_object* v___x_4320_; lean_object* v___f_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; lean_object* v___x_4324_; 
v___x_4320_ = l_Lean_Expr_bindingBody_x21(v_t_4314_);
lean_inc_ref(v___x_4320_);
lean_inc(v_numIndices_4306_);
v___f_4321_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4321_, 0, v___x_4301_);
lean_closure_set(v___f_4321_, 1, v_indName_4302_);
lean_closure_set(v___f_4321_, 2, v_tail_4303_);
lean_closure_set(v___f_4321_, 3, v_params_4313_);
lean_closure_set(v___f_4321_, 4, v_head_4304_);
lean_closure_set(v___f_4321_, 5, v_ctors_4305_);
lean_closure_set(v___f_4321_, 6, v_numIndices_4306_);
lean_closure_set(v___f_4321_, 7, v___x_4307_);
lean_closure_set(v___f_4321_, 8, v___x_4308_);
lean_closure_set(v___f_4321_, 9, v_val_4309_);
lean_closure_set(v___f_4321_, 10, v_declName_4310_);
lean_closure_set(v___f_4321_, 11, v_levelParams_4311_);
lean_closure_set(v___f_4321_, 12, v_numParams_4312_);
lean_closure_set(v___f_4321_, 13, v___x_4320_);
v___x_4322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4322_, 0, v_numIndices_4306_);
v___x_4323_ = 0;
v___x_4324_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4320_, v___x_4322_, v___f_4321_, v___x_4323_, v___x_4323_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
return v___x_4324_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4325_ = _args[0];
lean_object* v_indName_4326_ = _args[1];
lean_object* v_tail_4327_ = _args[2];
lean_object* v_head_4328_ = _args[3];
lean_object* v_ctors_4329_ = _args[4];
lean_object* v_numIndices_4330_ = _args[5];
lean_object* v___x_4331_ = _args[6];
lean_object* v___x_4332_ = _args[7];
lean_object* v_val_4333_ = _args[8];
lean_object* v_declName_4334_ = _args[9];
lean_object* v_levelParams_4335_ = _args[10];
lean_object* v_numParams_4336_ = _args[11];
lean_object* v_params_4337_ = _args[12];
lean_object* v_t_4338_ = _args[13];
lean_object* v___y_4339_ = _args[14];
lean_object* v___y_4340_ = _args[15];
lean_object* v___y_4341_ = _args[16];
lean_object* v___y_4342_ = _args[17];
lean_object* v___y_4343_ = _args[18];
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4325_, v_indName_4326_, v_tail_4327_, v_head_4328_, v_ctors_4329_, v_numIndices_4330_, v___x_4331_, v___x_4332_, v_val_4333_, v_declName_4334_, v_levelParams_4335_, v_numParams_4336_, v_params_4337_, v_t_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec_ref(v_t_4338_);
return v_res_4344_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v___x_4349_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4350_ = lean_unsigned_to_nat(58u);
v___x_4351_ = lean_unsigned_to_nat(142u);
v___x_4352_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4353_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4354_ = l_mkPanicMessageWithDecl(v___x_4353_, v___x_4352_, v___x_4351_, v___x_4350_, v___x_4349_);
return v___x_4354_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4355_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4356_ = lean_unsigned_to_nat(60u);
v___x_4357_ = lean_unsigned_to_nat(136u);
v___x_4358_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4359_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4360_ = l_mkPanicMessageWithDecl(v___x_4359_, v___x_4358_, v___x_4357_, v___x_4356_, v___x_4355_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4361_, lean_object* v_indName_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_){
_start:
{
lean_object* v___x_4368_; 
lean_inc(v_indName_4362_);
v___x_4368_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v_a_4369_; 
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
lean_inc(v_a_4369_);
lean_dec_ref_known(v___x_4368_, 1);
if (lean_obj_tag(v_a_4369_) == 5)
{
lean_object* v_val_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v_val_4370_ = lean_ctor_get(v_a_4369_, 0);
lean_inc_ref(v_val_4370_);
lean_dec_ref_known(v_a_4369_, 1);
v___x_4371_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4361_);
v___x_4372_ = l_Lean_Name_append(v_declName_4361_, v___x_4371_);
lean_inc(v_indName_4362_);
lean_inc(v___x_4372_);
v___x_4373_ = l_Lean_mkCasesOnSameCtorHet(v___x_4372_, v_indName_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4406_; 
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4406_ == 0)
{
lean_object* v_unused_4407_; 
v_unused_4407_ = lean_ctor_get(v___x_4373_, 0);
lean_dec(v_unused_4407_);
v___x_4375_ = v___x_4373_;
v_isShared_4376_ = v_isSharedCheck_4406_;
goto v_resetjp_4374_;
}
else
{
lean_dec(v___x_4373_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4406_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; 
lean_inc(v_indName_4362_);
v___x_4377_ = l_Lean_mkCasesOnName(v_indName_4362_);
v___x_4378_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4377_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; lean_object* v_levelParams_4380_; lean_object* v_type_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref_known(v___x_4378_, 1);
v_levelParams_4380_ = lean_ctor_get(v_a_4379_, 1);
lean_inc_n(v_levelParams_4380_, 2);
v_type_4381_ = lean_ctor_get(v_a_4379_, 2);
lean_inc_ref(v_type_4381_);
lean_dec(v_a_4379_);
v___x_4382_ = lean_box(0);
v___x_4383_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4380_, v___x_4382_);
if (lean_obj_tag(v___x_4383_) == 1)
{
lean_object* v_head_4384_; lean_object* v_tail_4385_; lean_object* v_numParams_4386_; lean_object* v_numIndices_4387_; lean_object* v_ctors_4388_; lean_object* v___x_4389_; lean_object* v___f_4390_; lean_object* v___x_4392_; 
v_head_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc(v_head_4384_);
v_tail_4385_ = lean_ctor_get(v___x_4383_, 1);
lean_inc(v_tail_4385_);
v_numParams_4386_ = lean_ctor_get(v_val_4370_, 1);
lean_inc_n(v_numParams_4386_, 2);
v_numIndices_4387_ = lean_ctor_get(v_val_4370_, 2);
lean_inc(v_numIndices_4387_);
v_ctors_4388_ = lean_ctor_get(v_val_4370_, 4);
lean_inc(v_ctors_4388_);
v___x_4389_ = l_Lean_instInhabitedExpr;
v___f_4390_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4390_, 0, v___x_4389_);
lean_closure_set(v___f_4390_, 1, v_indName_4362_);
lean_closure_set(v___f_4390_, 2, v_tail_4385_);
lean_closure_set(v___f_4390_, 3, v_head_4384_);
lean_closure_set(v___f_4390_, 4, v_ctors_4388_);
lean_closure_set(v___f_4390_, 5, v_numIndices_4387_);
lean_closure_set(v___f_4390_, 6, v___x_4372_);
lean_closure_set(v___f_4390_, 7, v___x_4383_);
lean_closure_set(v___f_4390_, 8, v_val_4370_);
lean_closure_set(v___f_4390_, 9, v_declName_4361_);
lean_closure_set(v___f_4390_, 10, v_levelParams_4380_);
lean_closure_set(v___f_4390_, 11, v_numParams_4386_);
if (v_isShared_4376_ == 0)
{
lean_ctor_set_tag(v___x_4375_, 1);
lean_ctor_set(v___x_4375_, 0, v_numParams_4386_);
v___x_4392_ = v___x_4375_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_numParams_4386_);
v___x_4392_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
uint8_t v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = 0;
v___x_4394_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4381_, v___x_4392_, v___f_4390_, v___x_4393_, v___x_4393_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
return v___x_4394_;
}
}
else
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
lean_dec(v___x_4383_);
lean_dec_ref(v_type_4381_);
lean_dec(v_levelParams_4380_);
lean_del_object(v___x_4375_);
lean_dec(v___x_4372_);
lean_dec_ref(v_val_4370_);
lean_dec(v_indName_4362_);
lean_dec(v_declName_4361_);
v___x_4396_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4397_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4396_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
return v___x_4397_;
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
lean_del_object(v___x_4375_);
lean_dec(v___x_4372_);
lean_dec_ref(v_val_4370_);
lean_dec(v_indName_4362_);
lean_dec(v_declName_4361_);
v_a_4398_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4378_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4378_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
else
{
lean_dec(v___x_4372_);
lean_dec_ref(v_val_4370_);
lean_dec(v_indName_4362_);
lean_dec(v_declName_4361_);
return v___x_4373_;
}
}
else
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
lean_dec(v_a_4369_);
lean_dec(v_indName_4362_);
lean_dec(v_declName_4361_);
v___x_4408_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4409_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4408_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_);
return v___x_4409_;
}
}
else
{
lean_object* v_a_4410_; lean_object* v___x_4412_; uint8_t v_isShared_4413_; uint8_t v_isSharedCheck_4417_; 
lean_dec(v_indName_4362_);
lean_dec(v_declName_4361_);
v_a_4410_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4417_ == 0)
{
v___x_4412_ = v___x_4368_;
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
else
{
lean_inc(v_a_4410_);
lean_dec(v___x_4368_);
v___x_4412_ = lean_box(0);
v_isShared_4413_ = v_isSharedCheck_4417_;
goto v_resetjp_4411_;
}
v_resetjp_4411_:
{
lean_object* v___x_4415_; 
if (v_isShared_4413_ == 0)
{
v___x_4415_ = v___x_4412_;
goto v_reusejp_4414_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_a_4410_);
v___x_4415_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4414_;
}
v_reusejp_4414_:
{
return v___x_4415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4418_, lean_object* v_indName_4419_, lean_object* v_a_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_){
_start:
{
lean_object* v_res_4425_; 
v_res_4425_ = l_Lean_mkCasesOnSameCtor(v_declName_4418_, v_indName_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_);
lean_dec(v_a_4423_);
lean_dec_ref(v_a_4422_);
lean_dec(v_a_4421_);
lean_dec_ref(v_a_4420_);
return v_res_4425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4426_, lean_object* v_params_4427_, lean_object* v_motive_4428_, lean_object* v_as_4429_, size_t v_sz_4430_, size_t v_i_4431_, lean_object* v_bs_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v___x_4438_; 
v___x_4438_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4426_, v_params_4427_, v_motive_4428_, v_sz_4430_, v_i_4431_, v_bs_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4439_, lean_object* v_params_4440_, lean_object* v_motive_4441_, lean_object* v_as_4442_, lean_object* v_sz_4443_, lean_object* v_i_4444_, lean_object* v_bs_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
size_t v_sz_boxed_4451_; size_t v_i_boxed_4452_; lean_object* v_res_4453_; 
v_sz_boxed_4451_ = lean_unbox_usize(v_sz_4443_);
lean_dec(v_sz_4443_);
v_i_boxed_4452_ = lean_unbox_usize(v_i_4444_);
lean_dec(v_i_4444_);
v_res_4453_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4439_, v_params_4440_, v_motive_4441_, v_as_4442_, v_sz_boxed_4451_, v_i_boxed_4452_, v_bs_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec_ref(v_as_4442_);
lean_dec_ref(v_params_4440_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4454_, lean_object* v_params_4455_, lean_object* v_a_4456_, lean_object* v_snd_4457_, lean_object* v_alts_4458_, lean_object* v_as_4459_, size_t v_sz_4460_, size_t v_i_4461_, lean_object* v_bs_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4454_, v_params_4455_, v_a_4456_, v_snd_4457_, v_alts_4458_, v_sz_4460_, v_i_4461_, v_bs_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4469_, lean_object* v_params_4470_, lean_object* v_a_4471_, lean_object* v_snd_4472_, lean_object* v_alts_4473_, lean_object* v_as_4474_, lean_object* v_sz_4475_, lean_object* v_i_4476_, lean_object* v_bs_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
size_t v_sz_boxed_4483_; size_t v_i_boxed_4484_; lean_object* v_res_4485_; 
v_sz_boxed_4483_ = lean_unbox_usize(v_sz_4475_);
lean_dec(v_sz_4475_);
v_i_boxed_4484_ = lean_unbox_usize(v_i_4476_);
lean_dec(v_i_4476_);
v_res_4485_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4469_, v_params_4470_, v_a_4471_, v_snd_4472_, v_alts_4473_, v_as_4474_, v_sz_boxed_4483_, v_i_boxed_4484_, v_bs_4477_, v___y_4478_, v___y_4479_, v___y_4480_, v___y_4481_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
lean_dec(v___y_4479_);
lean_dec_ref(v___y_4478_);
lean_dec_ref(v_as_4474_);
lean_dec_ref(v_params_4470_);
return v_res_4485_;
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
