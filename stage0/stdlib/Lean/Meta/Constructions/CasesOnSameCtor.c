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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_345_; lean_object* v_env_346_; uint8_t v_isExporting_347_; uint8_t v___y_414_; lean_object* v___x_416_; uint8_t v_isModule_417_; uint8_t v___x_418_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_346_);
lean_dec(v___x_345_);
v_isExporting_347_ = lean_ctor_get_uint8(v_env_346_, sizeof(void*)*8);
v___x_416_ = l_Lean_Environment_header(v_env_346_);
lean_dec_ref(v_env_346_);
v_isModule_417_ = lean_ctor_get_uint8(v___x_416_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_416_);
v___x_418_ = lean_bool_not(v_isModule_417_);
if (v___x_418_ == 0)
{
if (v_isExporting_347_ == 0)
{
if (v_isExporting_339_ == 0)
{
lean_object* v___x_419_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v___x_419_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
return v___x_419_;
}
else
{
goto v___jp_348_;
}
}
else
{
v___y_414_ = v_isExporting_339_;
goto v___jp_413_;
}
}
else
{
v___y_414_ = v___x_418_;
goto v___jp_413_;
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
v___jp_413_:
{
if (v___y_414_ == 0)
{
goto v___jp_348_;
}
else
{
lean_object* v___x_415_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v___x_415_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
return v___x_415_;
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
lean_object* v___f_455_; lean_object* v___x_15652__overap_456_; lean_object* v___x_457_; 
v___f_455_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15652__overap_456_ = lean_panic_fn_borrowed(v___f_455_, v_msg_449_);
lean_inc(v___y_453_);
lean_inc_ref(v___y_452_);
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
v___x_457_ = lean_apply_5(v___x_15652__overap_456_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, lean_box(0));
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
uint8_t v___x_20772__boxed_561_; uint8_t v___x_20773__boxed_562_; uint8_t v___x_20774__boxed_563_; lean_object* v_res_564_; 
v___x_20772__boxed_561_ = lean_unbox(v___x_542_);
v___x_20773__boxed_562_ = lean_unbox(v___x_543_);
v___x_20774__boxed_563_ = lean_unbox(v___x_544_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_539_, v_ism2_540_, v_motive_541_, v___x_20772__boxed_561_, v___x_20773__boxed_562_, v___x_20774__boxed_563_, v_a_545_, v___f_546_, v_zs1_547_, v_val_548_, v___x_549_, v_indName_550_, v_v_551_, v___x_552_, v_params_553_, v___x_554_, v_h_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
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
uint8_t v___x_20884__boxed_597_; uint8_t v___x_20885__boxed_598_; uint8_t v___x_20886__boxed_599_; lean_object* v_res_600_; 
v___x_20884__boxed_597_ = lean_unbox(v___x_587_);
v___x_20885__boxed_598_ = lean_unbox(v___x_588_);
v___x_20886__boxed_599_ = lean_unbox(v___x_589_);
v_res_600_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_583_, v_alts_584_, v___x_585_, v_zs1_586_, v___x_20884__boxed_597_, v___x_20885__boxed_598_, v___x_20886__boxed_599_, v_zs2_590_, v_x_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
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
lean_object* v___x_639_; 
lean_inc(v___y_637_);
lean_inc_ref(v___y_636_);
lean_inc(v___y_635_);
lean_inc_ref(v___y_634_);
v___x_639_ = lean_whnf(v_ctorRet1_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___f_644_; lean_object* v___x_645_; lean_object* v_dummy_646_; lean_object* v_nargs_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___f_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_641_ = lean_box(v___x_615_);
v___x_642_ = lean_box(v___x_616_);
v___x_643_ = lean_box(v___x_617_);
lean_inc_ref(v_zs1_632_);
lean_inc(v___x_614_);
v___f_644_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_644_, 0, v___x_612_);
lean_closure_set(v___f_644_, 1, v_alts_613_);
lean_closure_set(v___f_644_, 2, v___x_614_);
lean_closure_set(v___f_644_, 3, v_zs1_632_);
lean_closure_set(v___f_644_, 4, v___x_641_);
lean_closure_set(v___f_644_, 5, v___x_642_);
lean_closure_set(v___f_644_, 6, v___x_643_);
v___x_645_ = l_Lean_mkAppN(v___x_618_, v_zs1_632_);
v_dummy_646_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_647_ = l_Lean_Expr_getAppNumArgs(v_a_640_);
lean_inc(v_nargs_647_);
v___x_648_ = lean_mk_array(v_nargs_647_, v_dummy_646_);
v___x_649_ = lean_nat_sub(v_nargs_647_, v___x_619_);
lean_dec(v_nargs_647_);
v___x_650_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_640_, v___x_648_, v___x_649_);
v___x_651_ = lean_array_get_size(v___x_650_);
v___x_652_ = l_Array_toSubarray___redArg(v___x_650_, v___x_620_, v___x_651_);
v___x_653_ = l_Subarray_copy___redArg(v___x_652_);
v___x_654_ = lean_array_push(v___x_653_, v___x_645_);
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
lean_closure_set(v___f_658_, 7, v___f_644_);
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
lean_dec_ref(v___x_618_);
lean_dec(v___x_614_);
lean_dec_ref(v_alts_613_);
lean_dec_ref(v___x_612_);
return v___x_639_;
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
uint8_t v___x_20945__boxed_695_; uint8_t v___x_20946__boxed_696_; uint8_t v___x_20947__boxed_697_; lean_object* v_res_698_; 
v___x_20945__boxed_695_ = lean_unbox(v___x_671_);
v___x_20946__boxed_696_ = lean_unbox(v___x_672_);
v___x_20947__boxed_697_ = lean_unbox(v___x_673_);
v_res_698_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_668_, v_alts_669_, v___x_670_, v___x_20945__boxed_695_, v___x_20946__boxed_696_, v___x_20947__boxed_697_, v___x_674_, v___x_675_, v___x_676_, v_ism2_677_, v_motive_678_, v_a_679_, v_val_680_, v_indName_681_, v_v_682_, v___x_683_, v_params_684_, v___x_685_, v___x_686_, v___x_687_, v_zs1_688_, v_ctorRet1_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
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
lean_object* v_v_723_; lean_object* v___x_724_; lean_object* v_bs_x27_725_; lean_object* v___y_727_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_v_723_ = lean_array_uget(v_bs_715_, v_i_714_);
v___x_724_ = lean_unsigned_to_nat(0u);
v_bs_x27_725_ = lean_array_uset(v_bs_715_, v_i_714_, v___x_724_);
lean_inc(v_tail_702_);
lean_inc(v_v_723_);
v___x_741_ = l_Lean_mkConst(v_v_723_, v_tail_702_);
v___x_742_ = l_Lean_mkAppN(v___x_741_, v_params_703_);
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc_ref(v___x_742_);
v___x_743_ = lean_infer_type(v___x_742_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_745_; uint8_t v___x_746_; uint8_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___f_754_; lean_object* v___x_755_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc_n(v_a_744_, 2);
lean_dec_ref_known(v___x_743_, 1);
v___x_745_ = l_Lean_instInhabitedExpr;
v___x_746_ = 0;
v___x_747_ = 1;
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_750_ = lean_usize_to_nat(v_i_714_);
v___x_751_ = lean_box(v___x_746_);
v___x_752_ = lean_box(v___x_721_);
v___x_753_ = lean_box(v___x_747_);
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
lean_closure_set(v___f_754_, 0, v___x_745_);
lean_closure_set(v___f_754_, 1, v_alts_704_);
lean_closure_set(v___f_754_, 2, v___x_750_);
lean_closure_set(v___f_754_, 3, v___x_751_);
lean_closure_set(v___f_754_, 4, v___x_752_);
lean_closure_set(v___f_754_, 5, v___x_753_);
lean_closure_set(v___f_754_, 6, v___x_742_);
lean_closure_set(v___f_754_, 7, v___x_748_);
lean_closure_set(v___f_754_, 8, v___x_705_);
lean_closure_set(v___f_754_, 9, v_ism2_706_);
lean_closure_set(v___f_754_, 10, v_motive_707_);
lean_closure_set(v___f_754_, 11, v_a_744_);
lean_closure_set(v___f_754_, 12, v_val_708_);
lean_closure_set(v___f_754_, 13, v_indName_709_);
lean_closure_set(v___f_754_, 14, v_v_723_);
lean_closure_set(v___f_754_, 15, v___x_710_);
lean_closure_set(v___f_754_, 16, v_params_703_);
lean_closure_set(v___f_754_, 17, v___x_711_);
lean_closure_set(v___f_754_, 18, v___x_712_);
lean_closure_set(v___f_754_, 19, v___x_749_);
v___x_755_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_744_, v___f_754_, v___x_746_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
v___y_727_ = v___x_755_;
goto v___jp_726_;
}
else
{
lean_dec_ref(v___x_742_);
lean_dec(v_v_723_);
v___y_727_ = v___x_743_;
goto v___jp_726_;
}
v___jp_726_:
{
if (lean_obj_tag(v___y_727_) == 0)
{
lean_object* v_a_728_; size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
v_a_728_ = lean_ctor_get(v___y_727_, 0);
lean_inc(v_a_728_);
lean_dec_ref_known(v___y_727_, 1);
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_i_714_, v___x_729_);
v___x_731_ = lean_array_uset(v_bs_x27_725_, v_i_714_, v_a_728_);
v_i_714_ = v___x_730_;
v_bs_715_ = v___x_731_;
goto _start;
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec_ref(v_bs_x27_725_);
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
v_a_733_ = lean_ctor_get(v___y_727_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___y_727_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___y_727_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___y_727_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
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
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_778_, lean_object* v___x_779_, lean_object* v_a_780_, lean_object* v_ism1_781_, uint8_t v___x_782_, uint8_t v___x_783_, uint8_t v___x_784_, lean_object* v___x_785_, lean_object* v_tail_786_, lean_object* v_params_787_, lean_object* v_alts_788_, lean_object* v_numParams_789_, lean_object* v_ism2_790_, lean_object* v_val_791_, lean_object* v_indName_792_, lean_object* v___x_793_, lean_object* v___x_794_, lean_object* v___x_795_, lean_object* v_name_796_, lean_object* v___x_797_, lean_object* v_heq_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
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
lean_object* v_a_808_; size_t v_sz_809_; size_t v___x_810_; lean_object* v___x_811_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v_sz_809_ = lean_array_size(v___x_785_);
v___x_810_ = ((size_t)0ULL);
lean_inc(v___x_793_);
lean_inc_ref(v_motive_778_);
lean_inc_ref(v_ism2_790_);
lean_inc_ref(v_alts_788_);
lean_inc_ref(v_params_787_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_786_, v_params_787_, v_alts_788_, v_numParams_789_, v_ism2_790_, v_motive_778_, v_val_791_, v_indName_792_, v___x_793_, v___x_794_, v___x_795_, v_sz_809_, v___x_810_, v___x_785_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
lean_inc_ref(v_heq_798_);
v___x_813_ = l_Lean_Meta_mkEqSymm(v_heq_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref_known(v___x_813_, 1);
v___x_815_ = l_Lean_mkConst(v_name_796_, v___x_793_);
v___x_816_ = l_Lean_mkAppN(v___x_815_, v_params_787_);
v___x_817_ = l_Lean_Expr_app___override(v___x_816_, v_a_808_);
v___x_818_ = l_Lean_mkAppN(v___x_817_, v_ism1_781_);
v___x_819_ = l_Lean_mkAppN(v___x_818_, v_a_812_);
lean_dec(v_a_812_);
v___x_820_ = l_Lean_Expr_app___override(v___x_819_, v_a_814_);
v___x_821_ = lean_mk_empty_array_with_capacity(v___x_797_);
lean_inc_ref(v___x_821_);
v___x_822_ = lean_array_push(v___x_821_, v_motive_778_);
v___x_823_ = l_Array_append___redArg(v_params_787_, v___x_822_);
lean_dec_ref(v___x_822_);
v___x_824_ = l_Array_append___redArg(v___x_823_, v_ism1_781_);
v___x_825_ = l_Array_append___redArg(v___x_824_, v_ism2_790_);
lean_dec_ref(v_ism2_790_);
v___x_826_ = lean_array_push(v___x_821_, v_heq_798_);
v___x_827_ = l_Array_append___redArg(v___x_825_, v___x_826_);
lean_dec_ref(v___x_826_);
v___x_828_ = l_Array_append___redArg(v___x_827_, v_alts_788_);
lean_dec_ref(v_alts_788_);
v___x_829_ = l_Lean_Meta_mkLambdaFVars(v___x_828_, v___x_820_, v___x_782_, v___x_783_, v___x_782_, v___x_783_, v___x_784_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec_ref(v___x_828_);
return v___x_829_;
}
else
{
lean_dec(v_a_812_);
lean_dec(v_a_808_);
lean_dec_ref(v_heq_798_);
lean_dec(v_name_796_);
lean_dec(v___x_793_);
lean_dec_ref(v_ism2_790_);
lean_dec_ref(v_alts_788_);
lean_dec_ref(v_params_787_);
lean_dec_ref(v_motive_778_);
return v___x_813_;
}
}
else
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_837_; 
lean_dec(v_a_808_);
lean_dec_ref(v_heq_798_);
lean_dec(v_name_796_);
lean_dec(v___x_793_);
lean_dec_ref(v_ism2_790_);
lean_dec_ref(v_alts_788_);
lean_dec_ref(v_params_787_);
lean_dec_ref(v_motive_778_);
v_a_830_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_837_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_837_ == 0)
{
v___x_832_ = v___x_811_;
v_isShared_833_ = v_isSharedCheck_837_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_811_);
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
lean_dec(v_name_796_);
lean_dec_ref(v___x_795_);
lean_dec(v___x_794_);
lean_dec(v___x_793_);
lean_dec(v_indName_792_);
lean_dec_ref(v_val_791_);
lean_dec_ref(v_ism2_790_);
lean_dec(v_numParams_789_);
lean_dec_ref(v_alts_788_);
lean_dec_ref(v_params_787_);
lean_dec(v_tail_786_);
lean_dec_ref(v___x_785_);
lean_dec_ref(v_motive_778_);
return v___x_807_;
}
}
else
{
lean_dec_ref(v_heq_798_);
lean_dec(v_name_796_);
lean_dec_ref(v___x_795_);
lean_dec(v___x_794_);
lean_dec(v___x_793_);
lean_dec(v_indName_792_);
lean_dec_ref(v_val_791_);
lean_dec_ref(v_ism2_790_);
lean_dec(v_numParams_789_);
lean_dec_ref(v_alts_788_);
lean_dec_ref(v_params_787_);
lean_dec(v_tail_786_);
lean_dec_ref(v___x_785_);
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
lean_object* v___x_845_ = _args[7];
lean_object* v_tail_846_ = _args[8];
lean_object* v_params_847_ = _args[9];
lean_object* v_alts_848_ = _args[10];
lean_object* v_numParams_849_ = _args[11];
lean_object* v_ism2_850_ = _args[12];
lean_object* v_val_851_ = _args[13];
lean_object* v_indName_852_ = _args[14];
lean_object* v___x_853_ = _args[15];
lean_object* v___x_854_ = _args[16];
lean_object* v___x_855_ = _args[17];
lean_object* v_name_856_ = _args[18];
lean_object* v___x_857_ = _args[19];
lean_object* v_heq_858_ = _args[20];
lean_object* v___y_859_ = _args[21];
lean_object* v___y_860_ = _args[22];
lean_object* v___y_861_ = _args[23];
lean_object* v___y_862_ = _args[24];
lean_object* v___y_863_ = _args[25];
_start:
{
uint8_t v___x_21176__boxed_864_; uint8_t v___x_21177__boxed_865_; uint8_t v___x_21178__boxed_866_; lean_object* v_res_867_; 
v___x_21176__boxed_864_ = lean_unbox(v___x_842_);
v___x_21177__boxed_865_ = lean_unbox(v___x_843_);
v___x_21178__boxed_866_ = lean_unbox(v___x_844_);
v_res_867_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_838_, v___x_839_, v_a_840_, v_ism1_841_, v___x_21176__boxed_864_, v___x_21177__boxed_865_, v___x_21178__boxed_866_, v___x_845_, v_tail_846_, v_params_847_, v_alts_848_, v_numParams_849_, v_ism2_850_, v_val_851_, v_indName_852_, v___x_853_, v___x_854_, v___x_855_, v_name_856_, v___x_857_, v_heq_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
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
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_868_, lean_object* v_tail_869_, lean_object* v_params_870_, lean_object* v_ism1_871_, lean_object* v_ism2_872_, lean_object* v_motive_873_, lean_object* v___x_874_, uint8_t v___x_875_, uint8_t v___x_876_, uint8_t v___x_877_, lean_object* v___x_878_, lean_object* v_numParams_879_, lean_object* v_val_880_, lean_object* v___x_881_, lean_object* v___x_882_, lean_object* v_name_883_, lean_object* v___x_884_, lean_object* v_alts_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
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
lean_closure_set(v___f_904_, 7, v___x_878_);
lean_closure_set(v___f_904_, 8, v_tail_869_);
lean_closure_set(v___f_904_, 9, v_params_870_);
lean_closure_set(v___f_904_, 10, v_alts_885_);
lean_closure_set(v___f_904_, 11, v_numParams_879_);
lean_closure_set(v___f_904_, 12, v_ism2_872_);
lean_closure_set(v___f_904_, 13, v_val_880_);
lean_closure_set(v___f_904_, 14, v_indName_868_);
lean_closure_set(v___f_904_, 15, v___x_881_);
lean_closure_set(v___f_904_, 16, v___x_882_);
lean_closure_set(v___f_904_, 17, v___x_896_);
lean_closure_set(v___f_904_, 18, v_name_883_);
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
lean_dec(v_name_883_);
lean_dec(v___x_882_);
lean_dec(v___x_881_);
lean_dec_ref(v_val_880_);
lean_dec(v_numParams_879_);
lean_dec_ref(v___x_878_);
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
lean_dec(v_name_883_);
lean_dec(v___x_882_);
lean_dec(v___x_881_);
lean_dec_ref(v_val_880_);
lean_dec(v_numParams_879_);
lean_dec_ref(v___x_878_);
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
lean_object* v___x_917_ = _args[10];
lean_object* v_numParams_918_ = _args[11];
lean_object* v_val_919_ = _args[12];
lean_object* v___x_920_ = _args[13];
lean_object* v___x_921_ = _args[14];
lean_object* v_name_922_ = _args[15];
lean_object* v___x_923_ = _args[16];
lean_object* v_alts_924_ = _args[17];
lean_object* v___y_925_ = _args[18];
lean_object* v___y_926_ = _args[19];
lean_object* v___y_927_ = _args[20];
lean_object* v___y_928_ = _args[21];
lean_object* v___y_929_ = _args[22];
_start:
{
uint8_t v___x_21299__boxed_930_; uint8_t v___x_21300__boxed_931_; uint8_t v___x_21301__boxed_932_; lean_object* v_res_933_; 
v___x_21299__boxed_930_ = lean_unbox(v___x_914_);
v___x_21300__boxed_931_ = lean_unbox(v___x_915_);
v___x_21301__boxed_932_ = lean_unbox(v___x_916_);
v_res_933_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_907_, v_tail_908_, v_params_909_, v_ism1_910_, v_ism2_911_, v_motive_912_, v___x_913_, v___x_21299__boxed_930_, v___x_21300__boxed_931_, v___x_21301__boxed_932_, v___x_917_, v_numParams_918_, v_val_919_, v___x_920_, v___x_921_, v_name_922_, v___x_923_, v_alts_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object* v___x_977_, lean_object* v_a_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_20179__overap_985_; lean_object* v___x_986_; 
v___x_984_ = l_Lean_instInhabitedExpr;
v___x_20179__overap_985_ = l_instInhabitedOfMonad___redArg(v___x_977_, v___x_984_);
lean_inc(v___y_982_);
lean_inc_ref(v___y_981_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
v___x_986_ = lean_apply_5(v___x_20179__overap_985_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, lean_box(0));
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object* v___x_987_, lean_object* v_a_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_987_, v_a_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec_ref(v_a_988_);
return v_res_994_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_instMonadEIO(lean_box(0));
return v___x_995_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0);
v___x_997_ = l_StateRefT_x27_instMonad___redArg(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object* v_acc_1002_, lean_object* v_declInfos_1003_, lean_object* v_k_1004_, lean_object* v_kind_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
uint8_t v_kind_boxed_1012_; lean_object* v_res_1013_; 
v_kind_boxed_1012_ = lean_unbox(v_kind_1005_);
v_res_1013_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_1002_, v_declInfos_1003_, v_k_1004_, v_kind_boxed_1012_, v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_declInfos_1014_, lean_object* v_k_1015_, uint8_t v_kind_1016_, lean_object* v_acc_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v_toApplicative_1024_; lean_object* v_toFunctor_1025_; lean_object* v_toSeq_1026_; lean_object* v_toSeqLeft_1027_; lean_object* v_toSeqRight_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v_toApplicative_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1089_; 
v___x_1023_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_1024_ = lean_ctor_get(v___x_1023_, 0);
v_toFunctor_1025_ = lean_ctor_get(v_toApplicative_1024_, 0);
v_toSeq_1026_ = lean_ctor_get(v_toApplicative_1024_, 2);
v_toSeqLeft_1027_ = lean_ctor_get(v_toApplicative_1024_, 3);
v_toSeqRight_1028_ = lean_ctor_get(v_toApplicative_1024_, 4);
v___f_1029_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_1030_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_1025_, 2);
v___f_1031_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1031_, 0, v_toFunctor_1025_);
v___f_1032_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1032_, 0, v_toFunctor_1025_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___f_1031_);
lean_ctor_set(v___x_1033_, 1, v___f_1032_);
lean_inc(v_toSeqRight_1028_);
v___f_1034_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1034_, 0, v_toSeqRight_1028_);
lean_inc(v_toSeqLeft_1027_);
v___f_1035_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1035_, 0, v_toSeqLeft_1027_);
lean_inc(v_toSeq_1026_);
v___f_1036_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1036_, 0, v_toSeq_1026_);
v___x_1037_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1033_);
lean_ctor_set(v___x_1037_, 1, v___f_1029_);
lean_ctor_set(v___x_1037_, 2, v___f_1036_);
lean_ctor_set(v___x_1037_, 3, v___f_1035_);
lean_ctor_set(v___x_1037_, 4, v___f_1034_);
v___x_1038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___f_1030_);
v___x_1039_ = l_StateRefT_x27_instMonad___redArg(v___x_1038_);
v_toApplicative_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v___x_1039_, 1);
lean_dec(v_unused_1090_);
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1089_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_toApplicative_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1089_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_toFunctor_1044_; lean_object* v_toSeq_1045_; lean_object* v_toSeqLeft_1046_; lean_object* v_toSeqRight_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1087_; 
v_toFunctor_1044_ = lean_ctor_get(v_toApplicative_1040_, 0);
v_toSeq_1045_ = lean_ctor_get(v_toApplicative_1040_, 2);
v_toSeqLeft_1046_ = lean_ctor_get(v_toApplicative_1040_, 3);
v_toSeqRight_1047_ = lean_ctor_get(v_toApplicative_1040_, 4);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_toApplicative_1040_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v_toApplicative_1040_, 1);
lean_dec(v_unused_1088_);
v___x_1049_ = v_toApplicative_1040_;
v_isShared_1050_ = v_isSharedCheck_1087_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_toSeqRight_1047_);
lean_inc(v_toSeqLeft_1046_);
lean_inc(v_toSeq_1045_);
lean_inc(v_toFunctor_1044_);
lean_dec(v_toApplicative_1040_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1087_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___x_1060_; 
v___f_1051_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_1052_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_1044_);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toFunctor_1044_);
v___f_1054_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1054_, 0, v_toFunctor_1044_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___f_1053_);
lean_ctor_set(v___x_1055_, 1, v___f_1054_);
v___f_1056_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1056_, 0, v_toSeqRight_1047_);
v___f_1057_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1057_, 0, v_toSeqLeft_1046_);
v___f_1058_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1058_, 0, v_toSeq_1045_);
if (v_isShared_1050_ == 0)
{
lean_ctor_set(v___x_1049_, 4, v___f_1056_);
lean_ctor_set(v___x_1049_, 3, v___f_1057_);
lean_ctor_set(v___x_1049_, 2, v___f_1058_);
lean_ctor_set(v___x_1049_, 1, v___f_1051_);
lean_ctor_set(v___x_1049_, 0, v___x_1055_);
v___x_1060_ = v___x_1049_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___f_1051_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v___f_1058_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v___f_1057_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v___f_1056_);
v___x_1060_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1062_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 1, v___f_1052_);
lean_ctor_set(v___x_1042_, 0, v___x_1060_);
v___x_1062_ = v___x_1042_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1060_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___f_1052_);
v___x_1062_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1063_ = lean_array_get_size(v_acc_1017_);
v___x_1064_ = lean_array_get_size(v_declInfos_1014_);
v___x_1065_ = lean_nat_dec_lt(v___x_1063_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; 
lean_dec_ref(v___x_1062_);
lean_dec_ref(v_declInfos_1014_);
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
v___x_1066_ = lean_apply_6(v_k_1015_, v_acc_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, lean_box(0));
return v___x_1066_;
}
else
{
lean_object* v___f_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_snd_1075_; lean_object* v_fst_1076_; lean_object* v_fst_1077_; lean_object* v_snd_1078_; lean_object* v___x_1079_; 
v___f_1067_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1067_, 0, v___x_1062_);
v___x_1068_ = lean_box(0);
v___x_1069_ = 0;
v___f_1070_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1070_, 0, v___f_1067_);
v___x_1071_ = lean_box(v___x_1069_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___f_1070_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1068_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_array_get(v___x_1073_, v_declInfos_1014_, v___x_1063_);
lean_dec_ref_known(v___x_1073_, 2);
v_snd_1075_ = lean_ctor_get(v___x_1074_, 1);
lean_inc(v_snd_1075_);
v_fst_1076_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_fst_1076_);
lean_dec(v___x_1074_);
v_fst_1077_ = lean_ctor_get(v_snd_1075_, 0);
lean_inc(v_fst_1077_);
v_snd_1078_ = lean_ctor_get(v_snd_1075_, 1);
lean_inc(v_snd_1078_);
lean_dec(v_snd_1075_);
lean_inc(v___y_1021_);
lean_inc_ref(v___y_1020_);
lean_inc(v___y_1019_);
lean_inc_ref(v___y_1018_);
lean_inc_ref(v_acc_1017_);
v___x_1079_ = lean_apply_6(v_snd_1078_, v_acc_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, lean_box(0));
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___f_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = lean_box(v_kind_1016_);
v___f_1082_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1082_, 0, v_acc_1017_);
lean_closure_set(v___f_1082_, 1, v_declInfos_1014_);
lean_closure_set(v___f_1082_, 2, v_k_1015_);
lean_closure_set(v___f_1082_, 3, v___x_1081_);
v___x_1083_ = lean_unbox(v_fst_1077_);
lean_dec(v_fst_1077_);
v___x_1084_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1076_, v___x_1083_, v_a_1080_, v___f_1082_, v_kind_1016_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1084_;
}
else
{
lean_dec(v_fst_1077_);
lean_dec(v_fst_1076_);
lean_dec_ref(v_acc_1017_);
lean_dec_ref(v_k_1015_);
lean_dec_ref(v_declInfos_1014_);
return v___x_1079_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(lean_object* v_acc_1091_, lean_object* v_declInfos_1092_, lean_object* v_k_1093_, uint8_t v_kind_1094_, lean_object* v_x_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_array_push(v_acc_1091_, v_x_1095_);
v___x_1102_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1092_, v_k_1093_, v_kind_1094_, v___x_1101_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(lean_object* v_declInfos_1103_, lean_object* v_k_1104_, lean_object* v_kind_1105_, lean_object* v_acc_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
uint8_t v_kind_boxed_1112_; lean_object* v_res_1113_; 
v_kind_boxed_1112_ = lean_unbox(v_kind_1105_);
v_res_1113_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1103_, v_k_1104_, v_kind_boxed_1112_, v_acc_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(lean_object* v_declInfos_1116_, lean_object* v_k_1117_, uint8_t v_kind_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1124_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_1125_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_1116_, v_k_1117_, v_kind_1118_, v___x_1124_, v___y_1119_, v___y_1120_, v___y_1121_, v___y_1122_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(lean_object* v_declInfos_1126_, lean_object* v_k_1127_, lean_object* v_kind_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_){
_start:
{
uint8_t v_kind_boxed_1134_; lean_object* v_res_1135_; 
v_kind_boxed_1134_ = lean_unbox(v_kind_1128_);
v_res_1135_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_declInfos_1126_, v_k_1127_, v_kind_boxed_1134_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(size_t v_sz_1136_, size_t v_i_1137_, lean_object* v_bs_1138_){
_start:
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_usize_dec_lt(v_i_1137_, v_sz_1136_);
if (v___x_1139_ == 0)
{
return v_bs_1138_;
}
else
{
lean_object* v_v_1140_; lean_object* v_fst_1141_; lean_object* v_snd_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1158_; 
v_v_1140_ = lean_array_uget(v_bs_1138_, v_i_1137_);
v_fst_1141_ = lean_ctor_get(v_v_1140_, 0);
v_snd_1142_ = lean_ctor_get(v_v_1140_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_v_1140_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1144_ = v_v_1140_;
v_isShared_1145_ = v_isSharedCheck_1158_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_snd_1142_);
lean_inc(v_fst_1141_);
lean_dec(v_v_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1158_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1146_; lean_object* v_bs_x27_1147_; uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1146_ = lean_unsigned_to_nat(0u);
v_bs_x27_1147_ = lean_array_uset(v_bs_1138_, v_i_1137_, v___x_1146_);
v___x_1148_ = 0;
v___x_1149_ = lean_box(v___x_1148_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1149_);
v___x_1151_ = v___x_1144_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_snd_1142_);
v___x_1151_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; size_t v___x_1153_; size_t v___x_1154_; lean_object* v___x_1155_; 
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v_fst_1141_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = lean_usize_add(v_i_1137_, v___x_1153_);
v___x_1155_ = lean_array_uset(v_bs_x27_1147_, v_i_1137_, v___x_1152_);
v_i_1137_ = v___x_1154_;
v_bs_1138_ = v___x_1155_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_sz_1159_, lean_object* v_i_1160_, lean_object* v_bs_1161_){
_start:
{
size_t v_sz_boxed_1162_; size_t v_i_boxed_1163_; lean_object* v_res_1164_; 
v_sz_boxed_1162_ = lean_unbox_usize(v_sz_1159_);
lean_dec(v_sz_1159_);
v_i_boxed_1163_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_1162_, v_i_boxed_1163_, v_bs_1161_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_declInfos_1165_, lean_object* v_k_1166_, uint8_t v_kind_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
size_t v_sz_1173_; size_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_sz_1173_ = lean_array_size(v_declInfos_1165_);
v___x_1174_ = ((size_t)0ULL);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_1173_, v___x_1174_, v_declInfos_1165_);
v___x_1176_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v___x_1175_, v_k_1166_, v_kind_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_declInfos_1177_, lean_object* v_k_1178_, lean_object* v_kind_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
uint8_t v_kind_boxed_1185_; lean_object* v_res_1186_; 
v_kind_boxed_1185_ = lean_unbox(v_kind_1179_);
v_res_1186_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1177_, v_k_1178_, v_kind_boxed_1185_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_declInfos_1187_, lean_object* v_k_1188_, uint8_t v_kind_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
size_t v_sz_1195_; size_t v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_sz_1195_ = lean_array_size(v_declInfos_1187_);
v___x_1196_ = ((size_t)0ULL);
v___x_1197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1195_, v___x_1196_, v_declInfos_1187_);
v___x_1198_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_1197_, v_k_1188_, v_kind_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_declInfos_1199_, lean_object* v_k_1200_, lean_object* v_kind_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
uint8_t v_kind_boxed_1207_; lean_object* v_res_1208_; 
v_kind_boxed_1207_ = lean_unbox(v_kind_1201_);
v_res_1208_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1199_, v_k_1200_, v_kind_boxed_1207_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_1210_, lean_object* v_dummy_1211_, lean_object* v___x_1212_, lean_object* v___x_1213_, lean_object* v___x_1214_, lean_object* v_motive_1215_, lean_object* v_zs1_1216_, uint8_t v___x_1217_, uint8_t v___x_1218_, uint8_t v___x_1219_, lean_object* v_v_1220_, lean_object* v___x_1221_, lean_object* v_zs2_1222_, lean_object* v_ctorRet2_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
lean_inc(v___y_1227_);
lean_inc_ref(v___y_1226_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
v___x_1229_ = lean_whnf(v_ctorRet2_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_object* v_a_1230_; lean_object* v___x_1231_; lean_object* v_nargs_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref_known(v___x_1229_, 1);
v___x_1231_ = l_Lean_mkAppN(v___x_1210_, v_zs2_1222_);
v_nargs_1232_ = l_Lean_Expr_getAppNumArgs(v_a_1230_);
lean_inc(v_nargs_1232_);
v___x_1233_ = lean_mk_array(v_nargs_1232_, v_dummy_1211_);
v___x_1234_ = lean_nat_sub(v_nargs_1232_, v___x_1212_);
lean_dec(v_nargs_1232_);
v___x_1235_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1230_, v___x_1233_, v___x_1234_);
v___x_1236_ = lean_array_get_size(v___x_1235_);
v___x_1237_ = l_Array_toSubarray___redArg(v___x_1235_, v___x_1213_, v___x_1236_);
v___x_1238_ = l_Subarray_copy___redArg(v___x_1237_);
v___x_1239_ = lean_array_push(v___x_1238_, v___x_1231_);
v___x_1240_ = l_Array_append___redArg(v___x_1214_, v___x_1239_);
lean_dec_ref(v___x_1239_);
v___x_1241_ = l_Lean_mkAppN(v_motive_1215_, v___x_1240_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = l_Array_append___redArg(v_zs1_1216_, v_zs2_1222_);
v___x_1243_ = l_Lean_Meta_mkForallFVars(v___x_1242_, v___x_1241_, v___x_1217_, v___x_1218_, v___x_1218_, v___x_1219_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec_ref(v___x_1242_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1263_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1263_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1263_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___y_1249_; 
if (lean_obj_tag(v_v_1220_) == 1)
{
lean_object* v_str_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_str_1254_ = lean_ctor_get(v_v_1220_, 1);
lean_inc_ref(v_str_1254_);
lean_dec_ref_known(v_v_1220_, 2);
v___x_1255_ = lean_box(0);
v___x_1256_ = l_Lean_Name_str___override(v___x_1255_, v_str_1254_);
v___y_1249_ = v___x_1256_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
lean_dec(v_v_1220_);
v___x_1257_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_1258_ = lean_nat_add(v___x_1221_, v___x_1212_);
v___x_1259_ = l_Nat_reprFast(v___x_1258_);
v___x_1260_ = lean_string_append(v___x_1257_, v___x_1259_);
lean_dec_ref(v___x_1259_);
v___x_1261_ = lean_box(0);
v___x_1262_ = l_Lean_Name_str___override(v___x_1261_, v___x_1260_);
v___y_1249_ = v___x_1262_;
goto v___jp_1248_;
}
v___jp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___y_1249_);
lean_ctor_set(v___x_1250_, 1, v_a_1244_);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v___x_1250_);
v___x_1252_ = v___x_1246_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v_v_1220_);
v_a_1264_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1243_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1243_);
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
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec(v_v_1220_);
lean_dec_ref(v_zs1_1216_);
lean_dec_ref(v_motive_1215_);
lean_dec_ref(v___x_1214_);
lean_dec(v___x_1213_);
lean_dec_ref(v_dummy_1211_);
lean_dec_ref(v___x_1210_);
v_a_1272_ = lean_ctor_get(v___x_1229_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1229_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1229_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1229_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1280_ = _args[0];
lean_object* v_dummy_1281_ = _args[1];
lean_object* v___x_1282_ = _args[2];
lean_object* v___x_1283_ = _args[3];
lean_object* v___x_1284_ = _args[4];
lean_object* v_motive_1285_ = _args[5];
lean_object* v_zs1_1286_ = _args[6];
lean_object* v___x_1287_ = _args[7];
lean_object* v___x_1288_ = _args[8];
lean_object* v___x_1289_ = _args[9];
lean_object* v_v_1290_ = _args[10];
lean_object* v___x_1291_ = _args[11];
lean_object* v_zs2_1292_ = _args[12];
lean_object* v_ctorRet2_1293_ = _args[13];
lean_object* v___y_1294_ = _args[14];
lean_object* v___y_1295_ = _args[15];
lean_object* v___y_1296_ = _args[16];
lean_object* v___y_1297_ = _args[17];
lean_object* v___y_1298_ = _args[18];
_start:
{
uint8_t v___x_21735__boxed_1299_; uint8_t v___x_21736__boxed_1300_; uint8_t v___x_21737__boxed_1301_; lean_object* v_res_1302_; 
v___x_21735__boxed_1299_ = lean_unbox(v___x_1287_);
v___x_21736__boxed_1300_ = lean_unbox(v___x_1288_);
v___x_21737__boxed_1301_ = lean_unbox(v___x_1289_);
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1280_, v_dummy_1281_, v___x_1282_, v___x_1283_, v___x_1284_, v_motive_1285_, v_zs1_1286_, v___x_21735__boxed_1299_, v___x_21736__boxed_1300_, v___x_21737__boxed_1301_, v_v_1290_, v___x_1291_, v_zs2_1292_, v_ctorRet2_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec(v___y_1297_);
lean_dec_ref(v___y_1296_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec_ref(v_zs2_1292_);
lean_dec(v___x_1291_);
lean_dec(v___x_1282_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1303_, lean_object* v___x_1304_, lean_object* v___x_1305_, lean_object* v_motive_1306_, uint8_t v___x_1307_, uint8_t v___x_1308_, uint8_t v___x_1309_, lean_object* v_v_1310_, lean_object* v___x_1311_, lean_object* v_a_1312_, lean_object* v_zs1_1313_, lean_object* v_ctorRet1_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; 
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc_ref(v___y_1315_);
v___x_1320_ = lean_whnf(v_ctorRet1_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1322_; lean_object* v_dummy_1323_; lean_object* v_nargs_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___f_1335_; lean_object* v___x_1336_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 1);
lean_inc_ref(v___x_1303_);
v___x_1322_ = l_Lean_mkAppN(v___x_1303_, v_zs1_1313_);
v_dummy_1323_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1324_ = l_Lean_Expr_getAppNumArgs(v_a_1321_);
lean_inc(v_nargs_1324_);
v___x_1325_ = lean_mk_array(v_nargs_1324_, v_dummy_1323_);
v___x_1326_ = lean_nat_sub(v_nargs_1324_, v___x_1304_);
lean_dec(v_nargs_1324_);
v___x_1327_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1321_, v___x_1325_, v___x_1326_);
v___x_1328_ = lean_array_get_size(v___x_1327_);
lean_inc(v___x_1305_);
v___x_1329_ = l_Array_toSubarray___redArg(v___x_1327_, v___x_1305_, v___x_1328_);
v___x_1330_ = l_Subarray_copy___redArg(v___x_1329_);
v___x_1331_ = lean_array_push(v___x_1330_, v___x_1322_);
v___x_1332_ = lean_box(v___x_1307_);
v___x_1333_ = lean_box(v___x_1308_);
v___x_1334_ = lean_box(v___x_1309_);
v___f_1335_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1335_, 0, v___x_1303_);
lean_closure_set(v___f_1335_, 1, v_dummy_1323_);
lean_closure_set(v___f_1335_, 2, v___x_1304_);
lean_closure_set(v___f_1335_, 3, v___x_1305_);
lean_closure_set(v___f_1335_, 4, v___x_1331_);
lean_closure_set(v___f_1335_, 5, v_motive_1306_);
lean_closure_set(v___f_1335_, 6, v_zs1_1313_);
lean_closure_set(v___f_1335_, 7, v___x_1332_);
lean_closure_set(v___f_1335_, 8, v___x_1333_);
lean_closure_set(v___f_1335_, 9, v___x_1334_);
lean_closure_set(v___f_1335_, 10, v_v_1310_);
lean_closure_set(v___f_1335_, 11, v___x_1311_);
v___x_1336_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1312_, v___f_1335_, v___x_1307_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
return v___x_1336_;
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec_ref(v_zs1_1313_);
lean_dec_ref(v_a_1312_);
lean_dec(v___x_1311_);
lean_dec(v_v_1310_);
lean_dec_ref(v_motive_1306_);
lean_dec(v___x_1305_);
lean_dec(v___x_1304_);
lean_dec_ref(v___x_1303_);
v_a_1337_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1320_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1320_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1345_ = _args[0];
lean_object* v___x_1346_ = _args[1];
lean_object* v___x_1347_ = _args[2];
lean_object* v_motive_1348_ = _args[3];
lean_object* v___x_1349_ = _args[4];
lean_object* v___x_1350_ = _args[5];
lean_object* v___x_1351_ = _args[6];
lean_object* v_v_1352_ = _args[7];
lean_object* v___x_1353_ = _args[8];
lean_object* v_a_1354_ = _args[9];
lean_object* v_zs1_1355_ = _args[10];
lean_object* v_ctorRet1_1356_ = _args[11];
lean_object* v___y_1357_ = _args[12];
lean_object* v___y_1358_ = _args[13];
lean_object* v___y_1359_ = _args[14];
lean_object* v___y_1360_ = _args[15];
lean_object* v___y_1361_ = _args[16];
_start:
{
uint8_t v___x_21876__boxed_1362_; uint8_t v___x_21877__boxed_1363_; uint8_t v___x_21878__boxed_1364_; lean_object* v_res_1365_; 
v___x_21876__boxed_1362_ = lean_unbox(v___x_1349_);
v___x_21877__boxed_1363_ = lean_unbox(v___x_1350_);
v___x_21878__boxed_1364_ = lean_unbox(v___x_1351_);
v_res_1365_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1345_, v___x_1346_, v___x_1347_, v_motive_1348_, v___x_21876__boxed_1362_, v___x_21877__boxed_1363_, v___x_21878__boxed_1364_, v_v_1352_, v___x_1353_, v_a_1354_, v_zs1_1355_, v_ctorRet1_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1366_, lean_object* v_params_1367_, lean_object* v___x_1368_, lean_object* v_motive_1369_, size_t v_sz_1370_, size_t v_i_1371_, lean_object* v_bs_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
uint8_t v___x_1378_; 
v___x_1378_ = lean_usize_dec_lt(v_i_1371_, v_sz_1370_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref(v_motive_1369_);
lean_dec(v___x_1368_);
lean_dec(v_tail_1366_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_bs_1372_);
return v___x_1379_;
}
else
{
lean_object* v_v_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v_v_1380_ = lean_array_uget(v_bs_1372_, v_i_1371_);
lean_inc(v_tail_1366_);
lean_inc(v_v_1380_);
v___x_1381_ = l_Lean_mkConst(v_v_1380_, v_tail_1366_);
v___x_1382_ = l_Lean_mkAppN(v___x_1381_, v_params_1367_);
lean_inc(v___y_1376_);
lean_inc_ref(v___y_1375_);
lean_inc(v___y_1374_);
lean_inc_ref(v___y_1373_);
lean_inc_ref(v___x_1382_);
v___x_1383_ = lean_infer_type(v___x_1382_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; lean_object* v___x_1385_; lean_object* v_bs_x27_1386_; uint8_t v___x_1387_; uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___f_1394_; lean_object* v___x_1395_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc_n(v_a_1384_, 2);
lean_dec_ref_known(v___x_1383_, 1);
v___x_1385_ = lean_unsigned_to_nat(0u);
v_bs_x27_1386_ = lean_array_uset(v_bs_1372_, v_i_1371_, v___x_1385_);
v___x_1387_ = 0;
v___x_1388_ = 1;
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = lean_usize_to_nat(v_i_1371_);
v___x_1391_ = lean_box(v___x_1387_);
v___x_1392_ = lean_box(v___x_1378_);
v___x_1393_ = lean_box(v___x_1388_);
lean_inc_ref(v_motive_1369_);
lean_inc(v___x_1368_);
v___f_1394_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1394_, 0, v___x_1382_);
lean_closure_set(v___f_1394_, 1, v___x_1389_);
lean_closure_set(v___f_1394_, 2, v___x_1368_);
lean_closure_set(v___f_1394_, 3, v_motive_1369_);
lean_closure_set(v___f_1394_, 4, v___x_1391_);
lean_closure_set(v___f_1394_, 5, v___x_1392_);
lean_closure_set(v___f_1394_, 6, v___x_1393_);
lean_closure_set(v___f_1394_, 7, v_v_1380_);
lean_closure_set(v___f_1394_, 8, v___x_1390_);
lean_closure_set(v___f_1394_, 9, v_a_1384_);
v___x_1395_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1384_, v___f_1394_, v___x_1387_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
if (lean_obj_tag(v___x_1395_) == 0)
{
lean_object* v_a_1396_; size_t v___x_1397_; size_t v___x_1398_; lean_object* v___x_1399_; 
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref_known(v___x_1395_, 1);
v___x_1397_ = ((size_t)1ULL);
v___x_1398_ = lean_usize_add(v_i_1371_, v___x_1397_);
v___x_1399_ = lean_array_uset(v_bs_x27_1386_, v_i_1371_, v_a_1396_);
v_i_1371_ = v___x_1398_;
v_bs_1372_ = v___x_1399_;
goto _start;
}
else
{
lean_object* v_a_1401_; lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1408_; 
lean_dec_ref(v_bs_x27_1386_);
lean_dec_ref(v_motive_1369_);
lean_dec(v___x_1368_);
lean_dec(v_tail_1366_);
v_a_1401_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1403_ = v___x_1395_;
v_isShared_1404_ = v_isSharedCheck_1408_;
goto v_resetjp_1402_;
}
else
{
lean_inc(v_a_1401_);
lean_dec(v___x_1395_);
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
else
{
lean_object* v_a_1409_; lean_object* v___x_1411_; uint8_t v_isShared_1412_; uint8_t v_isSharedCheck_1416_; 
lean_dec_ref(v___x_1382_);
lean_dec(v_v_1380_);
lean_dec_ref(v_bs_1372_);
lean_dec_ref(v_motive_1369_);
lean_dec(v___x_1368_);
lean_dec(v_tail_1366_);
v_a_1409_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1411_ = v___x_1383_;
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
else
{
lean_inc(v_a_1409_);
lean_dec(v___x_1383_);
v___x_1411_ = lean_box(0);
v_isShared_1412_ = v_isSharedCheck_1416_;
goto v_resetjp_1410_;
}
v_resetjp_1410_:
{
lean_object* v___x_1414_; 
if (v_isShared_1412_ == 0)
{
v___x_1414_ = v___x_1411_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_a_1409_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1417_, lean_object* v_params_1418_, lean_object* v___x_1419_, lean_object* v_motive_1420_, lean_object* v_sz_1421_, lean_object* v_i_1422_, lean_object* v_bs_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
size_t v_sz_boxed_1429_; size_t v_i_boxed_1430_; lean_object* v_res_1431_; 
v_sz_boxed_1429_ = lean_unbox_usize(v_sz_1421_);
lean_dec(v_sz_1421_);
v_i_boxed_1430_ = lean_unbox_usize(v_i_1422_);
lean_dec(v_i_1422_);
v_res_1431_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1417_, v_params_1418_, v___x_1419_, v_motive_1420_, v_sz_boxed_1429_, v_i_boxed_1430_, v_bs_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec_ref(v_params_1418_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1432_, lean_object* v_tail_1433_, lean_object* v_params_1434_, lean_object* v_numParams_1435_, lean_object* v_indName_1436_, lean_object* v_ism1_1437_, lean_object* v_ism2_1438_, lean_object* v___x_1439_, uint8_t v___x_1440_, uint8_t v___x_1441_, uint8_t v___x_1442_, lean_object* v_val_1443_, lean_object* v___x_1444_, lean_object* v___x_1445_, lean_object* v_name_1446_, lean_object* v___x_1447_, lean_object* v_motive_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; size_t v_sz_1455_; size_t v___x_1456_; lean_object* v___x_1457_; 
v___x_1454_ = lean_array_mk(v_ctors_1432_);
v_sz_1455_ = lean_array_size(v___x_1454_);
v___x_1456_ = ((size_t)0ULL);
lean_inc_ref(v___x_1454_);
lean_inc_ref(v_motive_1448_);
lean_inc(v_numParams_1435_);
lean_inc(v_tail_1433_);
v___x_1457_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1433_, v_params_1434_, v_numParams_1435_, v_motive_1448_, v_sz_1455_, v___x_1456_, v___x_1454_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1457_) == 0)
{
lean_object* v_a_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___f_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; 
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref_known(v___x_1457_, 1);
v___x_1459_ = lean_box(v___x_1440_);
v___x_1460_ = lean_box(v___x_1441_);
v___x_1461_ = lean_box(v___x_1442_);
v___f_1462_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1462_, 0, v_indName_1436_);
lean_closure_set(v___f_1462_, 1, v_tail_1433_);
lean_closure_set(v___f_1462_, 2, v_params_1434_);
lean_closure_set(v___f_1462_, 3, v_ism1_1437_);
lean_closure_set(v___f_1462_, 4, v_ism2_1438_);
lean_closure_set(v___f_1462_, 5, v_motive_1448_);
lean_closure_set(v___f_1462_, 6, v___x_1439_);
lean_closure_set(v___f_1462_, 7, v___x_1459_);
lean_closure_set(v___f_1462_, 8, v___x_1460_);
lean_closure_set(v___f_1462_, 9, v___x_1461_);
lean_closure_set(v___f_1462_, 10, v___x_1454_);
lean_closure_set(v___f_1462_, 11, v_numParams_1435_);
lean_closure_set(v___f_1462_, 12, v_val_1443_);
lean_closure_set(v___f_1462_, 13, v___x_1444_);
lean_closure_set(v___f_1462_, 14, v___x_1445_);
lean_closure_set(v___f_1462_, 15, v_name_1446_);
lean_closure_set(v___f_1462_, 16, v___x_1447_);
v___x_1463_ = 0;
v___x_1464_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_a_1458_, v___f_1462_, v___x_1463_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
return v___x_1464_;
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec_ref(v___x_1454_);
lean_dec_ref(v_motive_1448_);
lean_dec(v___x_1447_);
lean_dec(v_name_1446_);
lean_dec(v___x_1445_);
lean_dec(v___x_1444_);
lean_dec_ref(v_val_1443_);
lean_dec_ref(v___x_1439_);
lean_dec_ref(v_ism2_1438_);
lean_dec_ref(v_ism1_1437_);
lean_dec(v_indName_1436_);
lean_dec(v_numParams_1435_);
lean_dec_ref(v_params_1434_);
lean_dec(v_tail_1433_);
v_a_1465_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1457_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1457_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1473_ = _args[0];
lean_object* v_tail_1474_ = _args[1];
lean_object* v_params_1475_ = _args[2];
lean_object* v_numParams_1476_ = _args[3];
lean_object* v_indName_1477_ = _args[4];
lean_object* v_ism1_1478_ = _args[5];
lean_object* v_ism2_1479_ = _args[6];
lean_object* v___x_1480_ = _args[7];
lean_object* v___x_1481_ = _args[8];
lean_object* v___x_1482_ = _args[9];
lean_object* v___x_1483_ = _args[10];
lean_object* v_val_1484_ = _args[11];
lean_object* v___x_1485_ = _args[12];
lean_object* v___x_1486_ = _args[13];
lean_object* v_name_1487_ = _args[14];
lean_object* v___x_1488_ = _args[15];
lean_object* v_motive_1489_ = _args[16];
lean_object* v___y_1490_ = _args[17];
lean_object* v___y_1491_ = _args[18];
lean_object* v___y_1492_ = _args[19];
lean_object* v___y_1493_ = _args[20];
lean_object* v___y_1494_ = _args[21];
_start:
{
uint8_t v___x_22056__boxed_1495_; uint8_t v___x_22057__boxed_1496_; uint8_t v___x_22058__boxed_1497_; lean_object* v_res_1498_; 
v___x_22056__boxed_1495_ = lean_unbox(v___x_1481_);
v___x_22057__boxed_1496_ = lean_unbox(v___x_1482_);
v___x_22058__boxed_1497_ = lean_unbox(v___x_1483_);
v_res_1498_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1473_, v_tail_1474_, v_params_1475_, v_numParams_1476_, v_indName_1477_, v_ism1_1478_, v_ism2_1479_, v___x_1480_, v___x_22056__boxed_1495_, v___x_22057__boxed_1496_, v___x_22058__boxed_1497_, v_val_1484_, v___x_1485_, v___x_1486_, v_name_1487_, v___x_1488_, v_motive_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1502_, lean_object* v_head_1503_, lean_object* v_ctors_1504_, lean_object* v_tail_1505_, lean_object* v_params_1506_, lean_object* v_numParams_1507_, lean_object* v_indName_1508_, lean_object* v_val_1509_, lean_object* v___x_1510_, lean_object* v___x_1511_, lean_object* v_name_1512_, lean_object* v___x_1513_, lean_object* v_ism2_1514_, lean_object* v_x_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; uint8_t v___x_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
lean_inc_ref(v_ism1_1502_);
v___x_1521_ = l_Array_append___redArg(v_ism1_1502_, v_ism2_1514_);
v___x_1522_ = l_Lean_mkSort(v_head_1503_);
v___x_1523_ = 0;
v___x_1524_ = 1;
v___x_1525_ = 1;
v___x_1526_ = l_Lean_Meta_mkForallFVars(v___x_1521_, v___x_1522_, v___x_1523_, v___x_1524_, v___x_1524_, v___x_1525_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___f_1531_; lean_object* v___x_1532_; uint8_t v___x_1533_; lean_object* v___x_1534_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = lean_box(v___x_1523_);
v___x_1529_ = lean_box(v___x_1524_);
v___x_1530_ = lean_box(v___x_1525_);
v___f_1531_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 22, 16);
lean_closure_set(v___f_1531_, 0, v_ctors_1504_);
lean_closure_set(v___f_1531_, 1, v_tail_1505_);
lean_closure_set(v___f_1531_, 2, v_params_1506_);
lean_closure_set(v___f_1531_, 3, v_numParams_1507_);
lean_closure_set(v___f_1531_, 4, v_indName_1508_);
lean_closure_set(v___f_1531_, 5, v_ism1_1502_);
lean_closure_set(v___f_1531_, 6, v_ism2_1514_);
lean_closure_set(v___f_1531_, 7, v___x_1521_);
lean_closure_set(v___f_1531_, 8, v___x_1528_);
lean_closure_set(v___f_1531_, 9, v___x_1529_);
lean_closure_set(v___f_1531_, 10, v___x_1530_);
lean_closure_set(v___f_1531_, 11, v_val_1509_);
lean_closure_set(v___f_1531_, 12, v___x_1510_);
lean_closure_set(v___f_1531_, 13, v___x_1511_);
lean_closure_set(v___f_1531_, 14, v_name_1512_);
lean_closure_set(v___f_1531_, 15, v___x_1513_);
v___x_1532_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1533_ = 0;
v___x_1534_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1532_, v___x_1525_, v_a_1527_, v___f_1531_, v___x_1533_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_);
return v___x_1534_;
}
else
{
lean_dec_ref(v___x_1521_);
lean_dec_ref(v_ism2_1514_);
lean_dec(v___x_1513_);
lean_dec(v_name_1512_);
lean_dec(v___x_1511_);
lean_dec(v___x_1510_);
lean_dec_ref(v_val_1509_);
lean_dec(v_indName_1508_);
lean_dec(v_numParams_1507_);
lean_dec_ref(v_params_1506_);
lean_dec(v_tail_1505_);
lean_dec(v_ctors_1504_);
lean_dec_ref(v_ism1_1502_);
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1535_ = _args[0];
lean_object* v_head_1536_ = _args[1];
lean_object* v_ctors_1537_ = _args[2];
lean_object* v_tail_1538_ = _args[3];
lean_object* v_params_1539_ = _args[4];
lean_object* v_numParams_1540_ = _args[5];
lean_object* v_indName_1541_ = _args[6];
lean_object* v_val_1542_ = _args[7];
lean_object* v___x_1543_ = _args[8];
lean_object* v___x_1544_ = _args[9];
lean_object* v_name_1545_ = _args[10];
lean_object* v___x_1546_ = _args[11];
lean_object* v_ism2_1547_ = _args[12];
lean_object* v_x_1548_ = _args[13];
lean_object* v___y_1549_ = _args[14];
lean_object* v___y_1550_ = _args[15];
lean_object* v___y_1551_ = _args[16];
lean_object* v___y_1552_ = _args[17];
lean_object* v___y_1553_ = _args[18];
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1535_, v_head_1536_, v_ctors_1537_, v_tail_1538_, v_params_1539_, v_numParams_1540_, v_indName_1541_, v_val_1542_, v___x_1543_, v___x_1544_, v_name_1545_, v___x_1546_, v_ism2_1547_, v_x_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v_x_1548_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1555_, lean_object* v_ctors_1556_, lean_object* v_tail_1557_, lean_object* v_params_1558_, lean_object* v_numParams_1559_, lean_object* v_indName_1560_, lean_object* v_val_1561_, lean_object* v___x_1562_, lean_object* v___x_1563_, lean_object* v_name_1564_, lean_object* v___x_1565_, lean_object* v_t_1566_, lean_object* v___x_1567_, lean_object* v_ism1_1568_, lean_object* v_x_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___f_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; 
v___f_1575_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 19, 12);
lean_closure_set(v___f_1575_, 0, v_ism1_1568_);
lean_closure_set(v___f_1575_, 1, v_head_1555_);
lean_closure_set(v___f_1575_, 2, v_ctors_1556_);
lean_closure_set(v___f_1575_, 3, v_tail_1557_);
lean_closure_set(v___f_1575_, 4, v_params_1558_);
lean_closure_set(v___f_1575_, 5, v_numParams_1559_);
lean_closure_set(v___f_1575_, 6, v_indName_1560_);
lean_closure_set(v___f_1575_, 7, v_val_1561_);
lean_closure_set(v___f_1575_, 8, v___x_1562_);
lean_closure_set(v___f_1575_, 9, v___x_1563_);
lean_closure_set(v___f_1575_, 10, v_name_1564_);
lean_closure_set(v___f_1575_, 11, v___x_1565_);
v___x_1576_ = 0;
v___x_1577_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1566_, v___x_1567_, v___f_1575_, v___x_1576_, v___x_1576_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1578_ = _args[0];
lean_object* v_ctors_1579_ = _args[1];
lean_object* v_tail_1580_ = _args[2];
lean_object* v_params_1581_ = _args[3];
lean_object* v_numParams_1582_ = _args[4];
lean_object* v_indName_1583_ = _args[5];
lean_object* v_val_1584_ = _args[6];
lean_object* v___x_1585_ = _args[7];
lean_object* v___x_1586_ = _args[8];
lean_object* v_name_1587_ = _args[9];
lean_object* v___x_1588_ = _args[10];
lean_object* v_t_1589_ = _args[11];
lean_object* v___x_1590_ = _args[12];
lean_object* v_ism1_1591_ = _args[13];
lean_object* v_x_1592_ = _args[14];
lean_object* v___y_1593_ = _args[15];
lean_object* v___y_1594_ = _args[16];
lean_object* v___y_1595_ = _args[17];
lean_object* v___y_1596_ = _args[18];
lean_object* v___y_1597_ = _args[19];
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1578_, v_ctors_1579_, v_tail_1580_, v_params_1581_, v_numParams_1582_, v_indName_1583_, v_val_1584_, v___x_1585_, v___x_1586_, v_name_1587_, v___x_1588_, v_t_1589_, v___x_1590_, v_ism1_1591_, v_x_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec_ref(v_x_1592_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1599_, lean_object* v___x_1600_, lean_object* v_head_1601_, lean_object* v_ctors_1602_, lean_object* v_tail_1603_, lean_object* v_params_1604_, lean_object* v_numParams_1605_, lean_object* v_indName_1606_, lean_object* v_val_1607_, lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v_name_1610_, lean_object* v_x_1611_, lean_object* v_t_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___f_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; 
v___x_1618_ = lean_nat_add(v_numIndices_1599_, v___x_1600_);
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
lean_inc_ref(v___x_1619_);
lean_inc_ref(v_t_1612_);
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 20, 13);
lean_closure_set(v___f_1620_, 0, v_head_1601_);
lean_closure_set(v___f_1620_, 1, v_ctors_1602_);
lean_closure_set(v___f_1620_, 2, v_tail_1603_);
lean_closure_set(v___f_1620_, 3, v_params_1604_);
lean_closure_set(v___f_1620_, 4, v_numParams_1605_);
lean_closure_set(v___f_1620_, 5, v_indName_1606_);
lean_closure_set(v___f_1620_, 6, v_val_1607_);
lean_closure_set(v___f_1620_, 7, v___x_1608_);
lean_closure_set(v___f_1620_, 8, v___x_1609_);
lean_closure_set(v___f_1620_, 9, v_name_1610_);
lean_closure_set(v___f_1620_, 10, v___x_1600_);
lean_closure_set(v___f_1620_, 11, v_t_1612_);
lean_closure_set(v___f_1620_, 12, v___x_1619_);
v___x_1621_ = 0;
v___x_1622_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1612_, v___x_1619_, v___f_1620_, v___x_1621_, v___x_1621_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1623_ = _args[0];
lean_object* v___x_1624_ = _args[1];
lean_object* v_head_1625_ = _args[2];
lean_object* v_ctors_1626_ = _args[3];
lean_object* v_tail_1627_ = _args[4];
lean_object* v_params_1628_ = _args[5];
lean_object* v_numParams_1629_ = _args[6];
lean_object* v_indName_1630_ = _args[7];
lean_object* v_val_1631_ = _args[8];
lean_object* v___x_1632_ = _args[9];
lean_object* v___x_1633_ = _args[10];
lean_object* v_name_1634_ = _args[11];
lean_object* v_x_1635_ = _args[12];
lean_object* v_t_1636_ = _args[13];
lean_object* v___y_1637_ = _args[14];
lean_object* v___y_1638_ = _args[15];
lean_object* v___y_1639_ = _args[16];
lean_object* v___y_1640_ = _args[17];
lean_object* v___y_1641_ = _args[18];
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1623_, v___x_1624_, v_head_1625_, v_ctors_1626_, v_tail_1627_, v_params_1628_, v_numParams_1629_, v_indName_1630_, v_val_1631_, v___x_1632_, v___x_1633_, v_name_1634_, v_x_1635_, v_t_1636_, v___y_1637_, v___y_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec_ref(v_x_1635_);
lean_dec(v_numIndices_1623_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1645_, lean_object* v_head_1646_, lean_object* v_ctors_1647_, lean_object* v_tail_1648_, lean_object* v_numParams_1649_, lean_object* v_indName_1650_, lean_object* v_val_1651_, lean_object* v___x_1652_, lean_object* v___x_1653_, lean_object* v_name_1654_, lean_object* v_params_1655_, lean_object* v_t_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v___x_1662_; lean_object* v___f_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; lean_object* v___x_1666_; 
v___x_1662_ = lean_unsigned_to_nat(1u);
v___f_1663_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 19, 12);
lean_closure_set(v___f_1663_, 0, v_numIndices_1645_);
lean_closure_set(v___f_1663_, 1, v___x_1662_);
lean_closure_set(v___f_1663_, 2, v_head_1646_);
lean_closure_set(v___f_1663_, 3, v_ctors_1647_);
lean_closure_set(v___f_1663_, 4, v_tail_1648_);
lean_closure_set(v___f_1663_, 5, v_params_1655_);
lean_closure_set(v___f_1663_, 6, v_numParams_1649_);
lean_closure_set(v___f_1663_, 7, v_indName_1650_);
lean_closure_set(v___f_1663_, 8, v_val_1651_);
lean_closure_set(v___f_1663_, 9, v___x_1652_);
lean_closure_set(v___f_1663_, 10, v___x_1653_);
lean_closure_set(v___f_1663_, 11, v_name_1654_);
v___x_1664_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1665_ = 0;
v___x_1666_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1656_, v___x_1664_, v___f_1663_, v___x_1665_, v___x_1665_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1667_ = _args[0];
lean_object* v_head_1668_ = _args[1];
lean_object* v_ctors_1669_ = _args[2];
lean_object* v_tail_1670_ = _args[3];
lean_object* v_numParams_1671_ = _args[4];
lean_object* v_indName_1672_ = _args[5];
lean_object* v_val_1673_ = _args[6];
lean_object* v___x_1674_ = _args[7];
lean_object* v___x_1675_ = _args[8];
lean_object* v_name_1676_ = _args[9];
lean_object* v_params_1677_ = _args[10];
lean_object* v_t_1678_ = _args[11];
lean_object* v___y_1679_ = _args[12];
lean_object* v___y_1680_ = _args[13];
lean_object* v___y_1681_ = _args[14];
lean_object* v___y_1682_ = _args[15];
lean_object* v___y_1683_ = _args[16];
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1667_, v_head_1668_, v_ctors_1669_, v_tail_1670_, v_numParams_1671_, v_indName_1672_, v_val_1673_, v___x_1674_, v___x_1675_, v_name_1676_, v_params_1677_, v_t_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1685_, lean_object* v_declName_1686_, lean_object* v_levelParams_1687_, uint8_t v___x_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
lean_inc_ref(v_a_1685_);
v___x_1694_ = lean_infer_type(v_a_1685_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1706_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref_known(v___x_1694_, 1);
v___x_1696_ = lean_box(1);
v___x_1697_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1686_, v_levelParams_1687_, v_a_1695_, v_a_1685_, v___x_1696_, v___y_1692_);
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1706_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
lean_ctor_set_tag(v___x_1700_, 1);
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_addDecl(v___x_1703_, v___x_1688_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
return v___x_1704_;
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v_levelParams_1687_);
lean_dec(v_declName_1686_);
lean_dec_ref(v_a_1685_);
v_a_1707_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1694_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1694_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1715_, lean_object* v_declName_1716_, lean_object* v_levelParams_1717_, lean_object* v___x_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v___x_22344__boxed_1724_; lean_object* v_res_1725_; 
v___x_22344__boxed_1724_ = lean_unbox(v___x_1718_);
v_res_1725_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1715_, v_declName_1716_, v_levelParams_1717_, v___x_22344__boxed_1724_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1726_, lean_object* v_a_1727_){
_start:
{
if (lean_obj_tag(v_a_1726_) == 0)
{
lean_object* v___x_1728_; 
v___x_1728_ = l_List_reverse___redArg(v_a_1727_);
return v___x_1728_;
}
else
{
lean_object* v_head_1729_; lean_object* v_tail_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1739_; 
v_head_1729_ = lean_ctor_get(v_a_1726_, 0);
v_tail_1730_ = lean_ctor_get(v_a_1726_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_a_1726_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1732_ = v_a_1726_;
v_isShared_1733_ = v_isSharedCheck_1739_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_tail_1730_);
lean_inc(v_head_1729_);
lean_dec(v_a_1726_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1739_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v___x_1734_; lean_object* v___x_1736_; 
v___x_1734_ = l_Lean_mkLevelParam(v_head_1729_);
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v_a_1727_);
lean_ctor_set(v___x_1732_, 0, v___x_1734_);
v___x_1736_ = v___x_1732_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_a_1727_);
v___x_1736_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
v_a_1726_ = v_tail_1730_;
v_a_1727_ = v___x_1736_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(lean_object* v_msgData_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v___x_1746_; lean_object* v_env_1747_; lean_object* v___x_1748_; lean_object* v_mctx_1749_; lean_object* v_lctx_1750_; lean_object* v_options_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1746_ = lean_st_ref_get(v___y_1744_);
v_env_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_ref(v_env_1747_);
lean_dec(v___x_1746_);
v___x_1748_ = lean_st_ref_get(v___y_1742_);
v_mctx_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc_ref(v_mctx_1749_);
lean_dec(v___x_1748_);
v_lctx_1750_ = lean_ctor_get(v___y_1741_, 2);
v_options_1751_ = lean_ctor_get(v___y_1743_, 2);
lean_inc_ref(v_options_1751_);
lean_inc_ref(v_lctx_1750_);
v___x_1752_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1752_, 0, v_env_1747_);
lean_ctor_set(v___x_1752_, 1, v_mctx_1749_);
lean_ctor_set(v___x_1752_, 2, v_lctx_1750_);
lean_ctor_set(v___x_1752_, 3, v_options_1751_);
v___x_1753_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v_msgData_1740_);
v___x_1754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_ref_1768_; lean_object* v___x_1769_; lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1778_; 
v_ref_1768_ = lean_ctor_get(v___y_1765_, 5);
v___x_1769_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
lean_inc(v_ref_1768_);
v___x_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1774_, 0, v_ref_1768_);
lean_ctor_set(v___x_1774_, 1, v_a_1770_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set_tag(v___x_1772_, 1);
lean_ctor_set(v___x_1772_, 0, v___x_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1786_, lean_object* v_msg_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_fileName_1793_; lean_object* v_fileMap_1794_; lean_object* v_options_1795_; lean_object* v_currRecDepth_1796_; lean_object* v_maxRecDepth_1797_; lean_object* v_ref_1798_; lean_object* v_currNamespace_1799_; lean_object* v_openDecls_1800_; lean_object* v_initHeartbeats_1801_; lean_object* v_maxHeartbeats_1802_; lean_object* v_quotContext_1803_; lean_object* v_currMacroScope_1804_; uint8_t v_diag_1805_; lean_object* v_cancelTk_x3f_1806_; uint8_t v_suppressElabErrors_1807_; lean_object* v_inheritedTraceOptions_1808_; lean_object* v_ref_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v_fileName_1793_ = lean_ctor_get(v___y_1790_, 0);
v_fileMap_1794_ = lean_ctor_get(v___y_1790_, 1);
v_options_1795_ = lean_ctor_get(v___y_1790_, 2);
v_currRecDepth_1796_ = lean_ctor_get(v___y_1790_, 3);
v_maxRecDepth_1797_ = lean_ctor_get(v___y_1790_, 4);
v_ref_1798_ = lean_ctor_get(v___y_1790_, 5);
v_currNamespace_1799_ = lean_ctor_get(v___y_1790_, 6);
v_openDecls_1800_ = lean_ctor_get(v___y_1790_, 7);
v_initHeartbeats_1801_ = lean_ctor_get(v___y_1790_, 8);
v_maxHeartbeats_1802_ = lean_ctor_get(v___y_1790_, 9);
v_quotContext_1803_ = lean_ctor_get(v___y_1790_, 10);
v_currMacroScope_1804_ = lean_ctor_get(v___y_1790_, 11);
v_diag_1805_ = lean_ctor_get_uint8(v___y_1790_, sizeof(void*)*14);
v_cancelTk_x3f_1806_ = lean_ctor_get(v___y_1790_, 12);
v_suppressElabErrors_1807_ = lean_ctor_get_uint8(v___y_1790_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1808_ = lean_ctor_get(v___y_1790_, 13);
v_ref_1809_ = l_Lean_replaceRef(v_ref_1786_, v_ref_1798_);
lean_inc_ref(v_inheritedTraceOptions_1808_);
lean_inc(v_cancelTk_x3f_1806_);
lean_inc(v_currMacroScope_1804_);
lean_inc(v_quotContext_1803_);
lean_inc(v_maxHeartbeats_1802_);
lean_inc(v_initHeartbeats_1801_);
lean_inc(v_openDecls_1800_);
lean_inc(v_currNamespace_1799_);
lean_inc(v_maxRecDepth_1797_);
lean_inc(v_currRecDepth_1796_);
lean_inc_ref(v_options_1795_);
lean_inc_ref(v_fileMap_1794_);
lean_inc_ref(v_fileName_1793_);
v___x_1810_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1810_, 0, v_fileName_1793_);
lean_ctor_set(v___x_1810_, 1, v_fileMap_1794_);
lean_ctor_set(v___x_1810_, 2, v_options_1795_);
lean_ctor_set(v___x_1810_, 3, v_currRecDepth_1796_);
lean_ctor_set(v___x_1810_, 4, v_maxRecDepth_1797_);
lean_ctor_set(v___x_1810_, 5, v_ref_1809_);
lean_ctor_set(v___x_1810_, 6, v_currNamespace_1799_);
lean_ctor_set(v___x_1810_, 7, v_openDecls_1800_);
lean_ctor_set(v___x_1810_, 8, v_initHeartbeats_1801_);
lean_ctor_set(v___x_1810_, 9, v_maxHeartbeats_1802_);
lean_ctor_set(v___x_1810_, 10, v_quotContext_1803_);
lean_ctor_set(v___x_1810_, 11, v_currMacroScope_1804_);
lean_ctor_set(v___x_1810_, 12, v_cancelTk_x3f_1806_);
lean_ctor_set(v___x_1810_, 13, v_inheritedTraceOptions_1808_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*14, v_diag_1805_);
lean_ctor_set_uint8(v___x_1810_, sizeof(void*)*14 + 1, v_suppressElabErrors_1807_);
v___x_1811_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1787_, v___y_1788_, v___y_1789_, v___x_1810_, v___y_1791_);
lean_dec_ref_known(v___x_1810_, 14);
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
lean_object* v___x_1820_; 
v___x_1820_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1820_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1824_ = lean_unsigned_to_nat(0u);
v___x_1825_ = lean_alloc_ctor(0, 10, 0);
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
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1829_ = ((size_t)5ULL);
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_unsigned_to_nat(32u);
v___x_1832_ = lean_mk_empty_array_with_capacity(v___x_1831_);
v___x_1833_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1834_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v___x_1832_);
lean_ctor_set(v___x_1834_, 2, v___x_1830_);
lean_ctor_set(v___x_1834_, 3, v___x_1830_);
lean_ctor_set_usize(v___x_1834_, 4, v___x_1829_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1835_ = lean_box(1);
v___x_1836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1837_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v___x_1836_);
lean_ctor_set(v___x_1838_, 2, v___x_1835_);
return v___x_1838_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6));
v___x_1841_ = l_Lean_stringToMessageData(v___x_1840_);
return v___x_1841_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10));
v___x_1847_ = l_Lean_stringToMessageData(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1849_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12));
v___x_1850_ = l_Lean_stringToMessageData(v___x_1849_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14));
v___x_1853_ = l_Lean_stringToMessageData(v___x_1852_);
return v___x_1853_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16));
v___x_1856_ = l_Lean_stringToMessageData(v___x_1855_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18));
v___x_1859_ = l_Lean_stringToMessageData(v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1860_, lean_object* v_declHint_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; lean_object* v_env_1865_; uint8_t v___y_1867_; uint8_t v___x_1923_; uint8_t v___x_1924_; 
v___x_1864_ = lean_st_ref_get(v___y_1862_);
v_env_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc_ref(v_env_1865_);
lean_dec(v___x_1864_);
v___x_1923_ = l_Lean_Name_isAnonymous(v_declHint_1861_);
v___x_1924_ = lean_bool_not(v___x_1923_);
if (v___x_1924_ == 0)
{
v___y_1867_ = v___x_1924_;
goto v___jp_1866_;
}
else
{
uint8_t v_isExporting_1925_; 
v_isExporting_1925_ = lean_ctor_get_uint8(v_env_1865_, sizeof(void*)*8);
v___y_1867_ = v_isExporting_1925_;
goto v___jp_1866_;
}
v___jp_1866_:
{
if (v___y_1867_ == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v_env_1865_);
lean_dec(v_declHint_1861_);
v___x_1868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1868_, 0, v_msg_1860_);
return v___x_1868_;
}
else
{
uint8_t v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1869_ = 0;
lean_inc_ref(v_env_1865_);
v___x_1870_ = l_Lean_Environment_setExporting(v_env_1865_, v___x_1869_);
lean_inc(v_declHint_1861_);
lean_inc_ref(v___x_1870_);
v___x_1871_ = l_Lean_Environment_contains(v___x_1870_, v_declHint_1861_, v___y_1867_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v___x_1870_);
lean_dec_ref(v_env_1865_);
lean_dec(v_declHint_1861_);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_msg_1860_);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_c_1878_; lean_object* v___x_1879_; 
v___x_1873_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1874_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5);
v___x_1875_ = l_Lean_Options_empty;
v___x_1876_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1870_);
lean_ctor_set(v___x_1876_, 1, v___x_1873_);
lean_ctor_set(v___x_1876_, 2, v___x_1874_);
lean_ctor_set(v___x_1876_, 3, v___x_1875_);
lean_inc(v_declHint_1861_);
v___x_1877_ = l_Lean_MessageData_ofConstName(v_declHint_1861_, v___x_1869_);
v_c_1878_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1878_, 0, v___x_1876_);
lean_ctor_set(v_c_1878_, 1, v___x_1877_);
v___x_1879_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1865_, v_declHint_1861_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
lean_dec_ref(v_env_1865_);
lean_dec(v_declHint_1861_);
v___x_1880_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1880_);
lean_ctor_set(v___x_1881_, 1, v_c_1878_);
v___x_1882_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9);
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
lean_object* v_val_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1922_; 
v_val_1887_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1889_ = v___x_1879_;
v_isShared_1890_ = v_isSharedCheck_1922_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_val_1887_);
lean_dec(v___x_1879_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1922_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v_mod_1894_; uint8_t v___x_1895_; 
v___x_1891_ = lean_box(0);
v___x_1892_ = l_Lean_Environment_header(v_env_1865_);
lean_dec_ref(v_env_1865_);
v___x_1893_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1892_);
v_mod_1894_ = lean_array_get(v___x_1891_, v___x_1893_, v_val_1887_);
lean_dec(v_val_1887_);
lean_dec_ref(v___x_1893_);
v___x_1895_ = l_Lean_isPrivateName(v_declHint_1861_);
lean_dec(v_declHint_1861_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1896_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11);
v___x_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v_c_1878_);
v___x_1898_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = l_Lean_MessageData_ofName(v_mod_1894_);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_MessageData_note(v___x_1903_);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_msg_1860_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1905_);
v___x_1907_ = v___x_1889_;
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
v___x_1909_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v_c_1878_);
v___x_1911_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = l_Lean_MessageData_ofName(v_mod_1894_);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = l_Lean_MessageData_note(v___x_1916_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v_msg_1860_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set_tag(v___x_1889_, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1918_);
v___x_1920_ = v___x_1889_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1926_, lean_object* v_declHint_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1926_, v_declHint_1927_, v___y_1928_);
lean_dec(v___y_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1931_, lean_object* v_declHint_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v___x_1938_; lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1948_; 
v___x_1938_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1931_, v_declHint_1932_, v___y_1936_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1948_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1948_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1943_ = l_Lean_unknownIdentifierMessageTag;
v___x_1944_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v_a_1939_);
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1944_);
v___x_1946_ = v___x_1941_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1949_, lean_object* v_declHint_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1949_, v_declHint_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1957_, lean_object* v_msg_1958_, lean_object* v_declHint_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v_a_1966_; lean_object* v___x_1967_; 
v___x_1965_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1958_, v_declHint_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1965_);
v___x_1967_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1957_, v_a_1966_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1968_, lean_object* v_msg_1969_, lean_object* v_declHint_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1968_, v_msg_1969_, v_declHint_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v_ref_1968_);
return v_res_1976_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1978_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_1979_ = l_Lean_stringToMessageData(v___x_1978_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1981_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_1982_ = l_Lean_stringToMessageData(v___x_1981_);
return v___x_1982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_1983_, lean_object* v_constName_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1990_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_1991_ = 0;
lean_inc(v_constName_1984_);
v___x_1992_ = l_Lean_MessageData_ofConstName(v_constName_1984_, v___x_1991_);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1990_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1983_, v___x_1995_, v_constName_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_1997_, lean_object* v_constName_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1997_, v_constName_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v_ref_1997_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v_ref_2011_; lean_object* v___x_2012_; 
v_ref_2011_ = lean_ctor_get(v___y_2008_, 5);
v___x_2012_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2011_, v_constName_2005_, v___y_2006_, v___y_2007_, v___y_2008_, v___y_2009_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
lean_dec(v___y_2015_);
lean_dec_ref(v___y_2014_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v___x_2026_; lean_object* v_env_2027_; uint8_t v___x_2028_; lean_object* v___x_2029_; 
v___x_2026_ = lean_st_ref_get(v___y_2024_);
v_env_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc_ref(v_env_2027_);
lean_dec(v___x_2026_);
v___x_2028_ = 0;
lean_inc(v_constName_2020_);
v___x_2029_ = l_Lean_Environment_findConstVal_x3f(v_env_2027_, v_constName_2020_, v___x_2028_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
return v___x_2030_;
}
else
{
lean_object* v_val_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v_constName_2020_);
v_val_2031_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2029_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_val_2031_);
lean_dec(v___x_2029_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set_tag(v___x_2033_, 0);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_val_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2046_, uint8_t v_s_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
lean_object* v___x_2051_; lean_object* v_env_2052_; lean_object* v_nextMacroScope_2053_; lean_object* v_ngen_2054_; lean_object* v_auxDeclNGen_2055_; lean_object* v_traceState_2056_; lean_object* v_messages_2057_; lean_object* v_infoState_2058_; lean_object* v_snapshotTasks_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2088_; 
v___x_2051_ = lean_st_ref_take(v___y_2049_);
v_env_2052_ = lean_ctor_get(v___x_2051_, 0);
v_nextMacroScope_2053_ = lean_ctor_get(v___x_2051_, 1);
v_ngen_2054_ = lean_ctor_get(v___x_2051_, 2);
v_auxDeclNGen_2055_ = lean_ctor_get(v___x_2051_, 3);
v_traceState_2056_ = lean_ctor_get(v___x_2051_, 4);
v_messages_2057_ = lean_ctor_get(v___x_2051_, 6);
v_infoState_2058_ = lean_ctor_get(v___x_2051_, 7);
v_snapshotTasks_2059_ = lean_ctor_get(v___x_2051_, 8);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; 
v_unused_2089_ = lean_ctor_get(v___x_2051_, 5);
lean_dec(v_unused_2089_);
v___x_2061_ = v___x_2051_;
v_isShared_2062_ = v_isSharedCheck_2088_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_snapshotTasks_2059_);
lean_inc(v_infoState_2058_);
lean_inc(v_messages_2057_);
lean_inc(v_traceState_2056_);
lean_inc(v_auxDeclNGen_2055_);
lean_inc(v_ngen_2054_);
lean_inc(v_nextMacroScope_2053_);
lean_inc(v_env_2052_);
lean_dec(v___x_2051_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2088_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2063_ = 0;
v___x_2064_ = lean_box(0);
v___x_2065_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2052_, v_declName_2046_, v_s_2047_, v___x_2063_, v___x_2064_);
v___x_2066_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 5, v___x_2066_);
lean_ctor_set(v___x_2061_, 0, v___x_2065_);
v___x_2068_ = v___x_2061_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_nextMacroScope_2053_);
lean_ctor_set(v_reuseFailAlloc_2087_, 2, v_ngen_2054_);
lean_ctor_set(v_reuseFailAlloc_2087_, 3, v_auxDeclNGen_2055_);
lean_ctor_set(v_reuseFailAlloc_2087_, 4, v_traceState_2056_);
lean_ctor_set(v_reuseFailAlloc_2087_, 5, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2087_, 6, v_messages_2057_);
lean_ctor_set(v_reuseFailAlloc_2087_, 7, v_infoState_2058_);
lean_ctor_set(v_reuseFailAlloc_2087_, 8, v_snapshotTasks_2059_);
v___x_2068_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v_mctx_2071_; lean_object* v_zetaDeltaFVarIds_2072_; lean_object* v_postponed_2073_; lean_object* v_diag_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2085_; 
v___x_2069_ = lean_st_ref_set(v___y_2049_, v___x_2068_);
v___x_2070_ = lean_st_ref_take(v___y_2048_);
v_mctx_2071_ = lean_ctor_get(v___x_2070_, 0);
v_zetaDeltaFVarIds_2072_ = lean_ctor_get(v___x_2070_, 2);
v_postponed_2073_ = lean_ctor_get(v___x_2070_, 3);
v_diag_2074_ = lean_ctor_get(v___x_2070_, 4);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2070_, 1);
lean_dec(v_unused_2086_);
v___x_2076_ = v___x_2070_;
v_isShared_2077_ = v_isSharedCheck_2085_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_diag_2074_);
lean_inc(v_postponed_2073_);
lean_inc(v_zetaDeltaFVarIds_2072_);
lean_inc(v_mctx_2071_);
lean_dec(v___x_2070_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2085_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_mctx_2071_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_zetaDeltaFVarIds_2072_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_postponed_2073_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_diag_2074_);
v___x_2080_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = lean_st_ref_set(v___y_2048_, v___x_2080_);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2083_, 0, v___x_2082_);
return v___x_2083_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2090_, lean_object* v_s_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v_s_boxed_2095_; lean_object* v_res_2096_; 
v_s_boxed_2095_ = lean_unbox(v_s_2091_);
v_res_2096_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2090_, v_s_boxed_2095_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec(v___y_2092_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
uint8_t v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = 0;
v___x_2104_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2097_, v___x_2103_, v___y_2099_, v___y_2101_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2111_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2114_ = l_Lean_stringToMessageData(v___x_2113_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2121_, lean_object* v_declName_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2128_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2129_ = l_Lean_MessageData_ofName(v_attrName_2121_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2128_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = 0;
v___x_2134_ = l_Lean_MessageData_ofConstName(v_declName_2122_, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2132_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2135_);
lean_ctor_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2137_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2139_, lean_object* v_declName_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2139_, v_declName_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
return v_res_2146_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2152_ = l_Lean_stringToMessageData(v___x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2153_, lean_object* v_declName_2154_, lean_object* v_asyncPrefix_x3f_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___y_2162_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2155_) == 0)
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_MessageData_nil;
v___y_2162_ = v___x_2175_;
goto v___jp_2161_;
}
else
{
lean_object* v_val_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v_val_2176_ = lean_ctor_get(v_asyncPrefix_x3f_2155_, 0);
lean_inc(v_val_2176_);
lean_dec_ref_known(v_asyncPrefix_x3f_2155_, 1);
v___x_2177_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2178_ = l_Lean_MessageData_ofName(v_val_2176_);
v___x_2179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___y_2162_ = v___x_2181_;
goto v___jp_2161_;
}
v___jp_2161_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; uint8_t v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2163_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2164_ = l_Lean_MessageData_ofName(v_attrName_2153_);
v___x_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = 0;
v___x_2169_ = l_Lean_MessageData_ofConstName(v_declName_2154_, v___x_2168_);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2167_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
v___x_2171_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2173_, 0, v___x_2172_);
lean_ctor_set(v___x_2173_, 1, v___y_2162_);
v___x_2174_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2173_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2182_, lean_object* v_declName_2183_, lean_object* v_asyncPrefix_x3f_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2182_, v_declName_2183_, v_asyncPrefix_x3f_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2191_, lean_object* v_decl_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___y_2199_; lean_object* v___y_2200_; lean_object* v___x_2241_; lean_object* v_env_2242_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v___y_2246_; lean_object* v___y_2247_; lean_object* v___x_2257_; 
v___x_2241_ = lean_st_ref_get(v___y_2196_);
v_env_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc_ref(v_env_2242_);
lean_dec(v___x_2241_);
v___x_2257_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2242_, v_decl_2192_);
if (lean_obj_tag(v___x_2257_) == 0)
{
v___y_2244_ = v___y_2193_;
v___y_2245_ = v___y_2194_;
v___y_2246_ = v___y_2195_;
v___y_2247_ = v___y_2196_;
goto v___jp_2243_;
}
else
{
lean_object* v_attr_2258_; lean_object* v_toAttributeImplCore_2259_; lean_object* v_name_2260_; lean_object* v___x_2261_; 
lean_dec_ref_known(v___x_2257_, 1);
lean_dec_ref(v_env_2242_);
v_attr_2258_ = lean_ctor_get(v_attr_2191_, 0);
lean_inc_ref(v_attr_2258_);
lean_dec_ref(v_attr_2191_);
v_toAttributeImplCore_2259_ = lean_ctor_get(v_attr_2258_, 0);
lean_inc_ref(v_toAttributeImplCore_2259_);
lean_dec_ref(v_attr_2258_);
v_name_2260_ = lean_ctor_get(v_toAttributeImplCore_2259_, 1);
lean_inc(v_name_2260_);
lean_dec_ref(v_toAttributeImplCore_2259_);
v___x_2261_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2260_, v_decl_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
return v___x_2261_;
}
v___jp_2198_:
{
lean_object* v___x_2201_; lean_object* v_ext_2202_; lean_object* v_toEnvExtension_2203_; lean_object* v_env_2204_; lean_object* v_nextMacroScope_2205_; lean_object* v_ngen_2206_; lean_object* v_auxDeclNGen_2207_; lean_object* v_traceState_2208_; lean_object* v_messages_2209_; lean_object* v_infoState_2210_; lean_object* v_snapshotTasks_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2239_; 
v___x_2201_ = lean_st_ref_take(v___y_2200_);
v_ext_2202_ = lean_ctor_get(v_attr_2191_, 1);
lean_inc_ref(v_ext_2202_);
lean_dec_ref(v_attr_2191_);
v_toEnvExtension_2203_ = lean_ctor_get(v_ext_2202_, 0);
v_env_2204_ = lean_ctor_get(v___x_2201_, 0);
v_nextMacroScope_2205_ = lean_ctor_get(v___x_2201_, 1);
v_ngen_2206_ = lean_ctor_get(v___x_2201_, 2);
v_auxDeclNGen_2207_ = lean_ctor_get(v___x_2201_, 3);
v_traceState_2208_ = lean_ctor_get(v___x_2201_, 4);
v_messages_2209_ = lean_ctor_get(v___x_2201_, 6);
v_infoState_2210_ = lean_ctor_get(v___x_2201_, 7);
v_snapshotTasks_2211_ = lean_ctor_get(v___x_2201_, 8);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2239_ == 0)
{
lean_object* v_unused_2240_; 
v_unused_2240_ = lean_ctor_get(v___x_2201_, 5);
lean_dec(v_unused_2240_);
v___x_2213_ = v___x_2201_;
v_isShared_2214_ = v_isSharedCheck_2239_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_snapshotTasks_2211_);
lean_inc(v_infoState_2210_);
lean_inc(v_messages_2209_);
lean_inc(v_traceState_2208_);
lean_inc(v_auxDeclNGen_2207_);
lean_inc(v_ngen_2206_);
lean_inc(v_nextMacroScope_2205_);
lean_inc(v_env_2204_);
lean_dec(v___x_2201_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2239_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_asyncMode_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v_asyncMode_2215_ = lean_ctor_get(v_toEnvExtension_2203_, 2);
lean_inc(v_asyncMode_2215_);
lean_inc(v_decl_2192_);
v___x_2216_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2202_, v_env_2204_, v_decl_2192_, v_asyncMode_2215_, v_decl_2192_);
lean_dec(v_asyncMode_2215_);
v___x_2217_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 5, v___x_2217_);
lean_ctor_set(v___x_2213_, 0, v___x_2216_);
v___x_2219_ = v___x_2213_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_nextMacroScope_2205_);
lean_ctor_set(v_reuseFailAlloc_2238_, 2, v_ngen_2206_);
lean_ctor_set(v_reuseFailAlloc_2238_, 3, v_auxDeclNGen_2207_);
lean_ctor_set(v_reuseFailAlloc_2238_, 4, v_traceState_2208_);
lean_ctor_set(v_reuseFailAlloc_2238_, 5, v___x_2217_);
lean_ctor_set(v_reuseFailAlloc_2238_, 6, v_messages_2209_);
lean_ctor_set(v_reuseFailAlloc_2238_, 7, v_infoState_2210_);
lean_ctor_set(v_reuseFailAlloc_2238_, 8, v_snapshotTasks_2211_);
v___x_2219_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v_mctx_2222_; lean_object* v_zetaDeltaFVarIds_2223_; lean_object* v_postponed_2224_; lean_object* v_diag_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2236_; 
v___x_2220_ = lean_st_ref_set(v___y_2200_, v___x_2219_);
v___x_2221_ = lean_st_ref_take(v___y_2199_);
v_mctx_2222_ = lean_ctor_get(v___x_2221_, 0);
v_zetaDeltaFVarIds_2223_ = lean_ctor_get(v___x_2221_, 2);
v_postponed_2224_ = lean_ctor_get(v___x_2221_, 3);
v_diag_2225_ = lean_ctor_get(v___x_2221_, 4);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; 
v_unused_2237_ = lean_ctor_get(v___x_2221_, 1);
lean_dec(v_unused_2237_);
v___x_2227_ = v___x_2221_;
v_isShared_2228_ = v_isSharedCheck_2236_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_diag_2225_);
lean_inc(v_postponed_2224_);
lean_inc(v_zetaDeltaFVarIds_2223_);
lean_inc(v_mctx_2222_);
lean_dec(v___x_2221_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2236_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
v___x_2229_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 1, v___x_2229_);
v___x_2231_ = v___x_2227_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_mctx_2222_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v___x_2229_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_zetaDeltaFVarIds_2223_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_postponed_2224_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_diag_2225_);
v___x_2231_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = lean_st_ref_set(v___y_2199_, v___x_2231_);
v___x_2233_ = lean_box(0);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
}
}
}
v___jp_2243_:
{
lean_object* v_ext_2248_; lean_object* v_toEnvExtension_2249_; lean_object* v_attr_2250_; lean_object* v_asyncMode_2251_; uint8_t v___x_2252_; 
v_ext_2248_ = lean_ctor_get(v_attr_2191_, 1);
v_toEnvExtension_2249_ = lean_ctor_get(v_ext_2248_, 0);
v_attr_2250_ = lean_ctor_get(v_attr_2191_, 0);
v_asyncMode_2251_ = lean_ctor_get(v_toEnvExtension_2249_, 2);
lean_inc(v_decl_2192_);
lean_inc_ref(v_env_2242_);
v___x_2252_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2242_, v_decl_2192_, v_asyncMode_2251_);
if (v___x_2252_ == 0)
{
lean_object* v_toAttributeImplCore_2253_; lean_object* v_name_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_inc_ref(v_attr_2250_);
lean_dec_ref(v_attr_2191_);
v_toAttributeImplCore_2253_ = lean_ctor_get(v_attr_2250_, 0);
lean_inc_ref(v_toAttributeImplCore_2253_);
lean_dec_ref(v_attr_2250_);
v_name_2254_ = lean_ctor_get(v_toAttributeImplCore_2253_, 1);
lean_inc(v_name_2254_);
lean_dec_ref(v_toAttributeImplCore_2253_);
v___x_2255_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2242_);
v___x_2256_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2254_, v_decl_2192_, v___x_2255_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
return v___x_2256_;
}
else
{
lean_dec_ref(v_env_2242_);
v___y_2199_ = v___y_2245_;
v___y_2200_ = v___y_2247_;
goto v___jp_2198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2262_, lean_object* v_decl_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2262_, v_decl_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v___x_2276_; lean_object* v_env_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; 
v___x_2276_ = lean_st_ref_get(v___y_2274_);
v_env_2277_ = lean_ctor_get(v___x_2276_, 0);
lean_inc_ref(v_env_2277_);
lean_dec(v___x_2276_);
v___x_2278_ = 0;
lean_inc(v_constName_2270_);
v___x_2279_ = l_Lean_Environment_find_x3f(v_env_2277_, v_constName_2270_, v___x_2278_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
return v___x_2280_;
}
else
{
lean_object* v_val_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
lean_dec(v_constName_2270_);
v_val_2281_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2279_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_val_2281_);
lean_dec(v___x_2279_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set_tag(v___x_2283_, 0);
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_val_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v_res_2295_; 
v_res_2295_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
return v_res_2295_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2299_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2300_ = lean_unsigned_to_nat(58u);
v___x_2301_ = lean_unsigned_to_nat(33u);
v___x_2302_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2303_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2304_ = l_mkPanicMessageWithDecl(v___x_2303_, v___x_2302_, v___x_2301_, v___x_2300_, v___x_2299_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2306_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2307_ = lean_unsigned_to_nat(60u);
v___x_2308_ = lean_unsigned_to_nat(30u);
v___x_2309_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2310_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2311_ = l_mkPanicMessageWithDecl(v___x_2310_, v___x_2309_, v___x_2308_, v___x_2307_, v___x_2306_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2312_, lean_object* v_indName_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2319_; 
lean_inc(v_indName_2313_);
v___x_2319_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2313_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
if (lean_obj_tag(v_a_2320_) == 5)
{
lean_object* v_val_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2505_; 
v_val_2321_ = lean_ctor_get(v_a_2320_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v_a_2320_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2323_ = v_a_2320_;
v_isShared_2324_ = v_isSharedCheck_2505_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_val_2321_);
lean_dec(v_a_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2505_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_inc(v_indName_2313_);
v___x_2325_ = l_Lean_mkCasesOnName(v_indName_2313_);
lean_inc(v___x_2325_);
v___x_2326_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2325_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v_name_2328_; lean_object* v_levelParams_2329_; lean_object* v_type_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v_name_2328_ = lean_ctor_get(v_a_2327_, 0);
lean_inc(v_name_2328_);
v_levelParams_2329_ = lean_ctor_get(v_a_2327_, 1);
lean_inc_n(v_levelParams_2329_, 2);
v_type_2330_ = lean_ctor_get(v_a_2327_, 2);
lean_inc_ref(v_type_2330_);
lean_dec(v_a_2327_);
v___x_2331_ = lean_box(0);
v___x_2332_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2329_, v___x_2331_);
if (lean_obj_tag(v___x_2332_) == 1)
{
lean_object* v_head_2333_; lean_object* v_tail_2334_; lean_object* v_numParams_2335_; lean_object* v_numIndices_2336_; lean_object* v_ctors_2337_; lean_object* v___f_2338_; lean_object* v___x_2340_; 
v_head_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_head_2333_);
v_tail_2334_ = lean_ctor_get(v___x_2332_, 1);
lean_inc(v_tail_2334_);
v_numParams_2335_ = lean_ctor_get(v_val_2321_, 1);
lean_inc_n(v_numParams_2335_, 2);
v_numIndices_2336_ = lean_ctor_get(v_val_2321_, 2);
lean_inc(v_numIndices_2336_);
v_ctors_2337_ = lean_ctor_get(v_val_2321_, 4);
lean_inc(v_ctors_2337_);
v___f_2338_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2338_, 0, v_numIndices_2336_);
lean_closure_set(v___f_2338_, 1, v_head_2333_);
lean_closure_set(v___f_2338_, 2, v_ctors_2337_);
lean_closure_set(v___f_2338_, 3, v_tail_2334_);
lean_closure_set(v___f_2338_, 4, v_numParams_2335_);
lean_closure_set(v___f_2338_, 5, v_indName_2313_);
lean_closure_set(v___f_2338_, 6, v_val_2321_);
lean_closure_set(v___f_2338_, 7, v___x_2332_);
lean_closure_set(v___f_2338_, 8, v___x_2325_);
lean_closure_set(v___f_2338_, 9, v_name_2328_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set_tag(v___x_2323_, 1);
lean_ctor_set(v___x_2323_, 0, v_numParams_2335_);
v___x_2340_ = v___x_2323_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_numParams_2335_);
v___x_2340_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
uint8_t v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = 0;
v___x_2342_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2330_, v___x_2340_, v___f_2338_, v___x_2341_, v___x_2341_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; lean_object* v___f_2345_; uint8_t v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2344_ = lean_box(v___x_2341_);
lean_inc(v_declName_2312_);
v___f_2345_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2345_, 0, v_a_2343_);
lean_closure_set(v___f_2345_, 1, v_declName_2312_);
lean_closure_set(v___f_2345_, 2, v_levelParams_2329_);
lean_closure_set(v___f_2345_, 3, v___x_2344_);
v___x_2346_ = l_Lean_isPrivateName(v_declName_2312_);
v___x_2347_ = lean_bool_not(v___x_2346_);
v___x_2348_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2345_, v___x_2347_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v___x_2349_; lean_object* v_env_2350_; lean_object* v_nextMacroScope_2351_; lean_object* v_ngen_2352_; lean_object* v_auxDeclNGen_2353_; lean_object* v_traceState_2354_; lean_object* v_messages_2355_; lean_object* v_infoState_2356_; lean_object* v_snapshotTasks_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref_known(v___x_2348_, 1);
v___x_2349_ = lean_st_ref_take(v_a_2317_);
v_env_2350_ = lean_ctor_get(v___x_2349_, 0);
v_nextMacroScope_2351_ = lean_ctor_get(v___x_2349_, 1);
v_ngen_2352_ = lean_ctor_get(v___x_2349_, 2);
v_auxDeclNGen_2353_ = lean_ctor_get(v___x_2349_, 3);
v_traceState_2354_ = lean_ctor_get(v___x_2349_, 4);
v_messages_2355_ = lean_ctor_get(v___x_2349_, 6);
v_infoState_2356_ = lean_ctor_get(v___x_2349_, 7);
v_snapshotTasks_2357_ = lean_ctor_get(v___x_2349_, 8);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2484_ == 0)
{
lean_object* v_unused_2485_; 
v_unused_2485_ = lean_ctor_get(v___x_2349_, 5);
lean_dec(v_unused_2485_);
v___x_2359_ = v___x_2349_;
v_isShared_2360_ = v_isSharedCheck_2484_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_snapshotTasks_2357_);
lean_inc(v_infoState_2356_);
lean_inc(v_messages_2355_);
lean_inc(v_traceState_2354_);
lean_inc(v_auxDeclNGen_2353_);
lean_inc(v_ngen_2352_);
lean_inc(v_nextMacroScope_2351_);
lean_inc(v_env_2350_);
lean_dec(v___x_2349_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2484_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2364_; 
lean_inc(v_declName_2312_);
v___x_2361_ = l_Lean_Meta_markMatcherLike(v_env_2350_, v_declName_2312_);
v___x_2362_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 5, v___x_2362_);
lean_ctor_set(v___x_2359_, 0, v___x_2361_);
v___x_2364_ = v___x_2359_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v_nextMacroScope_2351_);
lean_ctor_set(v_reuseFailAlloc_2483_, 2, v_ngen_2352_);
lean_ctor_set(v_reuseFailAlloc_2483_, 3, v_auxDeclNGen_2353_);
lean_ctor_set(v_reuseFailAlloc_2483_, 4, v_traceState_2354_);
lean_ctor_set(v_reuseFailAlloc_2483_, 5, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2483_, 6, v_messages_2355_);
lean_ctor_set(v_reuseFailAlloc_2483_, 7, v_infoState_2356_);
lean_ctor_set(v_reuseFailAlloc_2483_, 8, v_snapshotTasks_2357_);
v___x_2364_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v_mctx_2367_; lean_object* v_zetaDeltaFVarIds_2368_; lean_object* v_postponed_2369_; lean_object* v_diag_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2481_; 
v___x_2365_ = lean_st_ref_set(v_a_2317_, v___x_2364_);
v___x_2366_ = lean_st_ref_take(v_a_2315_);
v_mctx_2367_ = lean_ctor_get(v___x_2366_, 0);
v_zetaDeltaFVarIds_2368_ = lean_ctor_get(v___x_2366_, 2);
v_postponed_2369_ = lean_ctor_get(v___x_2366_, 3);
v_diag_2370_ = lean_ctor_get(v___x_2366_, 4);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v___x_2366_, 1);
lean_dec(v_unused_2482_);
v___x_2372_ = v___x_2366_;
v_isShared_2373_ = v_isSharedCheck_2481_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_diag_2370_);
lean_inc(v_postponed_2369_);
lean_inc(v_zetaDeltaFVarIds_2368_);
lean_inc(v_mctx_2367_);
lean_dec(v___x_2366_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2481_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2374_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 1, v___x_2374_);
v___x_2376_ = v___x_2372_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_mctx_2367_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_zetaDeltaFVarIds_2368_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_postponed_2369_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v_diag_2370_);
v___x_2376_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v_env_2379_; lean_object* v_nextMacroScope_2380_; lean_object* v_ngen_2381_; lean_object* v_auxDeclNGen_2382_; lean_object* v_traceState_2383_; lean_object* v_messages_2384_; lean_object* v_infoState_2385_; lean_object* v_snapshotTasks_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2478_; 
v___x_2377_ = lean_st_ref_set(v_a_2315_, v___x_2376_);
v___x_2378_ = lean_st_ref_take(v_a_2317_);
v_env_2379_ = lean_ctor_get(v___x_2378_, 0);
v_nextMacroScope_2380_ = lean_ctor_get(v___x_2378_, 1);
v_ngen_2381_ = lean_ctor_get(v___x_2378_, 2);
v_auxDeclNGen_2382_ = lean_ctor_get(v___x_2378_, 3);
v_traceState_2383_ = lean_ctor_get(v___x_2378_, 4);
v_messages_2384_ = lean_ctor_get(v___x_2378_, 6);
v_infoState_2385_ = lean_ctor_get(v___x_2378_, 7);
v_snapshotTasks_2386_ = lean_ctor_get(v___x_2378_, 8);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v___x_2378_, 5);
lean_dec(v_unused_2479_);
v___x_2388_ = v___x_2378_;
v_isShared_2389_ = v_isSharedCheck_2478_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_snapshotTasks_2386_);
lean_inc(v_infoState_2385_);
lean_inc(v_messages_2384_);
lean_inc(v_traceState_2383_);
lean_inc(v_auxDeclNGen_2382_);
lean_inc(v_ngen_2381_);
lean_inc(v_nextMacroScope_2380_);
lean_inc(v_env_2379_);
lean_dec(v___x_2378_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2478_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2392_; 
lean_inc(v_declName_2312_);
v___x_2390_ = l_Lean_markAuxRecursor(v_env_2379_, v_declName_2312_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 5, v___x_2362_);
lean_ctor_set(v___x_2388_, 0, v___x_2390_);
v___x_2392_ = v___x_2388_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v_nextMacroScope_2380_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_ngen_2381_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_auxDeclNGen_2382_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_traceState_2383_);
lean_ctor_set(v_reuseFailAlloc_2477_, 5, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2477_, 6, v_messages_2384_);
lean_ctor_set(v_reuseFailAlloc_2477_, 7, v_infoState_2385_);
lean_ctor_set(v_reuseFailAlloc_2477_, 8, v_snapshotTasks_2386_);
v___x_2392_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_mctx_2395_; lean_object* v_zetaDeltaFVarIds_2396_; lean_object* v_postponed_2397_; lean_object* v_diag_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2475_; 
v___x_2393_ = lean_st_ref_set(v_a_2317_, v___x_2392_);
v___x_2394_ = lean_st_ref_take(v_a_2315_);
v_mctx_2395_ = lean_ctor_get(v___x_2394_, 0);
v_zetaDeltaFVarIds_2396_ = lean_ctor_get(v___x_2394_, 2);
v_postponed_2397_ = lean_ctor_get(v___x_2394_, 3);
v_diag_2398_ = lean_ctor_get(v___x_2394_, 4);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v___x_2394_, 1);
lean_dec(v_unused_2476_);
v___x_2400_ = v___x_2394_;
v_isShared_2401_ = v_isSharedCheck_2475_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_diag_2398_);
lean_inc(v_postponed_2397_);
lean_inc(v_zetaDeltaFVarIds_2396_);
lean_inc(v_mctx_2395_);
lean_dec(v___x_2394_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2475_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 1, v___x_2374_);
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_mctx_2395_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_zetaDeltaFVarIds_2396_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_postponed_2397_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_diag_2398_);
v___x_2403_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v_env_2406_; lean_object* v_nextMacroScope_2407_; lean_object* v_ngen_2408_; lean_object* v_auxDeclNGen_2409_; lean_object* v_traceState_2410_; lean_object* v_messages_2411_; lean_object* v_infoState_2412_; lean_object* v_snapshotTasks_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2472_; 
v___x_2404_ = lean_st_ref_set(v_a_2315_, v___x_2403_);
v___x_2405_ = lean_st_ref_take(v_a_2317_);
v_env_2406_ = lean_ctor_get(v___x_2405_, 0);
v_nextMacroScope_2407_ = lean_ctor_get(v___x_2405_, 1);
v_ngen_2408_ = lean_ctor_get(v___x_2405_, 2);
v_auxDeclNGen_2409_ = lean_ctor_get(v___x_2405_, 3);
v_traceState_2410_ = lean_ctor_get(v___x_2405_, 4);
v_messages_2411_ = lean_ctor_get(v___x_2405_, 6);
v_infoState_2412_ = lean_ctor_get(v___x_2405_, 7);
v_snapshotTasks_2413_ = lean_ctor_get(v___x_2405_, 8);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; 
v_unused_2473_ = lean_ctor_get(v___x_2405_, 5);
lean_dec(v_unused_2473_);
v___x_2415_ = v___x_2405_;
v_isShared_2416_ = v_isSharedCheck_2472_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_snapshotTasks_2413_);
lean_inc(v_infoState_2412_);
lean_inc(v_messages_2411_);
lean_inc(v_traceState_2410_);
lean_inc(v_auxDeclNGen_2409_);
lean_inc(v_ngen_2408_);
lean_inc(v_nextMacroScope_2407_);
lean_inc(v_env_2406_);
lean_dec(v___x_2405_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2472_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
lean_inc(v_declName_2312_);
v___x_2417_ = l_Lean_Meta_addToCompletionBlackList(v_env_2406_, v_declName_2312_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 5, v___x_2362_);
lean_ctor_set(v___x_2415_, 0, v___x_2417_);
v___x_2419_ = v___x_2415_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_nextMacroScope_2407_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_ngen_2408_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v_auxDeclNGen_2409_);
lean_ctor_set(v_reuseFailAlloc_2471_, 4, v_traceState_2410_);
lean_ctor_set(v_reuseFailAlloc_2471_, 5, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2471_, 6, v_messages_2411_);
lean_ctor_set(v_reuseFailAlloc_2471_, 7, v_infoState_2412_);
lean_ctor_set(v_reuseFailAlloc_2471_, 8, v_snapshotTasks_2413_);
v___x_2419_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v_mctx_2422_; lean_object* v_zetaDeltaFVarIds_2423_; lean_object* v_postponed_2424_; lean_object* v_diag_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2469_; 
v___x_2420_ = lean_st_ref_set(v_a_2317_, v___x_2419_);
v___x_2421_ = lean_st_ref_take(v_a_2315_);
v_mctx_2422_ = lean_ctor_get(v___x_2421_, 0);
v_zetaDeltaFVarIds_2423_ = lean_ctor_get(v___x_2421_, 2);
v_postponed_2424_ = lean_ctor_get(v___x_2421_, 3);
v_diag_2425_ = lean_ctor_get(v___x_2421_, 4);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2469_ == 0)
{
lean_object* v_unused_2470_; 
v_unused_2470_ = lean_ctor_get(v___x_2421_, 1);
lean_dec(v_unused_2470_);
v___x_2427_ = v___x_2421_;
v_isShared_2428_ = v_isSharedCheck_2469_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_diag_2425_);
lean_inc(v_postponed_2424_);
lean_inc(v_zetaDeltaFVarIds_2423_);
lean_inc(v_mctx_2422_);
lean_dec(v___x_2421_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2469_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v___x_2374_);
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_mctx_2422_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_zetaDeltaFVarIds_2423_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_postponed_2424_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v_diag_2425_);
v___x_2430_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v_env_2433_; lean_object* v_nextMacroScope_2434_; lean_object* v_ngen_2435_; lean_object* v_auxDeclNGen_2436_; lean_object* v_traceState_2437_; lean_object* v_messages_2438_; lean_object* v_infoState_2439_; lean_object* v_snapshotTasks_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2466_; 
v___x_2431_ = lean_st_ref_set(v_a_2315_, v___x_2430_);
v___x_2432_ = lean_st_ref_take(v_a_2317_);
v_env_2433_ = lean_ctor_get(v___x_2432_, 0);
v_nextMacroScope_2434_ = lean_ctor_get(v___x_2432_, 1);
v_ngen_2435_ = lean_ctor_get(v___x_2432_, 2);
v_auxDeclNGen_2436_ = lean_ctor_get(v___x_2432_, 3);
v_traceState_2437_ = lean_ctor_get(v___x_2432_, 4);
v_messages_2438_ = lean_ctor_get(v___x_2432_, 6);
v_infoState_2439_ = lean_ctor_get(v___x_2432_, 7);
v_snapshotTasks_2440_ = lean_ctor_get(v___x_2432_, 8);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; 
v_unused_2467_ = lean_ctor_get(v___x_2432_, 5);
lean_dec(v_unused_2467_);
v___x_2442_ = v___x_2432_;
v_isShared_2443_ = v_isSharedCheck_2466_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snapshotTasks_2440_);
lean_inc(v_infoState_2439_);
lean_inc(v_messages_2438_);
lean_inc(v_traceState_2437_);
lean_inc(v_auxDeclNGen_2436_);
lean_inc(v_ngen_2435_);
lean_inc(v_nextMacroScope_2434_);
lean_inc(v_env_2433_);
lean_dec(v___x_2432_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2466_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
lean_inc(v_declName_2312_);
v___x_2444_ = l_Lean_addProtected(v_env_2433_, v_declName_2312_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 5, v___x_2362_);
lean_ctor_set(v___x_2442_, 0, v___x_2444_);
v___x_2446_ = v___x_2442_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_nextMacroScope_2434_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_ngen_2435_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v_auxDeclNGen_2436_);
lean_ctor_set(v_reuseFailAlloc_2465_, 4, v_traceState_2437_);
lean_ctor_set(v_reuseFailAlloc_2465_, 5, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2465_, 6, v_messages_2438_);
lean_ctor_set(v_reuseFailAlloc_2465_, 7, v_infoState_2439_);
lean_ctor_set(v_reuseFailAlloc_2465_, 8, v_snapshotTasks_2440_);
v___x_2446_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v_mctx_2449_; lean_object* v_zetaDeltaFVarIds_2450_; lean_object* v_postponed_2451_; lean_object* v_diag_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2463_; 
v___x_2447_ = lean_st_ref_set(v_a_2317_, v___x_2446_);
v___x_2448_ = lean_st_ref_take(v_a_2315_);
v_mctx_2449_ = lean_ctor_get(v___x_2448_, 0);
v_zetaDeltaFVarIds_2450_ = lean_ctor_get(v___x_2448_, 2);
v_postponed_2451_ = lean_ctor_get(v___x_2448_, 3);
v_diag_2452_ = lean_ctor_get(v___x_2448_, 4);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v___x_2448_, 1);
lean_dec(v_unused_2464_);
v___x_2454_ = v___x_2448_;
v_isShared_2455_ = v_isSharedCheck_2463_;
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
v_isShared_2455_ = v_isSharedCheck_2463_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 1, v___x_2374_);
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_mctx_2449_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_zetaDeltaFVarIds_2450_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v_postponed_2451_);
lean_ctor_set(v_reuseFailAlloc_2462_, 4, v_diag_2452_);
v___x_2457_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2458_ = lean_st_ref_set(v_a_2315_, v___x_2457_);
v___x_2459_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2312_);
v___x_2460_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2459_, v_declName_2312_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v___x_2461_; 
lean_dec_ref_known(v___x_2460_, 1);
v___x_2461_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2312_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
return v___x_2461_;
}
else
{
lean_dec(v_declName_2312_);
return v___x_2460_;
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
lean_dec(v_declName_2312_);
return v___x_2348_;
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v_levelParams_2329_);
lean_dec(v_declName_2312_);
v_a_2486_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2342_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2342_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
else
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_dec(v___x_2332_);
lean_dec_ref(v_type_2330_);
lean_dec(v_levelParams_2329_);
lean_dec(v_name_2328_);
lean_dec(v___x_2325_);
lean_del_object(v___x_2323_);
lean_dec_ref(v_val_2321_);
lean_dec(v_indName_2313_);
lean_dec(v_declName_2312_);
v___x_2495_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2496_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2495_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
return v___x_2496_;
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v___x_2325_);
lean_del_object(v___x_2323_);
lean_dec_ref(v_val_2321_);
lean_dec(v_indName_2313_);
lean_dec(v_declName_2312_);
v_a_2497_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2326_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2326_);
v___x_2499_ = lean_box(0);
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
v_resetjp_2498_:
{
lean_object* v___x_2502_; 
if (v_isShared_2500_ == 0)
{
v___x_2502_ = v___x_2499_;
goto v_reusejp_2501_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_a_2497_);
v___x_2502_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2501_;
}
v_reusejp_2501_:
{
return v___x_2502_;
}
}
}
}
}
else
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v_a_2320_);
lean_dec(v_indName_2313_);
lean_dec(v_declName_2312_);
v___x_2506_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2507_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2506_, v_a_2314_, v_a_2315_, v_a_2316_, v_a_2317_);
return v___x_2507_;
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_indName_2313_);
lean_dec(v_declName_2312_);
v_a_2508_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2319_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2319_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2516_, lean_object* v_indName_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2516_, v_indName_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2524_, lean_object* v_name_2525_, lean_object* v_type_2526_, lean_object* v_k_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2525_, v_type_2526_, v_k_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2534_, lean_object* v_name_2535_, lean_object* v_type_2536_, lean_object* v_k_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v_res_2543_; 
v_res_2543_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2534_, v_name_2535_, v_type_2536_, v_k_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2544_, lean_object* v_params_2545_, lean_object* v_alts_2546_, lean_object* v___x_2547_, lean_object* v_ism2_2548_, lean_object* v_motive_2549_, lean_object* v_val_2550_, lean_object* v_indName_2551_, lean_object* v___x_2552_, lean_object* v___x_2553_, lean_object* v___x_2554_, lean_object* v_as_2555_, size_t v_sz_2556_, size_t v_i_2557_, lean_object* v_bs_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2544_, v_params_2545_, v_alts_2546_, v___x_2547_, v_ism2_2548_, v_motive_2549_, v_val_2550_, v_indName_2551_, v___x_2552_, v___x_2553_, v___x_2554_, v_sz_2556_, v_i_2557_, v_bs_2558_, v___y_2559_, v___y_2560_, v___y_2561_, v___y_2562_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2565_ = _args[0];
lean_object* v_params_2566_ = _args[1];
lean_object* v_alts_2567_ = _args[2];
lean_object* v___x_2568_ = _args[3];
lean_object* v_ism2_2569_ = _args[4];
lean_object* v_motive_2570_ = _args[5];
lean_object* v_val_2571_ = _args[6];
lean_object* v_indName_2572_ = _args[7];
lean_object* v___x_2573_ = _args[8];
lean_object* v___x_2574_ = _args[9];
lean_object* v___x_2575_ = _args[10];
lean_object* v_as_2576_ = _args[11];
lean_object* v_sz_2577_ = _args[12];
lean_object* v_i_2578_ = _args[13];
lean_object* v_bs_2579_ = _args[14];
lean_object* v___y_2580_ = _args[15];
lean_object* v___y_2581_ = _args[16];
lean_object* v___y_2582_ = _args[17];
lean_object* v___y_2583_ = _args[18];
lean_object* v___y_2584_ = _args[19];
_start:
{
size_t v_sz_boxed_2585_; size_t v_i_boxed_2586_; lean_object* v_res_2587_; 
v_sz_boxed_2585_ = lean_unbox_usize(v_sz_2577_);
lean_dec(v_sz_2577_);
v_i_boxed_2586_ = lean_unbox_usize(v_i_2578_);
lean_dec(v_i_2578_);
v_res_2587_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2565_, v_params_2566_, v_alts_2567_, v___x_2568_, v_ism2_2569_, v_motive_2570_, v_val_2571_, v_indName_2572_, v___x_2573_, v___x_2574_, v___x_2575_, v_as_2576_, v_sz_boxed_2585_, v_i_boxed_2586_, v_bs_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec_ref(v_as_2576_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2588_, lean_object* v_params_2589_, lean_object* v___x_2590_, lean_object* v_motive_2591_, lean_object* v_as_2592_, size_t v_sz_2593_, size_t v_i_2594_, lean_object* v_bs_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v___x_2601_; 
v___x_2601_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2588_, v_params_2589_, v___x_2590_, v_motive_2591_, v_sz_2593_, v_i_2594_, v_bs_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2602_, lean_object* v_params_2603_, lean_object* v___x_2604_, lean_object* v_motive_2605_, lean_object* v_as_2606_, lean_object* v_sz_2607_, lean_object* v_i_2608_, lean_object* v_bs_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
size_t v_sz_boxed_2615_; size_t v_i_boxed_2616_; lean_object* v_res_2617_; 
v_sz_boxed_2615_ = lean_unbox_usize(v_sz_2607_);
lean_dec(v_sz_2607_);
v_i_boxed_2616_ = lean_unbox_usize(v_i_2608_);
lean_dec(v_i_2608_);
v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2602_, v_params_2603_, v___x_2604_, v_motive_2605_, v_as_2606_, v_sz_boxed_2615_, v_i_boxed_2616_, v_bs_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_);
lean_dec(v___y_2613_);
lean_dec_ref(v___y_2612_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec_ref(v_as_2606_);
lean_dec_ref(v_params_2603_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2618_, uint8_t v_s_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_){
_start:
{
lean_object* v___x_2625_; 
v___x_2625_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2618_, v_s_2619_, v___y_2621_, v___y_2623_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2626_, lean_object* v_s_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
uint8_t v_s_boxed_2633_; lean_object* v_res_2634_; 
v_s_boxed_2633_ = lean_unbox(v_s_2627_);
v_res_2634_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2626_, v_s_boxed_2633_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
return v_res_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2635_, lean_object* v_constName_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2643_, lean_object* v_constName_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v_res_2650_; 
v_res_2650_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2643_, v_constName_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
lean_dec(v___y_2648_);
lean_dec_ref(v___y_2647_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
return v_res_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2651_, lean_object* v_attrName_2652_, lean_object* v_declName_2653_, lean_object* v_asyncPrefix_x3f_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2652_, v_declName_2653_, v_asyncPrefix_x3f_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2661_, lean_object* v_attrName_2662_, lean_object* v_declName_2663_, lean_object* v_asyncPrefix_x3f_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2661_, v_attrName_2662_, v_declName_2663_, v_asyncPrefix_x3f_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2671_, lean_object* v_attrName_2672_, lean_object* v_declName_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2672_, v_declName_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2680_, lean_object* v_attrName_2681_, lean_object* v_declName_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2680_, v_attrName_2681_, v_declName_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2689_, lean_object* v_ref_2690_, lean_object* v_constName_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2690_, v_constName_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2698_, lean_object* v_ref_2699_, lean_object* v_constName_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v_res_2706_; 
v_res_2706_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2698_, v_ref_2699_, v_constName_2700_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
lean_dec(v___y_2702_);
lean_dec_ref(v___y_2701_);
lean_dec(v_ref_2699_);
return v_res_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2707_, lean_object* v_msg_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2715_, lean_object* v_msg_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2715_, v_msg_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec(v___y_2718_);
lean_dec_ref(v___y_2717_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2723_, lean_object* v_ref_2724_, lean_object* v_msg_2725_, lean_object* v_declHint_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2724_, v_msg_2725_, v_declHint_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2733_, lean_object* v_ref_2734_, lean_object* v_msg_2735_, lean_object* v_declHint_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2733_, v_ref_2734_, v_msg_2735_, v_declHint_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_);
lean_dec(v___y_2740_);
lean_dec_ref(v___y_2739_);
lean_dec(v___y_2738_);
lean_dec_ref(v___y_2737_);
lean_dec(v_ref_2734_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2743_, lean_object* v_declHint_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2743_, v_declHint_2744_, v___y_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2751_, lean_object* v_declHint_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2751_, v_declHint_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2759_, lean_object* v_ref_2760_, lean_object* v_msg_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2760_, v_msg_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2768_, lean_object* v_ref_2769_, lean_object* v_msg_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2768_, v_ref_2769_, v_msg_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v_ref_2769_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2777_, lean_object* v___y_2778_){
_start:
{
uint8_t v___x_2780_; uint8_t v___x_2781_; 
v___x_2780_ = l_Lean_Expr_hasMVar(v_e_2777_);
v___x_2781_ = lean_bool_not(v___x_2780_);
if (v___x_2781_ == 0)
{
lean_object* v___x_2782_; lean_object* v_mctx_2783_; lean_object* v___x_2784_; lean_object* v_fst_2785_; lean_object* v_snd_2786_; lean_object* v___x_2787_; lean_object* v_cache_2788_; lean_object* v_zetaDeltaFVarIds_2789_; lean_object* v_postponed_2790_; lean_object* v_diag_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2800_; 
v___x_2782_ = lean_st_ref_get(v___y_2778_);
v_mctx_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc_ref(v_mctx_2783_);
lean_dec(v___x_2782_);
v___x_2784_ = l_Lean_instantiateMVarsCore(v_mctx_2783_, v_e_2777_);
v_fst_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_fst_2785_);
v_snd_2786_ = lean_ctor_get(v___x_2784_, 1);
lean_inc(v_snd_2786_);
lean_dec_ref(v___x_2784_);
v___x_2787_ = lean_st_ref_take(v___y_2778_);
v_cache_2788_ = lean_ctor_get(v___x_2787_, 1);
v_zetaDeltaFVarIds_2789_ = lean_ctor_get(v___x_2787_, 2);
v_postponed_2790_ = lean_ctor_get(v___x_2787_, 3);
v_diag_2791_ = lean_ctor_get(v___x_2787_, 4);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; 
v_unused_2801_ = lean_ctor_get(v___x_2787_, 0);
lean_dec(v_unused_2801_);
v___x_2793_ = v___x_2787_;
v_isShared_2794_ = v_isSharedCheck_2800_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_diag_2791_);
lean_inc(v_postponed_2790_);
lean_inc(v_zetaDeltaFVarIds_2789_);
lean_inc(v_cache_2788_);
lean_dec(v___x_2787_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2800_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v_snd_2786_);
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_snd_2786_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_cache_2788_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_zetaDeltaFVarIds_2789_);
lean_ctor_set(v_reuseFailAlloc_2799_, 3, v_postponed_2790_);
lean_ctor_set(v_reuseFailAlloc_2799_, 4, v_diag_2791_);
v___x_2796_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_st_ref_set(v___y_2778_, v___x_2796_);
v___x_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2798_, 0, v_fst_2785_);
return v___x_2798_;
}
}
}
else
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2802_, 0, v_e_2777_);
return v___x_2802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2803_, v___y_2804_);
lean_dec(v___y_2804_);
return v_res_2806_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2807_, v___y_2809_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
lean_dec(v___y_2818_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2821_, lean_object* v_info_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v_env_2827_; lean_object* v_nextMacroScope_2828_; lean_object* v_ngen_2829_; lean_object* v_auxDeclNGen_2830_; lean_object* v_traceState_2831_; lean_object* v_messages_2832_; lean_object* v_infoState_2833_; lean_object* v_snapshotTasks_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2861_; 
v___x_2826_ = lean_st_ref_take(v___y_2824_);
v_env_2827_ = lean_ctor_get(v___x_2826_, 0);
v_nextMacroScope_2828_ = lean_ctor_get(v___x_2826_, 1);
v_ngen_2829_ = lean_ctor_get(v___x_2826_, 2);
v_auxDeclNGen_2830_ = lean_ctor_get(v___x_2826_, 3);
v_traceState_2831_ = lean_ctor_get(v___x_2826_, 4);
v_messages_2832_ = lean_ctor_get(v___x_2826_, 6);
v_infoState_2833_ = lean_ctor_get(v___x_2826_, 7);
v_snapshotTasks_2834_ = lean_ctor_get(v___x_2826_, 8);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2861_ == 0)
{
lean_object* v_unused_2862_; 
v_unused_2862_ = lean_ctor_get(v___x_2826_, 5);
lean_dec(v_unused_2862_);
v___x_2836_ = v___x_2826_;
v_isShared_2837_ = v_isSharedCheck_2861_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_snapshotTasks_2834_);
lean_inc(v_infoState_2833_);
lean_inc(v_messages_2832_);
lean_inc(v_traceState_2831_);
lean_inc(v_auxDeclNGen_2830_);
lean_inc(v_ngen_2829_);
lean_inc(v_nextMacroScope_2828_);
lean_inc(v_env_2827_);
lean_dec(v___x_2826_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2861_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2838_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2827_, v_matcherName_2821_, v_info_2822_);
v___x_2839_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 5, v___x_2839_);
lean_ctor_set(v___x_2836_, 0, v___x_2838_);
v___x_2841_ = v___x_2836_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2838_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v_nextMacroScope_2828_);
lean_ctor_set(v_reuseFailAlloc_2860_, 2, v_ngen_2829_);
lean_ctor_set(v_reuseFailAlloc_2860_, 3, v_auxDeclNGen_2830_);
lean_ctor_set(v_reuseFailAlloc_2860_, 4, v_traceState_2831_);
lean_ctor_set(v_reuseFailAlloc_2860_, 5, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2860_, 6, v_messages_2832_);
lean_ctor_set(v_reuseFailAlloc_2860_, 7, v_infoState_2833_);
lean_ctor_set(v_reuseFailAlloc_2860_, 8, v_snapshotTasks_2834_);
v___x_2841_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v_mctx_2844_; lean_object* v_zetaDeltaFVarIds_2845_; lean_object* v_postponed_2846_; lean_object* v_diag_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2858_; 
v___x_2842_ = lean_st_ref_set(v___y_2824_, v___x_2841_);
v___x_2843_ = lean_st_ref_take(v___y_2823_);
v_mctx_2844_ = lean_ctor_get(v___x_2843_, 0);
v_zetaDeltaFVarIds_2845_ = lean_ctor_get(v___x_2843_, 2);
v_postponed_2846_ = lean_ctor_get(v___x_2843_, 3);
v_diag_2847_ = lean_ctor_get(v___x_2843_, 4);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v___x_2843_, 1);
lean_dec(v_unused_2859_);
v___x_2849_ = v___x_2843_;
v_isShared_2850_ = v_isSharedCheck_2858_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_diag_2847_);
lean_inc(v_postponed_2846_);
lean_inc(v_zetaDeltaFVarIds_2845_);
lean_inc(v_mctx_2844_);
lean_dec(v___x_2843_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2858_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2851_; lean_object* v___x_2853_; 
v___x_2851_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2850_ == 0)
{
lean_ctor_set(v___x_2849_, 1, v___x_2851_);
v___x_2853_ = v___x_2849_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_mctx_2844_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v___x_2851_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_zetaDeltaFVarIds_2845_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_postponed_2846_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_diag_2847_);
v___x_2853_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2854_ = lean_st_ref_set(v___y_2823_, v___x_2853_);
v___x_2855_ = lean_box(0);
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2863_, lean_object* v_info_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2863_, v_info_2864_, v___y_2865_, v___y_2866_);
lean_dec(v___y_2866_);
lean_dec(v___y_2865_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2869_, lean_object* v_info_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2869_, v_info_2870_, v___y_2872_, v___y_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2877_, lean_object* v_info_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2877_, v_info_2878_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2885_, lean_object* v___x_2886_, lean_object* v_newEqs1_2887_, uint8_t v___x_2888_, uint8_t v___x_2889_, uint8_t v___x_2890_, lean_object* v_ism1_x27_2891_, lean_object* v_ism2_x27_2892_, lean_object* v_newRefls1_2893_, lean_object* v_newEqs2_2894_, lean_object* v_newRefls2_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2901_ = l_Lean_mkAppN(v_motive_2885_, v___x_2886_);
v___x_2902_ = l_Array_append___redArg(v_newEqs1_2887_, v_newEqs2_2894_);
v___x_2903_ = l_Lean_Meta_mkForallFVars(v___x_2902_, v___x_2901_, v___x_2888_, v___x_2889_, v___x_2889_, v___x_2890_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec_ref(v___x_2902_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref_known(v___x_2903_, 1);
v___x_2905_ = l_Array_append___redArg(v_ism1_x27_2891_, v_ism2_x27_2892_);
v___x_2906_ = l_Lean_Meta_mkLambdaFVars(v___x_2905_, v_a_2904_, v___x_2888_, v___x_2889_, v___x_2888_, v___x_2889_, v___x_2890_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
lean_dec_ref(v___x_2905_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2916_; 
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2909_ = v___x_2906_;
v_isShared_2910_ = v_isSharedCheck_2916_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2906_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2916_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2914_; 
v___x_2911_ = l_Array_append___redArg(v_newRefls1_2893_, v_newRefls2_2895_);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v_a_2907_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 0, v___x_2912_);
v___x_2914_ = v___x_2909_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref(v_newRefls1_2893_);
v_a_2917_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2906_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2906_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2922_; 
if (v_isShared_2920_ == 0)
{
v___x_2922_ = v___x_2919_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec_ref(v_newRefls1_2893_);
lean_dec_ref(v_ism1_x27_2891_);
v_a_2925_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2903_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2903_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2933_, lean_object* v___x_2934_, lean_object* v_newEqs1_2935_, lean_object* v___x_2936_, lean_object* v___x_2937_, lean_object* v___x_2938_, lean_object* v_ism1_x27_2939_, lean_object* v_ism2_x27_2940_, lean_object* v_newRefls1_2941_, lean_object* v_newEqs2_2942_, lean_object* v_newRefls2_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
uint8_t v___x_15078__boxed_2949_; uint8_t v___x_15079__boxed_2950_; uint8_t v___x_15080__boxed_2951_; lean_object* v_res_2952_; 
v___x_15078__boxed_2949_ = lean_unbox(v___x_2936_);
v___x_15079__boxed_2950_ = lean_unbox(v___x_2937_);
v___x_15080__boxed_2951_ = lean_unbox(v___x_2938_);
v_res_2952_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2933_, v___x_2934_, v_newEqs1_2935_, v___x_15078__boxed_2949_, v___x_15079__boxed_2950_, v___x_15080__boxed_2951_, v_ism1_x27_2939_, v_ism2_x27_2940_, v_newRefls1_2941_, v_newEqs2_2942_, v_newRefls2_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec_ref(v_newRefls2_2943_);
lean_dec_ref(v_newEqs2_2942_);
lean_dec_ref(v_ism2_x27_2940_);
lean_dec_ref(v___x_2934_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2953_, lean_object* v___x_2954_, uint8_t v___x_2955_, uint8_t v___x_2956_, uint8_t v___x_2957_, lean_object* v_ism1_x27_2958_, lean_object* v_ism2_x27_2959_, lean_object* v_is_2960_, lean_object* v___x_2961_, lean_object* v_newEqs1_2962_, lean_object* v_newRefls1_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___f_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2969_ = lean_box(v___x_2955_);
v___x_2970_ = lean_box(v___x_2956_);
v___x_2971_ = lean_box(v___x_2957_);
lean_inc_ref(v_ism2_x27_2959_);
v___f_2972_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2972_, 0, v_motive_2953_);
lean_closure_set(v___f_2972_, 1, v___x_2954_);
lean_closure_set(v___f_2972_, 2, v_newEqs1_2962_);
lean_closure_set(v___f_2972_, 3, v___x_2969_);
lean_closure_set(v___f_2972_, 4, v___x_2970_);
lean_closure_set(v___f_2972_, 5, v___x_2971_);
lean_closure_set(v___f_2972_, 6, v_ism1_x27_2958_);
lean_closure_set(v___f_2972_, 7, v_ism2_x27_2959_);
lean_closure_set(v___f_2972_, 8, v_newRefls1_2963_);
v___x_2973_ = lean_array_push(v_is_2960_, v___x_2961_);
v___x_2974_ = l_Lean_Meta_withNewEqs___redArg(v___x_2973_, v_ism2_x27_2959_, v___f_2972_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2975_, lean_object* v___x_2976_, lean_object* v___x_2977_, lean_object* v___x_2978_, lean_object* v___x_2979_, lean_object* v_ism1_x27_2980_, lean_object* v_ism2_x27_2981_, lean_object* v_is_2982_, lean_object* v___x_2983_, lean_object* v_newEqs1_2984_, lean_object* v_newRefls1_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
uint8_t v___x_15169__boxed_2991_; uint8_t v___x_15170__boxed_2992_; uint8_t v___x_15171__boxed_2993_; lean_object* v_res_2994_; 
v___x_15169__boxed_2991_ = lean_unbox(v___x_2977_);
v___x_15170__boxed_2992_ = lean_unbox(v___x_2978_);
v___x_15171__boxed_2993_ = lean_unbox(v___x_2979_);
v_res_2994_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2975_, v___x_2976_, v___x_15169__boxed_2991_, v___x_15170__boxed_2992_, v___x_15171__boxed_2993_, v_ism1_x27_2980_, v_ism2_x27_2981_, v_is_2982_, v___x_2983_, v_newEqs1_2984_, v_newRefls1_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_2995_, uint8_t v___x_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_addDecl(v___x_2995_, v___x_2996_, v___y_2999_, v___y_3000_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3003_, lean_object* v___x_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
uint8_t v___x_15211__boxed_3010_; lean_object* v_res_3011_; 
v___x_15211__boxed_3010_ = lean_unbox(v___x_3004_);
v_res_3011_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3003_, v___x_15211__boxed_3010_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
return v_res_3011_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3014_ = l_Lean_stringToMessageData(v___x_3013_);
return v___x_3014_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3017_ = l_Lean_stringToMessageData(v___x_3016_);
return v___x_3017_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3023_ = lean_box(0);
v___x_3024_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3025_ = l_Lean_mkConst(v___x_3024_, v___x_3023_);
return v___x_3025_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3028_ = l_Lean_stringToMessageData(v___x_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3029_, lean_object* v_a_3030_, lean_object* v___x_3031_, lean_object* v_zs1_3032_, lean_object* v_snd_3033_, uint8_t v___x_3034_, uint8_t v___x_3035_, uint8_t v___x_3036_, lean_object* v_alts_3037_, lean_object* v_zs2_3038_, lean_object* v___ctorRet2_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = lean_array_get_borrowed(v___x_3029_, v_a_3030_, v___x_3031_);
lean_inc_ref(v_zs1_3032_);
v___x_3046_ = l_Array_append___redArg(v_zs1_3032_, v_zs2_3038_);
lean_inc(v___x_3045_);
v___x_3047_ = l_Lean_Meta_instantiateForall(v___x_3045_, v___x_3046_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref_known(v___x_3047_, 1);
v___x_3049_ = lean_box(0);
v___x_3050_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3048_, v___x_3049_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___x_3052_ = l_Lean_Expr_mvarId_x21(v_a_3051_);
v___x_3053_ = lean_array_get_size(v_snd_3033_);
v___x_3054_ = lean_box(0);
v___x_3055_ = lean_box(0);
lean_inc_ref(v___y_3042_);
v___x_3056_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3053_, v___x_3052_, v___x_3054_, v___x_3055_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
if (lean_obj_tag(v_a_3057_) == 1)
{
lean_object* v_val_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3105_; 
v_val_3058_ = lean_ctor_get(v_a_3057_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_a_3057_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3060_ = v_a_3057_;
v_isShared_3061_ = v_isSharedCheck_3105_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_val_3058_);
lean_dec(v_a_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3105_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v_fst_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3103_; 
v_fst_3062_ = lean_ctor_get(v_val_3058_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_val_3058_);
if (v_isSharedCheck_3103_ == 0)
{
lean_object* v_unused_3104_; 
v_unused_3104_ = lean_ctor_get(v_val_3058_, 1);
lean_dec(v_unused_3104_);
v___x_3064_ = v_val_3058_;
v_isShared_3065_ = v_isSharedCheck_3103_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_fst_3062_);
lean_dec(v_val_3058_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3103_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___y_3067_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v___x_3095_ = lean_array_get_borrowed(v___x_3029_, v_alts_3037_, v___x_3031_);
v___x_3096_ = lean_array_get_size(v_zs1_3032_);
lean_dec_ref(v_zs1_3032_);
v___x_3097_ = lean_unsigned_to_nat(0u);
v___x_3098_ = lean_nat_dec_eq(v___x_3096_, v___x_3097_);
if (v___x_3098_ == 0)
{
lean_inc(v___x_3095_);
v___y_3067_ = v___x_3095_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = lean_array_get_size(v_zs2_3038_);
v___x_3100_ = lean_nat_dec_eq(v___x_3099_, v___x_3097_);
if (v___x_3100_ == 0)
{
lean_inc(v___x_3095_);
v___y_3067_ = v___x_3095_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3095_);
v___x_3102_ = l_Lean_Expr_app___override(v___x_3095_, v___x_3101_);
v___y_3067_ = v___x_3102_;
goto v___jp_3066_;
}
}
v___jp_3066_:
{
uint8_t v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = 0;
v___x_3069_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3069_, 0, v___x_3068_);
lean_ctor_set_uint8(v___x_3069_, 1, v___x_3034_);
lean_ctor_set_uint8(v___x_3069_, 2, v___x_3035_);
lean_ctor_set_uint8(v___x_3069_, 3, v___x_3034_);
lean_inc_ref(v___y_3067_);
lean_inc(v_fst_3062_);
v___x_3070_ = l_Lean_MVarId_apply(v_fst_3062_, v___y_3067_, v___x_3069_, v___x_3055_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
if (lean_obj_tag(v_a_3071_) == 0)
{
lean_object* v___x_3072_; 
lean_dec_ref(v___y_3067_);
lean_del_object(v___x_3064_);
lean_dec(v_fst_3062_);
lean_del_object(v___x_3060_);
v___x_3072_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3051_, v___y_3041_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3074_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
v___x_3074_ = l_Lean_Meta_mkLambdaFVars(v___x_3046_, v_a_3073_, v___x_3035_, v___x_3034_, v___x_3035_, v___x_3034_, v___x_3036_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
lean_dec_ref(v___x_3046_);
return v___x_3074_;
}
else
{
lean_dec_ref(v___x_3046_);
return v___x_3072_;
}
}
else
{
lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3078_; 
lean_dec(v_a_3071_);
lean_dec(v_a_3051_);
lean_dec_ref(v___x_3046_);
v___x_3075_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3076_ = l_Lean_MessageData_ofExpr(v___y_3067_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set_tag(v___x_3064_, 7);
lean_ctor_set(v___x_3064_, 1, v___x_3076_);
lean_ctor_set(v___x_3064_, 0, v___x_3075_);
v___x_3078_ = v___x_3064_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3075_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3082_; 
v___x_3079_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3080_, 0, v___x_3078_);
lean_ctor_set(v___x_3080_, 1, v___x_3079_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 0, v_fst_3062_);
v___x_3082_ = v___x_3060_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_fst_3062_);
v___x_3082_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3080_);
lean_ctor_set(v___x_3083_, 1, v___x_3082_);
v___x_3084_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3083_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec_ref(v___y_3067_);
lean_del_object(v___x_3064_);
lean_dec(v_fst_3062_);
lean_del_object(v___x_3060_);
lean_dec(v_a_3051_);
lean_dec_ref(v___x_3046_);
v_a_3087_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3070_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3070_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_dec(v_a_3057_);
lean_dec(v_a_3051_);
lean_dec_ref(v___x_3046_);
lean_dec_ref(v_zs1_3032_);
v___x_3106_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3107_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3106_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_);
return v___x_3107_;
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v_a_3051_);
lean_dec_ref(v___x_3046_);
lean_dec_ref(v_zs1_3032_);
v_a_3108_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3056_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3056_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_dec_ref(v___x_3046_);
lean_dec_ref(v_zs1_3032_);
return v___x_3050_;
}
}
else
{
lean_dec_ref(v___x_3046_);
lean_dec_ref(v_zs1_3032_);
return v___x_3047_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3116_, lean_object* v_a_3117_, lean_object* v___x_3118_, lean_object* v_zs1_3119_, lean_object* v_snd_3120_, lean_object* v___x_3121_, lean_object* v___x_3122_, lean_object* v___x_3123_, lean_object* v_alts_3124_, lean_object* v_zs2_3125_, lean_object* v___ctorRet2_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
uint8_t v___x_15271__boxed_3132_; uint8_t v___x_15272__boxed_3133_; uint8_t v___x_15273__boxed_3134_; lean_object* v_res_3135_; 
v___x_15271__boxed_3132_ = lean_unbox(v___x_3121_);
v___x_15272__boxed_3133_ = lean_unbox(v___x_3122_);
v___x_15273__boxed_3134_ = lean_unbox(v___x_3123_);
v_res_3135_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3116_, v_a_3117_, v___x_3118_, v_zs1_3119_, v_snd_3120_, v___x_15271__boxed_3132_, v___x_15272__boxed_3133_, v___x_15273__boxed_3134_, v_alts_3124_, v_zs2_3125_, v___ctorRet2_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec_ref(v___ctorRet2_3126_);
lean_dec_ref(v_zs2_3125_);
lean_dec_ref(v_alts_3124_);
lean_dec_ref(v_snd_3120_);
lean_dec(v___x_3118_);
lean_dec_ref(v_a_3117_);
lean_dec_ref(v___x_3116_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3136_, lean_object* v_a_3137_, lean_object* v___x_3138_, lean_object* v_snd_3139_, uint8_t v___x_3140_, uint8_t v___x_3141_, uint8_t v___x_3142_, lean_object* v_alts_3143_, lean_object* v_a_3144_, lean_object* v_zs1_3145_, lean_object* v___ctorRet1_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___f_3155_; lean_object* v___x_3156_; 
v___x_3152_ = lean_box(v___x_3140_);
v___x_3153_ = lean_box(v___x_3141_);
v___x_3154_ = lean_box(v___x_3142_);
v___f_3155_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3155_, 0, v___x_3136_);
lean_closure_set(v___f_3155_, 1, v_a_3137_);
lean_closure_set(v___f_3155_, 2, v___x_3138_);
lean_closure_set(v___f_3155_, 3, v_zs1_3145_);
lean_closure_set(v___f_3155_, 4, v_snd_3139_);
lean_closure_set(v___f_3155_, 5, v___x_3152_);
lean_closure_set(v___f_3155_, 6, v___x_3153_);
lean_closure_set(v___f_3155_, 7, v___x_3154_);
lean_closure_set(v___f_3155_, 8, v_alts_3143_);
v___x_3156_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3144_, v___f_3155_, v___x_3141_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3157_, lean_object* v_a_3158_, lean_object* v___x_3159_, lean_object* v_snd_3160_, lean_object* v___x_3161_, lean_object* v___x_3162_, lean_object* v___x_3163_, lean_object* v_alts_3164_, lean_object* v_a_3165_, lean_object* v_zs1_3166_, lean_object* v___ctorRet1_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
uint8_t v___x_15470__boxed_3173_; uint8_t v___x_15471__boxed_3174_; uint8_t v___x_15472__boxed_3175_; lean_object* v_res_3176_; 
v___x_15470__boxed_3173_ = lean_unbox(v___x_3161_);
v___x_15471__boxed_3174_ = lean_unbox(v___x_3162_);
v___x_15472__boxed_3175_ = lean_unbox(v___x_3163_);
v_res_3176_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3157_, v_a_3158_, v___x_3159_, v_snd_3160_, v___x_15470__boxed_3173_, v___x_15471__boxed_3174_, v___x_15472__boxed_3175_, v_alts_3164_, v_a_3165_, v_zs1_3166_, v___ctorRet1_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec_ref(v___ctorRet1_3167_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3177_, lean_object* v_params_3178_, lean_object* v_a_3179_, lean_object* v_snd_3180_, lean_object* v_alts_3181_, size_t v_sz_3182_, size_t v_i_3183_, lean_object* v_bs_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
uint8_t v___x_3190_; 
v___x_3190_ = lean_usize_dec_lt(v_i_3183_, v_sz_3182_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; 
lean_dec_ref(v_alts_3181_);
lean_dec_ref(v_snd_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_tail_3177_);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v_bs_3184_);
return v___x_3191_;
}
else
{
lean_object* v_v_3192_; lean_object* v___x_3193_; lean_object* v_bs_x27_3194_; lean_object* v___y_3196_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v_v_3192_ = lean_array_uget(v_bs_3184_, v_i_3183_);
v___x_3193_ = lean_unsigned_to_nat(0u);
v_bs_x27_3194_ = lean_array_uset(v_bs_3184_, v_i_3183_, v___x_3193_);
lean_inc(v_tail_3177_);
v___x_3210_ = l_Lean_mkConst(v_v_3192_, v_tail_3177_);
v___x_3211_ = l_Lean_mkAppN(v___x_3210_, v_params_3178_);
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
v___x_3212_ = lean_infer_type(v___x_3211_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; lean_object* v___x_3214_; uint8_t v___x_3215_; uint8_t v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___f_3221_; lean_object* v___x_3222_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc_n(v_a_3213_, 2);
lean_dec_ref_known(v___x_3212_, 1);
v___x_3214_ = l_Lean_instInhabitedExpr;
v___x_3215_ = 0;
v___x_3216_ = 1;
v___x_3217_ = lean_usize_to_nat(v_i_3183_);
v___x_3218_ = lean_box(v___x_3190_);
v___x_3219_ = lean_box(v___x_3215_);
v___x_3220_ = lean_box(v___x_3216_);
lean_inc_ref(v_alts_3181_);
lean_inc_ref(v_snd_3180_);
lean_inc_ref(v_a_3179_);
v___f_3221_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3221_, 0, v___x_3214_);
lean_closure_set(v___f_3221_, 1, v_a_3179_);
lean_closure_set(v___f_3221_, 2, v___x_3217_);
lean_closure_set(v___f_3221_, 3, v_snd_3180_);
lean_closure_set(v___f_3221_, 4, v___x_3218_);
lean_closure_set(v___f_3221_, 5, v___x_3219_);
lean_closure_set(v___f_3221_, 6, v___x_3220_);
lean_closure_set(v___f_3221_, 7, v_alts_3181_);
lean_closure_set(v___f_3221_, 8, v_a_3213_);
v___x_3222_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3213_, v___f_3221_, v___x_3215_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
v___y_3196_ = v___x_3222_;
goto v___jp_3195_;
}
else
{
v___y_3196_ = v___x_3212_;
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
v___x_3199_ = lean_usize_add(v_i_3183_, v___x_3198_);
v___x_3200_ = lean_array_uset(v_bs_x27_3194_, v_i_3183_, v_a_3197_);
v_i_3183_ = v___x_3199_;
v_bs_3184_ = v___x_3200_;
goto _start;
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_dec_ref(v_bs_x27_3194_);
lean_dec_ref(v_alts_3181_);
lean_dec_ref(v_snd_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_tail_3177_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3223_, lean_object* v_params_3224_, lean_object* v_a_3225_, lean_object* v_snd_3226_, lean_object* v_alts_3227_, lean_object* v_sz_3228_, lean_object* v_i_3229_, lean_object* v_bs_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
size_t v_sz_boxed_3236_; size_t v_i_boxed_3237_; lean_object* v_res_3238_; 
v_sz_boxed_3236_ = lean_unbox_usize(v_sz_3228_);
lean_dec(v_sz_3228_);
v_i_boxed_3237_ = lean_unbox_usize(v_i_3229_);
lean_dec(v_i_3229_);
v_res_3238_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3223_, v_params_3224_, v_a_3225_, v_snd_3226_, v_alts_3227_, v_sz_boxed_3236_, v_i_boxed_3237_, v_bs_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec_ref(v_params_3224_);
return v_res_3238_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_box(0);
v___x_3240_ = lean_unsigned_to_nat(16u);
v___x_3241_ = lean_mk_array(v___x_3240_, v___x_3239_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3242_, lean_object* v___x_3243_, uint8_t v___x_3244_, uint8_t v___x_3245_, uint8_t v___x_3246_, lean_object* v_ism1_x27_3247_, lean_object* v_is_3248_, lean_object* v___x_3249_, lean_object* v___x_3250_, lean_object* v___x_3251_, lean_object* v___x_3252_, lean_object* v_params_3253_, lean_object* v___x_3254_, lean_object* v___x_3255_, lean_object* v_heq_3256_, lean_object* v_val_3257_, lean_object* v_tail_3258_, lean_object* v_alts_3259_, size_t v_sz_3260_, size_t v___x_3261_, lean_object* v___x_3262_, lean_object* v___x_3263_, lean_object* v_declName_3264_, lean_object* v_levelParams_3265_, lean_object* v___x_3266_, lean_object* v___x_3267_, lean_object* v_numIndices_3268_, lean_object* v_numParams_3269_, lean_object* v_snd_3270_, lean_object* v_ism2_x27_3271_, lean_object* v_x_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___f_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3278_ = lean_box(v___x_3244_);
v___x_3279_ = lean_box(v___x_3245_);
v___x_3280_ = lean_box(v___x_3246_);
lean_inc_ref(v___x_3249_);
lean_inc_ref_n(v_is_3248_, 2);
lean_inc_ref(v_ism1_x27_3247_);
lean_inc_ref(v_motive_3242_);
v___f_3281_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3281_, 0, v_motive_3242_);
lean_closure_set(v___f_3281_, 1, v___x_3243_);
lean_closure_set(v___f_3281_, 2, v___x_3278_);
lean_closure_set(v___f_3281_, 3, v___x_3279_);
lean_closure_set(v___f_3281_, 4, v___x_3280_);
lean_closure_set(v___f_3281_, 5, v_ism1_x27_3247_);
lean_closure_set(v___f_3281_, 6, v_ism2_x27_3271_);
lean_closure_set(v___f_3281_, 7, v_is_3248_);
lean_closure_set(v___f_3281_, 8, v___x_3249_);
lean_inc_ref(v___x_3250_);
v___x_3282_ = lean_array_push(v_is_3248_, v___x_3250_);
v___x_3283_ = l_Lean_Meta_withNewEqs___redArg(v___x_3282_, v_ism1_x27_3247_, v___f_3281_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v_fst_3285_; lean_object* v_snd_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3393_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3284_);
lean_dec_ref_known(v___x_3283_, 1);
v_fst_3285_ = lean_ctor_get(v_a_3284_, 0);
v_snd_3286_ = lean_ctor_get(v_a_3284_, 1);
v_isSharedCheck_3393_ = !lean_is_exclusive(v_a_3284_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3288_ = v_a_3284_;
v_isShared_3289_ = v_isSharedCheck_3393_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_snd_3286_);
lean_inc(v_fst_3285_);
lean_dec(v_a_3284_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3393_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3290_ = l_Lean_mkConst(v___x_3251_, v___x_3252_);
v___x_3291_ = l_Lean_mkAppN(v___x_3290_, v_params_3253_);
v___x_3292_ = l_Lean_Expr_app___override(v___x_3291_, v_fst_3285_);
lean_inc_ref(v_is_3248_);
v___x_3293_ = l_Array_append___redArg(v_is_3248_, v___x_3254_);
v___x_3294_ = l_Array_append___redArg(v___x_3293_, v_is_3248_);
v___x_3295_ = l_Array_append___redArg(v___x_3294_, v___x_3255_);
v___x_3296_ = l_Lean_mkAppN(v___x_3292_, v___x_3295_);
lean_dec_ref(v___x_3295_);
lean_inc_ref(v_heq_3256_);
v___x_3297_ = l_Lean_Expr_app___override(v___x_3296_, v_heq_3256_);
v___x_3298_ = l_Lean_InductiveVal_numCtors(v_val_3257_);
lean_inc_ref(v___x_3297_);
v___x_3299_ = l_Lean_Meta_inferArgumentTypesN(v___x_3298_, v___x_3297_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
lean_inc_ref(v_alts_3259_);
lean_inc(v_snd_3286_);
v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3258_, v_params_3253_, v_a_3300_, v_snd_3286_, v_alts_3259_, v_sz_3260_, v___x_3261_, v___x_3262_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v_a_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_a_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc(v_a_3302_);
lean_dec_ref_known(v___x_3301_, 1);
v___x_3303_ = l_Lean_mkAppN(v___x_3297_, v_a_3302_);
lean_dec(v_a_3302_);
v___x_3304_ = l_Lean_mkAppN(v___x_3303_, v_snd_3286_);
lean_dec(v_snd_3286_);
lean_inc_ref(v___x_3263_);
v___x_3305_ = lean_array_push(v___x_3263_, v_motive_3242_);
v___x_3306_ = l_Array_append___redArg(v_params_3253_, v___x_3305_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = l_Array_append___redArg(v___x_3306_, v_is_3248_);
lean_dec_ref(v_is_3248_);
v___x_3308_ = lean_unsigned_to_nat(2u);
v___x_3309_ = lean_mk_empty_array_with_capacity(v___x_3308_);
v___x_3310_ = lean_array_push(v___x_3309_, v___x_3250_);
v___x_3311_ = lean_array_push(v___x_3310_, v___x_3249_);
v___x_3312_ = l_Array_append___redArg(v___x_3307_, v___x_3311_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = lean_array_push(v___x_3263_, v_heq_3256_);
v___x_3314_ = l_Array_append___redArg(v___x_3312_, v___x_3313_);
lean_dec_ref(v___x_3313_);
v___x_3315_ = l_Array_append___redArg(v___x_3314_, v_alts_3259_);
lean_dec_ref(v_alts_3259_);
v___x_3316_ = l_Lean_Meta_mkLambdaFVars(v___x_3315_, v___x_3304_, v___x_3244_, v___x_3245_, v___x_3244_, v___x_3245_, v___x_3246_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec_ref(v___x_3315_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc_n(v_a_3317_, 2);
lean_dec_ref_known(v___x_3316_, 1);
lean_inc(v___y_3276_);
lean_inc_ref(v___y_3275_);
lean_inc(v___y_3274_);
lean_inc_ref(v___y_3273_);
v___x_3318_ = lean_infer_type(v_a_3317_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3360_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v___x_3320_ = lean_box(1);
lean_inc(v_declName_3264_);
v___x_3321_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3264_, v_levelParams_3265_, v_a_3319_, v_a_3317_, v___x_3320_, v___y_3276_);
v_a_3322_ = lean_ctor_get(v___x_3321_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3321_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3324_ = v___x_3321_;
v_isShared_3325_ = v_isSharedCheck_3360_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3321_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3360_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
lean_ctor_set_tag(v___x_3324_, 1);
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3328_; lean_object* v___f_3329_; uint8_t v___x_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; 
v___x_3328_ = lean_box(v___x_3244_);
lean_inc_ref(v___x_3327_);
v___f_3329_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3329_, 0, v___x_3327_);
lean_closure_set(v___f_3329_, 1, v___x_3328_);
v___x_3330_ = l_Lean_isPrivateName(v_declName_3264_);
v___x_3331_ = lean_bool_not(v___x_3330_);
v___x_3332_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3329_, v___x_3331_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3332_) == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3334_; 
lean_dec_ref_known(v___x_3332_, 1);
v___x_3333_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3264_);
v___x_3334_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3333_, v_declName_3264_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3357_; 
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v___x_3334_, 0);
lean_dec(v_unused_3358_);
v___x_3336_ = v___x_3334_;
v_isShared_3337_ = v_isSharedCheck_3357_;
goto v_resetjp_3335_;
}
else
{
lean_dec(v___x_3334_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3357_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3344_; 
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_mk_empty_array_with_capacity(v___x_3266_);
v___x_3340_ = lean_array_push(v___x_3339_, v___x_3338_);
v___x_3341_ = lean_array_push(v___x_3340_, v___x_3338_);
v___x_3342_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
lean_inc(v___x_3267_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 1, v___x_3342_);
lean_ctor_set(v___x_3288_, 0, v___x_3267_);
v___x_3344_ = v___x_3288_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3356_, 1, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
lean_object* v___x_3345_; lean_object* v___x_3347_; 
v___x_3345_ = lean_nat_add(v_numIndices_3268_, v___x_3266_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set_tag(v___x_3336_, 1);
lean_ctor_set(v___x_3336_, 0, v___x_3267_);
v___x_3347_ = v___x_3336_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3267_);
v___x_3347_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; uint8_t v___x_3351_; lean_object* v___x_3352_; 
v___x_3348_ = lean_array_push(v___x_3341_, v___x_3338_);
v___x_3349_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3349_, 0, v_numParams_3269_);
lean_ctor_set(v___x_3349_, 1, v___x_3345_);
lean_ctor_set(v___x_3349_, 2, v_snd_3270_);
lean_ctor_set(v___x_3349_, 3, v___x_3347_);
lean_ctor_set(v___x_3349_, 4, v___x_3348_);
lean_ctor_set(v___x_3349_, 5, v___x_3344_);
lean_inc_n(v_declName_3264_, 2);
v___x_3350_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3264_, v___x_3349_, v___y_3274_, v___y_3276_);
lean_dec_ref(v___x_3350_);
v___x_3351_ = 0;
v___x_3352_ = l_Lean_Meta_setInlineAttribute(v_declName_3264_, v___x_3351_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v___x_3353_; 
lean_dec_ref_known(v___x_3352_, 1);
v___x_3353_ = l_Lean_enableRealizationsForConst(v_declName_3264_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v___x_3354_; 
lean_dec_ref_known(v___x_3353_, 1);
v___x_3354_ = l_Lean_compileDecl(v___x_3327_, v___x_3245_, v___y_3275_, v___y_3276_);
return v___x_3354_;
}
else
{
lean_dec_ref(v___x_3327_);
return v___x_3353_;
}
}
else
{
lean_dec_ref(v___x_3327_);
lean_dec(v_declName_3264_);
return v___x_3352_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_3327_);
lean_del_object(v___x_3288_);
lean_dec_ref(v_snd_3270_);
lean_dec(v_numParams_3269_);
lean_dec(v___x_3267_);
lean_dec(v_declName_3264_);
return v___x_3334_;
}
}
else
{
lean_dec_ref(v___x_3327_);
lean_del_object(v___x_3288_);
lean_dec_ref(v_snd_3270_);
lean_dec(v_numParams_3269_);
lean_dec(v___x_3267_);
lean_dec(v_declName_3264_);
return v___x_3332_;
}
}
}
}
else
{
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3368_; 
lean_dec(v_a_3317_);
lean_del_object(v___x_3288_);
lean_dec_ref(v_snd_3270_);
lean_dec(v_numParams_3269_);
lean_dec(v___x_3267_);
lean_dec(v_levelParams_3265_);
lean_dec(v_declName_3264_);
v_a_3361_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3318_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3318_);
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
lean_del_object(v___x_3288_);
lean_dec_ref(v_snd_3270_);
lean_dec(v_numParams_3269_);
lean_dec(v___x_3267_);
lean_dec(v_levelParams_3265_);
lean_dec(v_declName_3264_);
v_a_3369_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3316_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3316_);
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
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec_ref(v___x_3297_);
lean_del_object(v___x_3288_);
lean_dec(v_snd_3286_);
lean_dec_ref(v_snd_3270_);
lean_dec(v_numParams_3269_);
lean_dec(v___x_3267_);
lean_dec(v_levelParams_3265_);
lean_dec(v_declName_3264_);
lean_dec_ref(v___x_3263_);
lean_dec_ref(v_alts_3259_);
lean_dec_ref(v_heq_3256_);
lean_dec_ref(v_params_3253_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v_is_3248_);
lean_dec_ref(v_motive_3242_);
v_a_3377_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3301_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3301_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v_a_3385_; lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3392_; 
lean_dec_ref(v___x_3297_);
lean_del_object(v___x_3288_);
lean_dec(v_snd_3286_);
lean_dec_ref(v_snd_3270_);
lean_dec(v_numParams_3269_);
lean_dec(v___x_3267_);
lean_dec(v_levelParams_3265_);
lean_dec(v_declName_3264_);
lean_dec_ref(v___x_3263_);
lean_dec_ref(v___x_3262_);
lean_dec_ref(v_alts_3259_);
lean_dec(v_tail_3258_);
lean_dec_ref(v_heq_3256_);
lean_dec_ref(v_params_3253_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v_is_3248_);
lean_dec_ref(v_motive_3242_);
v_a_3385_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3387_ = v___x_3299_;
v_isShared_3388_ = v_isSharedCheck_3392_;
goto v_resetjp_3386_;
}
else
{
lean_inc(v_a_3385_);
lean_dec(v___x_3299_);
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
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v_snd_3270_);
lean_dec(v_numParams_3269_);
lean_dec(v___x_3267_);
lean_dec(v_levelParams_3265_);
lean_dec(v_declName_3264_);
lean_dec_ref(v___x_3263_);
lean_dec_ref(v___x_3262_);
lean_dec_ref(v_alts_3259_);
lean_dec(v_tail_3258_);
lean_dec_ref(v_heq_3256_);
lean_dec_ref(v_params_3253_);
lean_dec(v___x_3252_);
lean_dec(v___x_3251_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3249_);
lean_dec_ref(v_is_3248_);
lean_dec_ref(v_motive_3242_);
v_a_3394_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3283_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3283_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3402_ = _args[0];
lean_object* v___x_3403_ = _args[1];
lean_object* v___x_3404_ = _args[2];
lean_object* v___x_3405_ = _args[3];
lean_object* v___x_3406_ = _args[4];
lean_object* v_ism1_x27_3407_ = _args[5];
lean_object* v_is_3408_ = _args[6];
lean_object* v___x_3409_ = _args[7];
lean_object* v___x_3410_ = _args[8];
lean_object* v___x_3411_ = _args[9];
lean_object* v___x_3412_ = _args[10];
lean_object* v_params_3413_ = _args[11];
lean_object* v___x_3414_ = _args[12];
lean_object* v___x_3415_ = _args[13];
lean_object* v_heq_3416_ = _args[14];
lean_object* v_val_3417_ = _args[15];
lean_object* v_tail_3418_ = _args[16];
lean_object* v_alts_3419_ = _args[17];
lean_object* v_sz_3420_ = _args[18];
lean_object* v___x_3421_ = _args[19];
lean_object* v___x_3422_ = _args[20];
lean_object* v___x_3423_ = _args[21];
lean_object* v_declName_3424_ = _args[22];
lean_object* v_levelParams_3425_ = _args[23];
lean_object* v___x_3426_ = _args[24];
lean_object* v___x_3427_ = _args[25];
lean_object* v_numIndices_3428_ = _args[26];
lean_object* v_numParams_3429_ = _args[27];
lean_object* v_snd_3430_ = _args[28];
lean_object* v_ism2_x27_3431_ = _args[29];
lean_object* v_x_3432_ = _args[30];
lean_object* v___y_3433_ = _args[31];
lean_object* v___y_3434_ = _args[32];
lean_object* v___y_3435_ = _args[33];
lean_object* v___y_3436_ = _args[34];
lean_object* v___y_3437_ = _args[35];
_start:
{
uint8_t v___x_15609__boxed_3438_; uint8_t v___x_15610__boxed_3439_; uint8_t v___x_15611__boxed_3440_; size_t v_sz_boxed_3441_; size_t v___x_15620__boxed_3442_; lean_object* v_res_3443_; 
v___x_15609__boxed_3438_ = lean_unbox(v___x_3404_);
v___x_15610__boxed_3439_ = lean_unbox(v___x_3405_);
v___x_15611__boxed_3440_ = lean_unbox(v___x_3406_);
v_sz_boxed_3441_ = lean_unbox_usize(v_sz_3420_);
lean_dec(v_sz_3420_);
v___x_15620__boxed_3442_ = lean_unbox_usize(v___x_3421_);
lean_dec(v___x_3421_);
v_res_3443_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3402_, v___x_3403_, v___x_15609__boxed_3438_, v___x_15610__boxed_3439_, v___x_15611__boxed_3440_, v_ism1_x27_3407_, v_is_3408_, v___x_3409_, v___x_3410_, v___x_3411_, v___x_3412_, v_params_3413_, v___x_3414_, v___x_3415_, v_heq_3416_, v_val_3417_, v_tail_3418_, v_alts_3419_, v_sz_boxed_3441_, v___x_15620__boxed_3442_, v___x_3422_, v___x_3423_, v_declName_3424_, v_levelParams_3425_, v___x_3426_, v___x_3427_, v_numIndices_3428_, v_numParams_3429_, v_snd_3430_, v_ism2_x27_3431_, v_x_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec_ref(v_x_3432_);
lean_dec(v_numIndices_3428_);
lean_dec(v___x_3426_);
lean_dec_ref(v_val_3417_);
lean_dec_ref(v___x_3415_);
lean_dec_ref(v___x_3414_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3444_, lean_object* v___x_3445_, uint8_t v___x_3446_, uint8_t v___x_3447_, uint8_t v___x_3448_, lean_object* v_is_3449_, lean_object* v___x_3450_, lean_object* v___x_3451_, lean_object* v___x_3452_, lean_object* v___x_3453_, lean_object* v_params_3454_, lean_object* v___x_3455_, lean_object* v___x_3456_, lean_object* v_heq_3457_, lean_object* v_val_3458_, lean_object* v_tail_3459_, lean_object* v_alts_3460_, size_t v_sz_3461_, size_t v___x_3462_, lean_object* v___x_3463_, lean_object* v___x_3464_, lean_object* v_declName_3465_, lean_object* v_levelParams_3466_, lean_object* v___x_3467_, lean_object* v___x_3468_, lean_object* v_numIndices_3469_, lean_object* v_numParams_3470_, lean_object* v_snd_3471_, lean_object* v___x_3472_, lean_object* v___x_3473_, lean_object* v_ism1_x27_3474_, lean_object* v_x_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___f_3486_; lean_object* v___x_3487_; 
v___x_3481_ = lean_box(v___x_3446_);
v___x_3482_ = lean_box(v___x_3447_);
v___x_3483_ = lean_box(v___x_3448_);
v___x_3484_ = lean_box_usize(v_sz_3461_);
v___x_3485_ = lean_box_usize(v___x_3462_);
v___f_3486_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3486_, 0, v_motive_3444_);
lean_closure_set(v___f_3486_, 1, v___x_3445_);
lean_closure_set(v___f_3486_, 2, v___x_3481_);
lean_closure_set(v___f_3486_, 3, v___x_3482_);
lean_closure_set(v___f_3486_, 4, v___x_3483_);
lean_closure_set(v___f_3486_, 5, v_ism1_x27_3474_);
lean_closure_set(v___f_3486_, 6, v_is_3449_);
lean_closure_set(v___f_3486_, 7, v___x_3450_);
lean_closure_set(v___f_3486_, 8, v___x_3451_);
lean_closure_set(v___f_3486_, 9, v___x_3452_);
lean_closure_set(v___f_3486_, 10, v___x_3453_);
lean_closure_set(v___f_3486_, 11, v_params_3454_);
lean_closure_set(v___f_3486_, 12, v___x_3455_);
lean_closure_set(v___f_3486_, 13, v___x_3456_);
lean_closure_set(v___f_3486_, 14, v_heq_3457_);
lean_closure_set(v___f_3486_, 15, v_val_3458_);
lean_closure_set(v___f_3486_, 16, v_tail_3459_);
lean_closure_set(v___f_3486_, 17, v_alts_3460_);
lean_closure_set(v___f_3486_, 18, v___x_3484_);
lean_closure_set(v___f_3486_, 19, v___x_3485_);
lean_closure_set(v___f_3486_, 20, v___x_3463_);
lean_closure_set(v___f_3486_, 21, v___x_3464_);
lean_closure_set(v___f_3486_, 22, v_declName_3465_);
lean_closure_set(v___f_3486_, 23, v_levelParams_3466_);
lean_closure_set(v___f_3486_, 24, v___x_3467_);
lean_closure_set(v___f_3486_, 25, v___x_3468_);
lean_closure_set(v___f_3486_, 26, v_numIndices_3469_);
lean_closure_set(v___f_3486_, 27, v_numParams_3470_);
lean_closure_set(v___f_3486_, 28, v_snd_3471_);
v___x_3487_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3472_, v___x_3473_, v___f_3486_, v___x_3446_, v___x_3446_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3488_ = _args[0];
lean_object* v___x_3489_ = _args[1];
lean_object* v___x_3490_ = _args[2];
lean_object* v___x_3491_ = _args[3];
lean_object* v___x_3492_ = _args[4];
lean_object* v_is_3493_ = _args[5];
lean_object* v___x_3494_ = _args[6];
lean_object* v___x_3495_ = _args[7];
lean_object* v___x_3496_ = _args[8];
lean_object* v___x_3497_ = _args[9];
lean_object* v_params_3498_ = _args[10];
lean_object* v___x_3499_ = _args[11];
lean_object* v___x_3500_ = _args[12];
lean_object* v_heq_3501_ = _args[13];
lean_object* v_val_3502_ = _args[14];
lean_object* v_tail_3503_ = _args[15];
lean_object* v_alts_3504_ = _args[16];
lean_object* v_sz_3505_ = _args[17];
lean_object* v___x_3506_ = _args[18];
lean_object* v___x_3507_ = _args[19];
lean_object* v___x_3508_ = _args[20];
lean_object* v_declName_3509_ = _args[21];
lean_object* v_levelParams_3510_ = _args[22];
lean_object* v___x_3511_ = _args[23];
lean_object* v___x_3512_ = _args[24];
lean_object* v_numIndices_3513_ = _args[25];
lean_object* v_numParams_3514_ = _args[26];
lean_object* v_snd_3515_ = _args[27];
lean_object* v___x_3516_ = _args[28];
lean_object* v___x_3517_ = _args[29];
lean_object* v_ism1_x27_3518_ = _args[30];
lean_object* v_x_3519_ = _args[31];
lean_object* v___y_3520_ = _args[32];
lean_object* v___y_3521_ = _args[33];
lean_object* v___y_3522_ = _args[34];
lean_object* v___y_3523_ = _args[35];
lean_object* v___y_3524_ = _args[36];
_start:
{
uint8_t v___x_15943__boxed_3525_; uint8_t v___x_15944__boxed_3526_; uint8_t v___x_15945__boxed_3527_; size_t v_sz_boxed_3528_; size_t v___x_15954__boxed_3529_; lean_object* v_res_3530_; 
v___x_15943__boxed_3525_ = lean_unbox(v___x_3490_);
v___x_15944__boxed_3526_ = lean_unbox(v___x_3491_);
v___x_15945__boxed_3527_ = lean_unbox(v___x_3492_);
v_sz_boxed_3528_ = lean_unbox_usize(v_sz_3505_);
lean_dec(v_sz_3505_);
v___x_15954__boxed_3529_ = lean_unbox_usize(v___x_3506_);
lean_dec(v___x_3506_);
v_res_3530_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3488_, v___x_3489_, v___x_15943__boxed_3525_, v___x_15944__boxed_3526_, v___x_15945__boxed_3527_, v_is_3493_, v___x_3494_, v___x_3495_, v___x_3496_, v___x_3497_, v_params_3498_, v___x_3499_, v___x_3500_, v_heq_3501_, v_val_3502_, v_tail_3503_, v_alts_3504_, v_sz_boxed_3528_, v___x_15954__boxed_3529_, v___x_3507_, v___x_3508_, v_declName_3509_, v_levelParams_3510_, v___x_3511_, v___x_3512_, v_numIndices_3513_, v_numParams_3514_, v_snd_3515_, v___x_3516_, v___x_3517_, v_ism1_x27_3518_, v_x_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec_ref(v_x_3519_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3531_, lean_object* v___x_3532_, lean_object* v_motive_3533_, lean_object* v___x_3534_, uint8_t v___x_3535_, uint8_t v___x_3536_, uint8_t v___x_3537_, lean_object* v_is_3538_, lean_object* v___x_3539_, lean_object* v___x_3540_, lean_object* v___x_3541_, lean_object* v___x_3542_, lean_object* v_params_3543_, lean_object* v___x_3544_, lean_object* v___x_3545_, lean_object* v_heq_3546_, lean_object* v_val_3547_, lean_object* v_tail_3548_, size_t v_sz_3549_, size_t v___x_3550_, lean_object* v___x_3551_, lean_object* v___x_3552_, lean_object* v_declName_3553_, lean_object* v_levelParams_3554_, lean_object* v___x_3555_, lean_object* v___x_3556_, lean_object* v_numParams_3557_, lean_object* v_snd_3558_, lean_object* v___x_3559_, lean_object* v_alts_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___f_3573_; lean_object* v___x_3574_; 
v___x_3566_ = lean_nat_add(v_numIndices_3531_, v___x_3532_);
v___x_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
v___x_3568_ = lean_box(v___x_3535_);
v___x_3569_ = lean_box(v___x_3536_);
v___x_3570_ = lean_box(v___x_3537_);
v___x_3571_ = lean_box_usize(v_sz_3549_);
v___x_3572_ = lean_box_usize(v___x_3550_);
lean_inc_ref(v___x_3567_);
lean_inc_ref(v___x_3559_);
v___f_3573_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3573_, 0, v_motive_3533_);
lean_closure_set(v___f_3573_, 1, v___x_3534_);
lean_closure_set(v___f_3573_, 2, v___x_3568_);
lean_closure_set(v___f_3573_, 3, v___x_3569_);
lean_closure_set(v___f_3573_, 4, v___x_3570_);
lean_closure_set(v___f_3573_, 5, v_is_3538_);
lean_closure_set(v___f_3573_, 6, v___x_3539_);
lean_closure_set(v___f_3573_, 7, v___x_3540_);
lean_closure_set(v___f_3573_, 8, v___x_3541_);
lean_closure_set(v___f_3573_, 9, v___x_3542_);
lean_closure_set(v___f_3573_, 10, v_params_3543_);
lean_closure_set(v___f_3573_, 11, v___x_3544_);
lean_closure_set(v___f_3573_, 12, v___x_3545_);
lean_closure_set(v___f_3573_, 13, v_heq_3546_);
lean_closure_set(v___f_3573_, 14, v_val_3547_);
lean_closure_set(v___f_3573_, 15, v_tail_3548_);
lean_closure_set(v___f_3573_, 16, v_alts_3560_);
lean_closure_set(v___f_3573_, 17, v___x_3571_);
lean_closure_set(v___f_3573_, 18, v___x_3572_);
lean_closure_set(v___f_3573_, 19, v___x_3551_);
lean_closure_set(v___f_3573_, 20, v___x_3552_);
lean_closure_set(v___f_3573_, 21, v_declName_3553_);
lean_closure_set(v___f_3573_, 22, v_levelParams_3554_);
lean_closure_set(v___f_3573_, 23, v___x_3555_);
lean_closure_set(v___f_3573_, 24, v___x_3556_);
lean_closure_set(v___f_3573_, 25, v_numIndices_3531_);
lean_closure_set(v___f_3573_, 26, v_numParams_3557_);
lean_closure_set(v___f_3573_, 27, v_snd_3558_);
lean_closure_set(v___f_3573_, 28, v___x_3559_);
lean_closure_set(v___f_3573_, 29, v___x_3567_);
v___x_3574_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3559_, v___x_3567_, v___f_3573_, v___x_3535_, v___x_3535_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3575_ = _args[0];
lean_object* v___x_3576_ = _args[1];
lean_object* v_motive_3577_ = _args[2];
lean_object* v___x_3578_ = _args[3];
lean_object* v___x_3579_ = _args[4];
lean_object* v___x_3580_ = _args[5];
lean_object* v___x_3581_ = _args[6];
lean_object* v_is_3582_ = _args[7];
lean_object* v___x_3583_ = _args[8];
lean_object* v___x_3584_ = _args[9];
lean_object* v___x_3585_ = _args[10];
lean_object* v___x_3586_ = _args[11];
lean_object* v_params_3587_ = _args[12];
lean_object* v___x_3588_ = _args[13];
lean_object* v___x_3589_ = _args[14];
lean_object* v_heq_3590_ = _args[15];
lean_object* v_val_3591_ = _args[16];
lean_object* v_tail_3592_ = _args[17];
lean_object* v_sz_3593_ = _args[18];
lean_object* v___x_3594_ = _args[19];
lean_object* v___x_3595_ = _args[20];
lean_object* v___x_3596_ = _args[21];
lean_object* v_declName_3597_ = _args[22];
lean_object* v_levelParams_3598_ = _args[23];
lean_object* v___x_3599_ = _args[24];
lean_object* v___x_3600_ = _args[25];
lean_object* v_numParams_3601_ = _args[26];
lean_object* v_snd_3602_ = _args[27];
lean_object* v___x_3603_ = _args[28];
lean_object* v_alts_3604_ = _args[29];
lean_object* v___y_3605_ = _args[30];
lean_object* v___y_3606_ = _args[31];
lean_object* v___y_3607_ = _args[32];
lean_object* v___y_3608_ = _args[33];
lean_object* v___y_3609_ = _args[34];
_start:
{
uint8_t v___x_16036__boxed_3610_; uint8_t v___x_16037__boxed_3611_; uint8_t v___x_16038__boxed_3612_; size_t v_sz_boxed_3613_; size_t v___x_16047__boxed_3614_; lean_object* v_res_3615_; 
v___x_16036__boxed_3610_ = lean_unbox(v___x_3579_);
v___x_16037__boxed_3611_ = lean_unbox(v___x_3580_);
v___x_16038__boxed_3612_ = lean_unbox(v___x_3581_);
v_sz_boxed_3613_ = lean_unbox_usize(v_sz_3593_);
lean_dec(v_sz_3593_);
v___x_16047__boxed_3614_ = lean_unbox_usize(v___x_3594_);
lean_dec(v___x_3594_);
v_res_3615_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3575_, v___x_3576_, v_motive_3577_, v___x_3578_, v___x_16036__boxed_3610_, v___x_16037__boxed_3611_, v___x_16038__boxed_3612_, v_is_3582_, v___x_3583_, v___x_3584_, v___x_3585_, v___x_3586_, v_params_3587_, v___x_3588_, v___x_3589_, v_heq_3590_, v_val_3591_, v_tail_3592_, v_sz_boxed_3613_, v___x_16047__boxed_3614_, v___x_3595_, v___x_3596_, v_declName_3597_, v_levelParams_3598_, v___x_3599_, v___x_3600_, v_numParams_3601_, v_snd_3602_, v___x_3603_, v_alts_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___x_3576_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3616_, lean_object* v_declInfos_3617_, lean_object* v_k_3618_, lean_object* v_kind_3619_, lean_object* v_x_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
uint8_t v_kind_boxed_3626_; lean_object* v_res_3627_; 
v_kind_boxed_3626_ = lean_unbox(v_kind_3619_);
v_res_3627_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3616_, v_declInfos_3617_, v_k_3618_, v_kind_boxed_3626_, v_x_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3628_, lean_object* v_k_3629_, uint8_t v_kind_3630_, lean_object* v_acc_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v___x_3637_; lean_object* v_toApplicative_3638_; lean_object* v_toFunctor_3639_; lean_object* v_toSeq_3640_; lean_object* v_toSeqLeft_3641_; lean_object* v_toSeqRight_3642_; lean_object* v___f_3643_; lean_object* v___f_3644_; lean_object* v___f_3645_; lean_object* v___f_3646_; lean_object* v___x_3647_; lean_object* v___f_3648_; lean_object* v___f_3649_; lean_object* v___f_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v_toApplicative_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3711_; 
v___x_3637_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3638_ = lean_ctor_get(v___x_3637_, 0);
v_toFunctor_3639_ = lean_ctor_get(v_toApplicative_3638_, 0);
v_toSeq_3640_ = lean_ctor_get(v_toApplicative_3638_, 2);
v_toSeqLeft_3641_ = lean_ctor_get(v_toApplicative_3638_, 3);
v_toSeqRight_3642_ = lean_ctor_get(v_toApplicative_3638_, 4);
v___f_3643_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3644_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3639_, 2);
v___f_3645_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3645_, 0, v_toFunctor_3639_);
v___f_3646_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3646_, 0, v_toFunctor_3639_);
v___x_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___f_3645_);
lean_ctor_set(v___x_3647_, 1, v___f_3646_);
lean_inc(v_toSeqRight_3642_);
v___f_3648_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3648_, 0, v_toSeqRight_3642_);
lean_inc(v_toSeqLeft_3641_);
v___f_3649_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3649_, 0, v_toSeqLeft_3641_);
lean_inc(v_toSeq_3640_);
v___f_3650_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3650_, 0, v_toSeq_3640_);
v___x_3651_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3647_);
lean_ctor_set(v___x_3651_, 1, v___f_3643_);
lean_ctor_set(v___x_3651_, 2, v___f_3650_);
lean_ctor_set(v___x_3651_, 3, v___f_3649_);
lean_ctor_set(v___x_3651_, 4, v___f_3648_);
v___x_3652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
lean_ctor_set(v___x_3652_, 1, v___f_3644_);
v___x_3653_ = l_StateRefT_x27_instMonad___redArg(v___x_3652_);
v_toApplicative_3654_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; 
v_unused_3712_ = lean_ctor_get(v___x_3653_, 1);
lean_dec(v_unused_3712_);
v___x_3656_ = v___x_3653_;
v_isShared_3657_ = v_isSharedCheck_3711_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_toApplicative_3654_);
lean_dec(v___x_3653_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3711_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v_toFunctor_3658_; lean_object* v_toSeq_3659_; lean_object* v_toSeqLeft_3660_; lean_object* v_toSeqRight_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3709_; 
v_toFunctor_3658_ = lean_ctor_get(v_toApplicative_3654_, 0);
v_toSeq_3659_ = lean_ctor_get(v_toApplicative_3654_, 2);
v_toSeqLeft_3660_ = lean_ctor_get(v_toApplicative_3654_, 3);
v_toSeqRight_3661_ = lean_ctor_get(v_toApplicative_3654_, 4);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_toApplicative_3654_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v_toApplicative_3654_, 1);
lean_dec(v_unused_3710_);
v___x_3663_ = v_toApplicative_3654_;
v_isShared_3664_ = v_isSharedCheck_3709_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_toSeqRight_3661_);
lean_inc(v_toSeqLeft_3660_);
lean_inc(v_toSeq_3659_);
lean_inc(v_toFunctor_3658_);
lean_dec(v_toApplicative_3654_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3709_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___f_3665_; lean_object* v___f_3666_; lean_object* v___f_3667_; lean_object* v___f_3668_; lean_object* v___x_3669_; lean_object* v___f_3670_; lean_object* v___f_3671_; lean_object* v___f_3672_; lean_object* v___x_3674_; 
v___f_3665_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3666_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3658_);
v___f_3667_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3667_, 0, v_toFunctor_3658_);
v___f_3668_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3668_, 0, v_toFunctor_3658_);
v___x_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___f_3667_);
lean_ctor_set(v___x_3669_, 1, v___f_3668_);
v___f_3670_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3670_, 0, v_toSeqRight_3661_);
v___f_3671_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3671_, 0, v_toSeqLeft_3660_);
v___f_3672_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3672_, 0, v_toSeq_3659_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 4, v___f_3670_);
lean_ctor_set(v___x_3663_, 3, v___f_3671_);
lean_ctor_set(v___x_3663_, 2, v___f_3672_);
lean_ctor_set(v___x_3663_, 1, v___f_3665_);
lean_ctor_set(v___x_3663_, 0, v___x_3669_);
v___x_3674_ = v___x_3663_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___f_3665_);
lean_ctor_set(v_reuseFailAlloc_3708_, 2, v___f_3672_);
lean_ctor_set(v_reuseFailAlloc_3708_, 3, v___f_3671_);
lean_ctor_set(v_reuseFailAlloc_3708_, 4, v___f_3670_);
v___x_3674_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3676_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 1, v___f_3666_);
lean_ctor_set(v___x_3656_, 0, v___x_3674_);
v___x_3676_ = v___x_3656_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3674_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v___f_3666_);
v___x_3676_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; 
v___x_3677_ = lean_array_get_size(v_acc_3631_);
v___x_3678_ = lean_array_get_size(v_declInfos_3628_);
v___x_3679_ = lean_nat_dec_lt(v___x_3677_, v___x_3678_);
if (v___x_3679_ == 0)
{
lean_object* v___x_3680_; 
lean_dec_ref(v___x_3676_);
lean_dec_ref(v_declInfos_3628_);
lean_inc(v___y_3635_);
lean_inc_ref(v___y_3634_);
lean_inc(v___y_3633_);
lean_inc_ref(v___y_3632_);
v___x_3680_ = lean_apply_6(v_k_3629_, v_acc_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, lean_box(0));
return v___x_3680_;
}
else
{
lean_object* v___f_3681_; lean_object* v___x_3682_; uint8_t v___x_3683_; lean_object* v___f_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v_snd_3689_; lean_object* v_fst_3690_; lean_object* v_fst_3691_; lean_object* v_snd_3692_; lean_object* v___x_3693_; 
v___f_3681_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3681_, 0, v___x_3676_);
v___x_3682_ = lean_box(0);
v___x_3683_ = 0;
v___f_3684_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3684_, 0, v___f_3681_);
v___x_3685_ = lean_box(v___x_3683_);
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
lean_ctor_set(v___x_3686_, 1, v___f_3684_);
v___x_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3682_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___x_3688_ = lean_array_get(v___x_3687_, v_declInfos_3628_, v___x_3677_);
lean_dec_ref_known(v___x_3687_, 2);
v_snd_3689_ = lean_ctor_get(v___x_3688_, 1);
lean_inc(v_snd_3689_);
v_fst_3690_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_fst_3690_);
lean_dec(v___x_3688_);
v_fst_3691_ = lean_ctor_get(v_snd_3689_, 0);
lean_inc(v_fst_3691_);
v_snd_3692_ = lean_ctor_get(v_snd_3689_, 1);
lean_inc(v_snd_3692_);
lean_dec(v_snd_3689_);
lean_inc(v___y_3635_);
lean_inc_ref(v___y_3634_);
lean_inc(v___y_3633_);
lean_inc_ref(v___y_3632_);
lean_inc_ref(v_acc_3631_);
v___x_3693_ = lean_apply_6(v_snd_3692_, v_acc_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, lean_box(0));
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v___x_3695_; lean_object* v___f_3696_; uint8_t v___x_3697_; lean_object* v___x_3698_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref_known(v___x_3693_, 1);
v___x_3695_ = lean_box(v_kind_3630_);
v___f_3696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3696_, 0, v_acc_3631_);
lean_closure_set(v___f_3696_, 1, v_declInfos_3628_);
lean_closure_set(v___f_3696_, 2, v_k_3629_);
lean_closure_set(v___f_3696_, 3, v___x_3695_);
v___x_3697_ = lean_unbox(v_fst_3691_);
lean_dec(v_fst_3691_);
v___x_3698_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3690_, v___x_3697_, v_a_3694_, v___f_3696_, v_kind_3630_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
return v___x_3698_;
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_fst_3691_);
lean_dec(v_fst_3690_);
lean_dec_ref(v_acc_3631_);
lean_dec_ref(v_k_3629_);
lean_dec_ref(v_declInfos_3628_);
v_a_3699_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3693_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3693_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3713_, lean_object* v_declInfos_3714_, lean_object* v_k_3715_, uint8_t v_kind_3716_, lean_object* v_x_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = lean_array_push(v_acc_3713_, v_x_3717_);
v___x_3724_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3714_, v_k_3715_, v_kind_3716_, v___x_3723_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3725_, lean_object* v_k_3726_, lean_object* v_kind_3727_, lean_object* v_acc_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
uint8_t v_kind_boxed_3734_; lean_object* v_res_3735_; 
v_kind_boxed_3734_ = lean_unbox(v_kind_3727_);
v_res_3735_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3725_, v_k_3726_, v_kind_boxed_3734_, v_acc_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
lean_dec(v___y_3732_);
lean_dec_ref(v___y_3731_);
lean_dec(v___y_3730_);
lean_dec_ref(v___y_3729_);
return v_res_3735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3736_, lean_object* v_k_3737_, uint8_t v_kind_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3745_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3736_, v_k_3737_, v_kind_3738_, v___x_3744_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3746_, lean_object* v_k_3747_, lean_object* v_kind_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
uint8_t v_kind_boxed_3754_; lean_object* v_res_3755_; 
v_kind_boxed_3754_ = lean_unbox(v_kind_3748_);
v_res_3755_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3746_, v_k_3747_, v_kind_boxed_3754_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3756_, lean_object* v_k_3757_, uint8_t v_kind_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
size_t v_sz_3764_; size_t v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v_sz_3764_ = lean_array_size(v_declInfos_3756_);
v___x_3765_ = ((size_t)0ULL);
v___x_3766_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3764_, v___x_3765_, v_declInfos_3756_);
v___x_3767_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3766_, v_k_3757_, v_kind_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
return v___x_3767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3768_, lean_object* v_k_3769_, lean_object* v_kind_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
uint8_t v_kind_boxed_3776_; lean_object* v_res_3777_; 
v_kind_boxed_3776_ = lean_unbox(v_kind_3770_);
v_res_3777_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3768_, v_k_3769_, v_kind_boxed_3776_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
lean_dec(v___y_3772_);
lean_dec_ref(v___y_3771_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3778_, lean_object* v_k_3779_, uint8_t v_kind_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_){
_start:
{
size_t v_sz_3786_; size_t v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v_sz_3786_ = lean_array_size(v_declInfos_3778_);
v___x_3787_ = ((size_t)0ULL);
v___x_3788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3786_, v___x_3787_, v_declInfos_3778_);
v___x_3789_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3788_, v_k_3779_, v_kind_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3790_, lean_object* v_k_3791_, lean_object* v_kind_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
uint8_t v_kind_boxed_3798_; lean_object* v_res_3799_; 
v_kind_boxed_3798_ = lean_unbox(v_kind_3792_);
v_res_3799_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3790_, v_k_3791_, v_kind_boxed_3798_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec(v___y_3794_);
lean_dec_ref(v___y_3793_);
return v_res_3799_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3802_ = lean_box(0);
v___x_3803_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3804_ = l_Lean_mkConst(v___x_3803_, v___x_3802_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3805_, lean_object* v___x_3806_, lean_object* v_motive_3807_, uint8_t v___x_3808_, uint8_t v___x_3809_, uint8_t v___x_3810_, lean_object* v___x_3811_, lean_object* v_v_3812_, lean_object* v___x_3813_, lean_object* v_zs12_3814_, lean_object* v_is_3815_, lean_object* v_fields1_3816_, lean_object* v_fields2_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v_e_3833_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_inc(v___x_3805_);
v___x_3843_ = l_Lean_mkNatLit(v___x_3805_);
v___x_3844_ = l_Lean_Meta_mkEqRefl(v___x_3843_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
lean_inc_ref(v___x_3806_);
v___x_3846_ = l_Lean_mkAppN(v___x_3806_, v_fields1_3816_);
v___x_3847_ = l_Lean_mkAppN(v___x_3806_, v_fields2_3817_);
v___x_3848_ = lean_unsigned_to_nat(3u);
v___x_3849_ = lean_mk_empty_array_with_capacity(v___x_3848_);
v___x_3850_ = lean_array_push(v___x_3849_, v___x_3846_);
v___x_3851_ = lean_array_push(v___x_3850_, v___x_3847_);
v___x_3852_ = lean_array_push(v___x_3851_, v_a_3845_);
v___x_3853_ = l_Array_append___redArg(v_is_3815_, v___x_3852_);
lean_dec_ref(v___x_3852_);
v___x_3854_ = l_Lean_mkAppN(v_motive_3807_, v___x_3853_);
lean_dec_ref(v___x_3853_);
v___x_3855_ = l_Lean_Meta_mkForallFVars(v_zs12_3814_, v___x_3854_, v___x_3808_, v___x_3809_, v___x_3809_, v___x_3810_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3855_) == 0)
{
lean_object* v_a_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v_a_3856_ = lean_ctor_get(v___x_3855_, 0);
lean_inc(v_a_3856_);
lean_dec_ref_known(v___x_3855_, 1);
v___x_3857_ = lean_array_get_size(v_zs12_3814_);
v___x_3858_ = lean_nat_dec_eq(v___x_3857_, v___x_3811_);
if (v___x_3858_ == 0)
{
v_e_3833_ = v_a_3856_;
goto v___jp_3832_;
}
else
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3860_ = l_Lean_mkArrow(v___x_3859_, v_a_3856_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref_known(v___x_3860_, 1);
v_e_3833_ = v_a_3861_;
goto v___jp_3832_;
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
lean_dec(v_v_3812_);
lean_dec(v___x_3811_);
lean_dec(v___x_3805_);
v_a_3862_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___x_3860_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___x_3860_);
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
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec(v_v_3812_);
lean_dec(v___x_3811_);
lean_dec(v___x_3805_);
v_a_3870_ = lean_ctor_get(v___x_3855_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3855_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3855_);
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
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v_is_3815_);
lean_dec(v_v_3812_);
lean_dec(v___x_3811_);
lean_dec_ref(v_motive_3807_);
lean_dec_ref(v___x_3806_);
lean_dec(v___x_3805_);
v_a_3878_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3844_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3844_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
v___jp_3823_:
{
lean_object* v___x_3826_; uint8_t v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3826_ = lean_array_get_size(v_zs12_3814_);
v___x_3827_ = lean_nat_dec_eq(v___x_3826_, v___x_3811_);
v___x_3828_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3828_, 0, v___x_3826_);
lean_ctor_set(v___x_3828_, 1, v___x_3811_);
lean_ctor_set_uint8(v___x_3828_, sizeof(void*)*2, v___x_3827_);
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___y_3825_);
lean_ctor_set(v___x_3829_, 1, v___y_3824_);
v___x_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
lean_ctor_set(v___x_3830_, 1, v___x_3828_);
v___x_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3830_);
return v___x_3831_;
}
v___jp_3832_:
{
if (lean_obj_tag(v_v_3812_) == 1)
{
lean_object* v_str_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
lean_dec(v___x_3805_);
v_str_3834_ = lean_ctor_get(v_v_3812_, 1);
lean_inc_ref(v_str_3834_);
lean_dec_ref_known(v_v_3812_, 2);
v___x_3835_ = lean_box(0);
v___x_3836_ = l_Lean_Name_str___override(v___x_3835_, v_str_3834_);
v___y_3824_ = v_e_3833_;
v___y_3825_ = v___x_3836_;
goto v___jp_3823_;
}
else
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
lean_dec(v_v_3812_);
v___x_3837_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3838_ = lean_nat_add(v___x_3805_, v___x_3813_);
lean_dec(v___x_3805_);
v___x_3839_ = l_Nat_reprFast(v___x_3838_);
v___x_3840_ = lean_string_append(v___x_3837_, v___x_3839_);
lean_dec_ref(v___x_3839_);
v___x_3841_ = lean_box(0);
v___x_3842_ = l_Lean_Name_str___override(v___x_3841_, v___x_3840_);
v___y_3824_ = v_e_3833_;
v___y_3825_ = v___x_3842_;
goto v___jp_3823_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3886_ = _args[0];
lean_object* v___x_3887_ = _args[1];
lean_object* v_motive_3888_ = _args[2];
lean_object* v___x_3889_ = _args[3];
lean_object* v___x_3890_ = _args[4];
lean_object* v___x_3891_ = _args[5];
lean_object* v___x_3892_ = _args[6];
lean_object* v_v_3893_ = _args[7];
lean_object* v___x_3894_ = _args[8];
lean_object* v_zs12_3895_ = _args[9];
lean_object* v_is_3896_ = _args[10];
lean_object* v_fields1_3897_ = _args[11];
lean_object* v_fields2_3898_ = _args[12];
lean_object* v___y_3899_ = _args[13];
lean_object* v___y_3900_ = _args[14];
lean_object* v___y_3901_ = _args[15];
lean_object* v___y_3902_ = _args[16];
lean_object* v___y_3903_ = _args[17];
_start:
{
uint8_t v___x_16379__boxed_3904_; uint8_t v___x_16380__boxed_3905_; uint8_t v___x_16381__boxed_3906_; lean_object* v_res_3907_; 
v___x_16379__boxed_3904_ = lean_unbox(v___x_3889_);
v___x_16380__boxed_3905_ = lean_unbox(v___x_3890_);
v___x_16381__boxed_3906_ = lean_unbox(v___x_3891_);
v_res_3907_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3886_, v___x_3887_, v_motive_3888_, v___x_16379__boxed_3904_, v___x_16380__boxed_3905_, v___x_16381__boxed_3906_, v___x_3892_, v_v_3893_, v___x_3894_, v_zs12_3895_, v_is_3896_, v_fields1_3897_, v_fields2_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
lean_dec(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v___y_3899_);
lean_dec_ref(v_fields2_3898_);
lean_dec_ref(v_fields1_3897_);
lean_dec_ref(v_zs12_3895_);
lean_dec(v___x_3894_);
return v_res_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3908_, lean_object* v_params_3909_, lean_object* v_motive_3910_, size_t v_sz_3911_, size_t v_i_3912_, lean_object* v_bs_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
uint8_t v___x_3919_; 
v___x_3919_ = lean_usize_dec_lt(v_i_3912_, v_sz_3911_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; 
lean_dec_ref(v_motive_3910_);
lean_dec(v_tail_3908_);
v___x_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3920_, 0, v_bs_3913_);
return v___x_3920_;
}
else
{
lean_object* v___x_3921_; lean_object* v___x_3922_; uint8_t v___x_3923_; uint8_t v___x_3924_; lean_object* v_v_3925_; lean_object* v_bs_x27_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___f_3933_; lean_object* v___x_3934_; 
v___x_3921_ = lean_unsigned_to_nat(0u);
v___x_3922_ = lean_unsigned_to_nat(1u);
v___x_3923_ = 0;
v___x_3924_ = 1;
v_v_3925_ = lean_array_uget(v_bs_3913_, v_i_3912_);
v_bs_x27_3926_ = lean_array_uset(v_bs_3913_, v_i_3912_, v___x_3921_);
v___x_3927_ = lean_usize_to_nat(v_i_3912_);
lean_inc(v_tail_3908_);
lean_inc(v_v_3925_);
v___x_3928_ = l_Lean_mkConst(v_v_3925_, v_tail_3908_);
v___x_3929_ = l_Lean_mkAppN(v___x_3928_, v_params_3909_);
v___x_3930_ = lean_box(v___x_3923_);
v___x_3931_ = lean_box(v___x_3919_);
v___x_3932_ = lean_box(v___x_3924_);
lean_inc_ref(v_motive_3910_);
lean_inc_ref(v___x_3929_);
v___f_3933_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3933_, 0, v___x_3927_);
lean_closure_set(v___f_3933_, 1, v___x_3929_);
lean_closure_set(v___f_3933_, 2, v_motive_3910_);
lean_closure_set(v___f_3933_, 3, v___x_3930_);
lean_closure_set(v___f_3933_, 4, v___x_3931_);
lean_closure_set(v___f_3933_, 5, v___x_3932_);
lean_closure_set(v___f_3933_, 6, v___x_3921_);
lean_closure_set(v___f_3933_, 7, v_v_3925_);
lean_closure_set(v___f_3933_, 8, v___x_3922_);
v___x_3934_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3929_, v___f_3933_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; size_t v___x_3936_; size_t v___x_3937_; lean_object* v___x_3938_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref_known(v___x_3934_, 1);
v___x_3936_ = ((size_t)1ULL);
v___x_3937_ = lean_usize_add(v_i_3912_, v___x_3936_);
v___x_3938_ = lean_array_uset(v_bs_x27_3926_, v_i_3912_, v_a_3935_);
v_i_3912_ = v___x_3937_;
v_bs_3913_ = v___x_3938_;
goto _start;
}
else
{
lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec_ref(v_bs_x27_3926_);
lean_dec_ref(v_motive_3910_);
lean_dec(v_tail_3908_);
v_a_3940_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3934_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_dec(v___x_3934_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3948_, lean_object* v_params_3949_, lean_object* v_motive_3950_, lean_object* v_sz_3951_, lean_object* v_i_3952_, lean_object* v_bs_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
size_t v_sz_boxed_3959_; size_t v_i_boxed_3960_; lean_object* v_res_3961_; 
v_sz_boxed_3959_ = lean_unbox_usize(v_sz_3951_);
lean_dec(v_sz_3951_);
v_i_boxed_3960_ = lean_unbox_usize(v_i_3952_);
lean_dec(v_i_3952_);
v_res_3961_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3948_, v_params_3949_, v_motive_3950_, v_sz_boxed_3959_, v_i_boxed_3960_, v_bs_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec_ref(v_params_3949_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3964_, lean_object* v_tail_3965_, lean_object* v_params_3966_, lean_object* v_numIndices_3967_, lean_object* v___x_3968_, lean_object* v___x_3969_, uint8_t v___x_3970_, uint8_t v___x_3971_, uint8_t v___x_3972_, lean_object* v_is_3973_, lean_object* v___x_3974_, lean_object* v___x_3975_, lean_object* v___x_3976_, lean_object* v___x_3977_, lean_object* v___x_3978_, lean_object* v___x_3979_, lean_object* v_heq_3980_, lean_object* v_val_3981_, lean_object* v___x_3982_, lean_object* v_declName_3983_, lean_object* v_levelParams_3984_, lean_object* v___x_3985_, lean_object* v___x_3986_, lean_object* v_numParams_3987_, lean_object* v___x_3988_, lean_object* v_motive_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_){
_start:
{
lean_object* v___x_3995_; size_t v_sz_3996_; size_t v___x_3997_; lean_object* v___x_3998_; 
v___x_3995_ = lean_array_mk(v_ctors_3964_);
v_sz_3996_ = lean_array_size(v___x_3995_);
v___x_3997_ = ((size_t)0ULL);
lean_inc_ref(v___x_3995_);
lean_inc_ref(v_motive_3989_);
lean_inc(v_tail_3965_);
v___x_3998_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3965_, v_params_3966_, v_motive_3989_, v_sz_3996_, v___x_3997_, v___x_3995_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4000_; lean_object* v_fst_4001_; lean_object* v_snd_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___f_4008_; uint8_t v___x_4009_; lean_object* v___x_4010_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v___x_4000_ = l_Array_unzip___redArg(v_a_3999_);
lean_dec(v_a_3999_);
v_fst_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_fst_4001_);
v_snd_4002_ = lean_ctor_get(v___x_4000_, 1);
lean_inc(v_snd_4002_);
lean_dec_ref(v___x_4000_);
v___x_4003_ = lean_box(v___x_3970_);
v___x_4004_ = lean_box(v___x_3971_);
v___x_4005_ = lean_box(v___x_3972_);
v___x_4006_ = lean_box_usize(v_sz_3996_);
v___x_4007_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4008_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4008_, 0, v_numIndices_3967_);
lean_closure_set(v___f_4008_, 1, v___x_3968_);
lean_closure_set(v___f_4008_, 2, v_motive_3989_);
lean_closure_set(v___f_4008_, 3, v___x_3969_);
lean_closure_set(v___f_4008_, 4, v___x_4003_);
lean_closure_set(v___f_4008_, 5, v___x_4004_);
lean_closure_set(v___f_4008_, 6, v___x_4005_);
lean_closure_set(v___f_4008_, 7, v_is_3973_);
lean_closure_set(v___f_4008_, 8, v___x_3974_);
lean_closure_set(v___f_4008_, 9, v___x_3975_);
lean_closure_set(v___f_4008_, 10, v___x_3976_);
lean_closure_set(v___f_4008_, 11, v___x_3977_);
lean_closure_set(v___f_4008_, 12, v_params_3966_);
lean_closure_set(v___f_4008_, 13, v___x_3978_);
lean_closure_set(v___f_4008_, 14, v___x_3979_);
lean_closure_set(v___f_4008_, 15, v_heq_3980_);
lean_closure_set(v___f_4008_, 16, v_val_3981_);
lean_closure_set(v___f_4008_, 17, v_tail_3965_);
lean_closure_set(v___f_4008_, 18, v___x_4006_);
lean_closure_set(v___f_4008_, 19, v___x_4007_);
lean_closure_set(v___f_4008_, 20, v___x_3995_);
lean_closure_set(v___f_4008_, 21, v___x_3982_);
lean_closure_set(v___f_4008_, 22, v_declName_3983_);
lean_closure_set(v___f_4008_, 23, v_levelParams_3984_);
lean_closure_set(v___f_4008_, 24, v___x_3985_);
lean_closure_set(v___f_4008_, 25, v___x_3986_);
lean_closure_set(v___f_4008_, 26, v_numParams_3987_);
lean_closure_set(v___f_4008_, 27, v_snd_4002_);
lean_closure_set(v___f_4008_, 28, v___x_3988_);
v___x_4009_ = 0;
v___x_4010_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_4001_, v___f_4008_, v___x_4009_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
return v___x_4010_;
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec_ref(v___x_3995_);
lean_dec_ref(v_motive_3989_);
lean_dec_ref(v___x_3988_);
lean_dec(v_numParams_3987_);
lean_dec(v___x_3986_);
lean_dec(v___x_3985_);
lean_dec(v_levelParams_3984_);
lean_dec(v_declName_3983_);
lean_dec_ref(v___x_3982_);
lean_dec_ref(v_val_3981_);
lean_dec_ref(v_heq_3980_);
lean_dec_ref(v___x_3979_);
lean_dec_ref(v___x_3978_);
lean_dec(v___x_3977_);
lean_dec(v___x_3976_);
lean_dec_ref(v___x_3975_);
lean_dec_ref(v___x_3974_);
lean_dec_ref(v_is_3973_);
lean_dec_ref(v___x_3969_);
lean_dec(v___x_3968_);
lean_dec(v_numIndices_3967_);
lean_dec_ref(v_params_3966_);
lean_dec(v_tail_3965_);
v_a_4011_ = lean_ctor_get(v___x_3998_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_3998_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_3998_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4019_ = _args[0];
lean_object* v_tail_4020_ = _args[1];
lean_object* v_params_4021_ = _args[2];
lean_object* v_numIndices_4022_ = _args[3];
lean_object* v___x_4023_ = _args[4];
lean_object* v___x_4024_ = _args[5];
lean_object* v___x_4025_ = _args[6];
lean_object* v___x_4026_ = _args[7];
lean_object* v___x_4027_ = _args[8];
lean_object* v_is_4028_ = _args[9];
lean_object* v___x_4029_ = _args[10];
lean_object* v___x_4030_ = _args[11];
lean_object* v___x_4031_ = _args[12];
lean_object* v___x_4032_ = _args[13];
lean_object* v___x_4033_ = _args[14];
lean_object* v___x_4034_ = _args[15];
lean_object* v_heq_4035_ = _args[16];
lean_object* v_val_4036_ = _args[17];
lean_object* v___x_4037_ = _args[18];
lean_object* v_declName_4038_ = _args[19];
lean_object* v_levelParams_4039_ = _args[20];
lean_object* v___x_4040_ = _args[21];
lean_object* v___x_4041_ = _args[22];
lean_object* v_numParams_4042_ = _args[23];
lean_object* v___x_4043_ = _args[24];
lean_object* v_motive_4044_ = _args[25];
lean_object* v___y_4045_ = _args[26];
lean_object* v___y_4046_ = _args[27];
lean_object* v___y_4047_ = _args[28];
lean_object* v___y_4048_ = _args[29];
lean_object* v___y_4049_ = _args[30];
_start:
{
uint8_t v___x_16618__boxed_4050_; uint8_t v___x_16619__boxed_4051_; uint8_t v___x_16620__boxed_4052_; lean_object* v_res_4053_; 
v___x_16618__boxed_4050_ = lean_unbox(v___x_4025_);
v___x_16619__boxed_4051_ = lean_unbox(v___x_4026_);
v___x_16620__boxed_4052_ = lean_unbox(v___x_4027_);
v_res_4053_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4019_, v_tail_4020_, v_params_4021_, v_numIndices_4022_, v___x_4023_, v___x_4024_, v___x_16618__boxed_4050_, v___x_16619__boxed_4051_, v___x_16620__boxed_4052_, v_is_4028_, v___x_4029_, v___x_4030_, v___x_4031_, v___x_4032_, v___x_4033_, v___x_4034_, v_heq_4035_, v_val_4036_, v___x_4037_, v_declName_4038_, v_levelParams_4039_, v___x_4040_, v___x_4041_, v_numParams_4042_, v___x_4043_, v_motive_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4054_, lean_object* v___x_4055_, lean_object* v_is_4056_, lean_object* v_head_4057_, lean_object* v_ctors_4058_, lean_object* v_tail_4059_, lean_object* v_params_4060_, lean_object* v_numIndices_4061_, lean_object* v___x_4062_, lean_object* v___x_4063_, lean_object* v___x_4064_, lean_object* v___x_4065_, lean_object* v___x_4066_, lean_object* v_val_4067_, lean_object* v___x_4068_, lean_object* v_declName_4069_, lean_object* v_levelParams_4070_, lean_object* v___x_4071_, lean_object* v_numParams_4072_, lean_object* v___x_4073_, lean_object* v_heq_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; uint8_t v___x_4087_; uint8_t v___x_4088_; uint8_t v___x_4089_; lean_object* v___x_4090_; 
v___x_4080_ = lean_unsigned_to_nat(3u);
v___x_4081_ = lean_mk_empty_array_with_capacity(v___x_4080_);
lean_inc_ref(v___x_4054_);
v___x_4082_ = lean_array_push(v___x_4081_, v___x_4054_);
lean_inc_ref(v___x_4055_);
v___x_4083_ = lean_array_push(v___x_4082_, v___x_4055_);
lean_inc_ref(v_heq_4074_);
v___x_4084_ = lean_array_push(v___x_4083_, v_heq_4074_);
lean_inc_ref(v_is_4056_);
v___x_4085_ = l_Array_append___redArg(v_is_4056_, v___x_4084_);
lean_dec_ref(v___x_4084_);
v___x_4086_ = l_Lean_mkSort(v_head_4057_);
v___x_4087_ = 0;
v___x_4088_ = 1;
v___x_4089_ = 1;
v___x_4090_ = l_Lean_Meta_mkForallFVars(v___x_4085_, v___x_4086_, v___x_4087_, v___x_4088_, v___x_4088_, v___x_4089_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4090_) == 0)
{
lean_object* v_a_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___f_4095_; lean_object* v___x_4096_; uint8_t v___x_4097_; lean_object* v___x_4098_; 
v_a_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc(v_a_4091_);
lean_dec_ref_known(v___x_4090_, 1);
v___x_4092_ = lean_box(v___x_4087_);
v___x_4093_ = lean_box(v___x_4088_);
v___x_4094_ = lean_box(v___x_4089_);
v___f_4095_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4095_, 0, v_ctors_4058_);
lean_closure_set(v___f_4095_, 1, v_tail_4059_);
lean_closure_set(v___f_4095_, 2, v_params_4060_);
lean_closure_set(v___f_4095_, 3, v_numIndices_4061_);
lean_closure_set(v___f_4095_, 4, v___x_4062_);
lean_closure_set(v___f_4095_, 5, v___x_4085_);
lean_closure_set(v___f_4095_, 6, v___x_4092_);
lean_closure_set(v___f_4095_, 7, v___x_4093_);
lean_closure_set(v___f_4095_, 8, v___x_4094_);
lean_closure_set(v___f_4095_, 9, v_is_4056_);
lean_closure_set(v___f_4095_, 10, v___x_4055_);
lean_closure_set(v___f_4095_, 11, v___x_4054_);
lean_closure_set(v___f_4095_, 12, v___x_4063_);
lean_closure_set(v___f_4095_, 13, v___x_4064_);
lean_closure_set(v___f_4095_, 14, v___x_4065_);
lean_closure_set(v___f_4095_, 15, v___x_4066_);
lean_closure_set(v___f_4095_, 16, v_heq_4074_);
lean_closure_set(v___f_4095_, 17, v_val_4067_);
lean_closure_set(v___f_4095_, 18, v___x_4068_);
lean_closure_set(v___f_4095_, 19, v_declName_4069_);
lean_closure_set(v___f_4095_, 20, v_levelParams_4070_);
lean_closure_set(v___f_4095_, 21, v___x_4080_);
lean_closure_set(v___f_4095_, 22, v___x_4071_);
lean_closure_set(v___f_4095_, 23, v_numParams_4072_);
lean_closure_set(v___f_4095_, 24, v___x_4073_);
v___x_4096_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4097_ = 0;
v___x_4098_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4096_, v___x_4089_, v_a_4091_, v___f_4095_, v___x_4097_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
return v___x_4098_;
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec_ref(v___x_4085_);
lean_dec_ref(v_heq_4074_);
lean_dec_ref(v___x_4073_);
lean_dec(v_numParams_4072_);
lean_dec(v___x_4071_);
lean_dec(v_levelParams_4070_);
lean_dec(v_declName_4069_);
lean_dec_ref(v___x_4068_);
lean_dec_ref(v_val_4067_);
lean_dec_ref(v___x_4066_);
lean_dec_ref(v___x_4065_);
lean_dec(v___x_4064_);
lean_dec(v___x_4063_);
lean_dec(v___x_4062_);
lean_dec(v_numIndices_4061_);
lean_dec_ref(v_params_4060_);
lean_dec(v_tail_4059_);
lean_dec(v_ctors_4058_);
lean_dec_ref(v_is_4056_);
lean_dec_ref(v___x_4055_);
lean_dec_ref(v___x_4054_);
v_a_4099_ = lean_ctor_get(v___x_4090_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4090_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4090_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4090_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4107_ = _args[0];
lean_object* v___x_4108_ = _args[1];
lean_object* v_is_4109_ = _args[2];
lean_object* v_head_4110_ = _args[3];
lean_object* v_ctors_4111_ = _args[4];
lean_object* v_tail_4112_ = _args[5];
lean_object* v_params_4113_ = _args[6];
lean_object* v_numIndices_4114_ = _args[7];
lean_object* v___x_4115_ = _args[8];
lean_object* v___x_4116_ = _args[9];
lean_object* v___x_4117_ = _args[10];
lean_object* v___x_4118_ = _args[11];
lean_object* v___x_4119_ = _args[12];
lean_object* v_val_4120_ = _args[13];
lean_object* v___x_4121_ = _args[14];
lean_object* v_declName_4122_ = _args[15];
lean_object* v_levelParams_4123_ = _args[16];
lean_object* v___x_4124_ = _args[17];
lean_object* v_numParams_4125_ = _args[18];
lean_object* v___x_4126_ = _args[19];
lean_object* v_heq_4127_ = _args[20];
lean_object* v___y_4128_ = _args[21];
lean_object* v___y_4129_ = _args[22];
lean_object* v___y_4130_ = _args[23];
lean_object* v___y_4131_ = _args[24];
lean_object* v___y_4132_ = _args[25];
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4107_, v___x_4108_, v_is_4109_, v_head_4110_, v_ctors_4111_, v_tail_4112_, v_params_4113_, v_numIndices_4114_, v___x_4115_, v___x_4116_, v___x_4117_, v___x_4118_, v___x_4119_, v_val_4120_, v___x_4121_, v_declName_4122_, v_levelParams_4123_, v___x_4124_, v_numParams_4125_, v___x_4126_, v_heq_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4134_, lean_object* v_x1_4135_, lean_object* v_indName_4136_, lean_object* v_tail_4137_, lean_object* v_params_4138_, lean_object* v_is_4139_, lean_object* v___x_4140_, lean_object* v_head_4141_, lean_object* v_ctors_4142_, lean_object* v_numIndices_4143_, lean_object* v___x_4144_, lean_object* v___x_4145_, lean_object* v_val_4146_, lean_object* v_declName_4147_, lean_object* v_levelParams_4148_, lean_object* v_numParams_4149_, lean_object* v___x_4150_, lean_object* v_x2_4151_, lean_object* v_x_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4158_ = lean_unsigned_to_nat(0u);
v___x_4159_ = lean_array_get_borrowed(v___x_4134_, v_x1_4135_, v___x_4158_);
v___x_4160_ = lean_array_get_borrowed(v___x_4134_, v_x2_4151_, v___x_4158_);
v___x_4161_ = l_Lean_mkCtorIdxName(v_indName_4136_);
lean_inc(v_tail_4137_);
v___x_4162_ = l_Lean_mkConst(v___x_4161_, v_tail_4137_);
lean_inc_ref(v_params_4138_);
v___x_4163_ = l_Array_append___redArg(v_params_4138_, v_is_4139_);
v___x_4164_ = lean_mk_empty_array_with_capacity(v___x_4140_);
lean_inc(v___x_4159_);
lean_inc_ref_n(v___x_4164_, 2);
v___x_4165_ = lean_array_push(v___x_4164_, v___x_4159_);
lean_inc_ref(v___x_4163_);
v___x_4166_ = l_Array_append___redArg(v___x_4163_, v___x_4165_);
lean_inc_ref(v___x_4162_);
v___x_4167_ = l_Lean_mkAppN(v___x_4162_, v___x_4166_);
lean_dec_ref(v___x_4166_);
lean_inc(v___x_4160_);
v___x_4168_ = lean_array_push(v___x_4164_, v___x_4160_);
v___x_4169_ = l_Array_append___redArg(v___x_4163_, v___x_4168_);
v___x_4170_ = l_Lean_mkAppN(v___x_4162_, v___x_4169_);
lean_dec_ref(v___x_4169_);
v___x_4171_ = l_Lean_Meta_mkEq(v___x_4167_, v___x_4170_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4171_) == 0)
{
lean_object* v_a_4172_; lean_object* v___f_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v_a_4172_ = lean_ctor_get(v___x_4171_, 0);
lean_inc(v_a_4172_);
lean_dec_ref_known(v___x_4171_, 1);
lean_inc(v___x_4160_);
lean_inc(v___x_4159_);
v___f_4173_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4173_, 0, v___x_4159_);
lean_closure_set(v___f_4173_, 1, v___x_4160_);
lean_closure_set(v___f_4173_, 2, v_is_4139_);
lean_closure_set(v___f_4173_, 3, v_head_4141_);
lean_closure_set(v___f_4173_, 4, v_ctors_4142_);
lean_closure_set(v___f_4173_, 5, v_tail_4137_);
lean_closure_set(v___f_4173_, 6, v_params_4138_);
lean_closure_set(v___f_4173_, 7, v_numIndices_4143_);
lean_closure_set(v___f_4173_, 8, v___x_4140_);
lean_closure_set(v___f_4173_, 9, v___x_4144_);
lean_closure_set(v___f_4173_, 10, v___x_4145_);
lean_closure_set(v___f_4173_, 11, v___x_4165_);
lean_closure_set(v___f_4173_, 12, v___x_4168_);
lean_closure_set(v___f_4173_, 13, v_val_4146_);
lean_closure_set(v___f_4173_, 14, v___x_4164_);
lean_closure_set(v___f_4173_, 15, v_declName_4147_);
lean_closure_set(v___f_4173_, 16, v_levelParams_4148_);
lean_closure_set(v___f_4173_, 17, v___x_4158_);
lean_closure_set(v___f_4173_, 18, v_numParams_4149_);
lean_closure_set(v___f_4173_, 19, v___x_4150_);
v___x_4174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4175_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4174_, v_a_4172_, v___f_4173_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
return v___x_4175_;
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec_ref(v___x_4168_);
lean_dec_ref(v___x_4165_);
lean_dec_ref(v___x_4164_);
lean_dec_ref(v___x_4150_);
lean_dec(v_numParams_4149_);
lean_dec(v_levelParams_4148_);
lean_dec(v_declName_4147_);
lean_dec_ref(v_val_4146_);
lean_dec(v___x_4145_);
lean_dec(v___x_4144_);
lean_dec(v_numIndices_4143_);
lean_dec(v_ctors_4142_);
lean_dec(v_head_4141_);
lean_dec(v___x_4140_);
lean_dec_ref(v_is_4139_);
lean_dec_ref(v_params_4138_);
lean_dec(v_tail_4137_);
v_a_4176_ = lean_ctor_get(v___x_4171_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4171_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4171_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4171_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4184_ = _args[0];
lean_object* v_x1_4185_ = _args[1];
lean_object* v_indName_4186_ = _args[2];
lean_object* v_tail_4187_ = _args[3];
lean_object* v_params_4188_ = _args[4];
lean_object* v_is_4189_ = _args[5];
lean_object* v___x_4190_ = _args[6];
lean_object* v_head_4191_ = _args[7];
lean_object* v_ctors_4192_ = _args[8];
lean_object* v_numIndices_4193_ = _args[9];
lean_object* v___x_4194_ = _args[10];
lean_object* v___x_4195_ = _args[11];
lean_object* v_val_4196_ = _args[12];
lean_object* v_declName_4197_ = _args[13];
lean_object* v_levelParams_4198_ = _args[14];
lean_object* v_numParams_4199_ = _args[15];
lean_object* v___x_4200_ = _args[16];
lean_object* v_x2_4201_ = _args[17];
lean_object* v_x_4202_ = _args[18];
lean_object* v___y_4203_ = _args[19];
lean_object* v___y_4204_ = _args[20];
lean_object* v___y_4205_ = _args[21];
lean_object* v___y_4206_ = _args[22];
lean_object* v___y_4207_ = _args[23];
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4184_, v_x1_4185_, v_indName_4186_, v_tail_4187_, v_params_4188_, v_is_4189_, v___x_4190_, v_head_4191_, v_ctors_4192_, v_numIndices_4193_, v___x_4194_, v___x_4195_, v_val_4196_, v_declName_4197_, v_levelParams_4198_, v_numParams_4199_, v___x_4200_, v_x2_4201_, v_x_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_);
lean_dec(v___y_4206_);
lean_dec_ref(v___y_4205_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
lean_dec_ref(v_x_4202_);
lean_dec_ref(v_x2_4201_);
lean_dec_ref(v_x1_4185_);
lean_dec_ref(v___x_4184_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4209_, lean_object* v_indName_4210_, lean_object* v_tail_4211_, lean_object* v_params_4212_, lean_object* v_is_4213_, lean_object* v___x_4214_, lean_object* v_head_4215_, lean_object* v_ctors_4216_, lean_object* v_numIndices_4217_, lean_object* v___x_4218_, lean_object* v___x_4219_, lean_object* v_val_4220_, lean_object* v_declName_4221_, lean_object* v_levelParams_4222_, lean_object* v_numParams_4223_, lean_object* v___x_4224_, lean_object* v_t_4225_, lean_object* v___x_4226_, lean_object* v_x1_4227_, lean_object* v_x_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_){
_start:
{
lean_object* v___f_4234_; uint8_t v___x_4235_; lean_object* v___x_4236_; 
v___f_4234_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4234_, 0, v___x_4209_);
lean_closure_set(v___f_4234_, 1, v_x1_4227_);
lean_closure_set(v___f_4234_, 2, v_indName_4210_);
lean_closure_set(v___f_4234_, 3, v_tail_4211_);
lean_closure_set(v___f_4234_, 4, v_params_4212_);
lean_closure_set(v___f_4234_, 5, v_is_4213_);
lean_closure_set(v___f_4234_, 6, v___x_4214_);
lean_closure_set(v___f_4234_, 7, v_head_4215_);
lean_closure_set(v___f_4234_, 8, v_ctors_4216_);
lean_closure_set(v___f_4234_, 9, v_numIndices_4217_);
lean_closure_set(v___f_4234_, 10, v___x_4218_);
lean_closure_set(v___f_4234_, 11, v___x_4219_);
lean_closure_set(v___f_4234_, 12, v_val_4220_);
lean_closure_set(v___f_4234_, 13, v_declName_4221_);
lean_closure_set(v___f_4234_, 14, v_levelParams_4222_);
lean_closure_set(v___f_4234_, 15, v_numParams_4223_);
lean_closure_set(v___f_4234_, 16, v___x_4224_);
v___x_4235_ = 0;
v___x_4236_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4225_, v___x_4226_, v___f_4234_, v___x_4235_, v___x_4235_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4237_ = _args[0];
lean_object* v_indName_4238_ = _args[1];
lean_object* v_tail_4239_ = _args[2];
lean_object* v_params_4240_ = _args[3];
lean_object* v_is_4241_ = _args[4];
lean_object* v___x_4242_ = _args[5];
lean_object* v_head_4243_ = _args[6];
lean_object* v_ctors_4244_ = _args[7];
lean_object* v_numIndices_4245_ = _args[8];
lean_object* v___x_4246_ = _args[9];
lean_object* v___x_4247_ = _args[10];
lean_object* v_val_4248_ = _args[11];
lean_object* v_declName_4249_ = _args[12];
lean_object* v_levelParams_4250_ = _args[13];
lean_object* v_numParams_4251_ = _args[14];
lean_object* v___x_4252_ = _args[15];
lean_object* v_t_4253_ = _args[16];
lean_object* v___x_4254_ = _args[17];
lean_object* v_x1_4255_ = _args[18];
lean_object* v_x_4256_ = _args[19];
lean_object* v___y_4257_ = _args[20];
lean_object* v___y_4258_ = _args[21];
lean_object* v___y_4259_ = _args[22];
lean_object* v___y_4260_ = _args[23];
lean_object* v___y_4261_ = _args[24];
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4237_, v_indName_4238_, v_tail_4239_, v_params_4240_, v_is_4241_, v___x_4242_, v_head_4243_, v_ctors_4244_, v_numIndices_4245_, v___x_4246_, v___x_4247_, v_val_4248_, v_declName_4249_, v_levelParams_4250_, v_numParams_4251_, v___x_4252_, v_t_4253_, v___x_4254_, v_x1_4255_, v_x_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec_ref(v_x_4256_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4263_, lean_object* v_indName_4264_, lean_object* v_tail_4265_, lean_object* v_params_4266_, lean_object* v_head_4267_, lean_object* v_ctors_4268_, lean_object* v_numIndices_4269_, lean_object* v___x_4270_, lean_object* v___x_4271_, lean_object* v_val_4272_, lean_object* v_declName_4273_, lean_object* v_levelParams_4274_, lean_object* v_numParams_4275_, lean_object* v___x_4276_, lean_object* v_is_4277_, lean_object* v_t_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___f_4286_; uint8_t v___x_4287_; lean_object* v___x_4288_; 
v___x_4284_ = lean_unsigned_to_nat(1u);
v___x_4285_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4278_);
v___f_4286_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4286_, 0, v___x_4263_);
lean_closure_set(v___f_4286_, 1, v_indName_4264_);
lean_closure_set(v___f_4286_, 2, v_tail_4265_);
lean_closure_set(v___f_4286_, 3, v_params_4266_);
lean_closure_set(v___f_4286_, 4, v_is_4277_);
lean_closure_set(v___f_4286_, 5, v___x_4284_);
lean_closure_set(v___f_4286_, 6, v_head_4267_);
lean_closure_set(v___f_4286_, 7, v_ctors_4268_);
lean_closure_set(v___f_4286_, 8, v_numIndices_4269_);
lean_closure_set(v___f_4286_, 9, v___x_4270_);
lean_closure_set(v___f_4286_, 10, v___x_4271_);
lean_closure_set(v___f_4286_, 11, v_val_4272_);
lean_closure_set(v___f_4286_, 12, v_declName_4273_);
lean_closure_set(v___f_4286_, 13, v_levelParams_4274_);
lean_closure_set(v___f_4286_, 14, v_numParams_4275_);
lean_closure_set(v___f_4286_, 15, v___x_4276_);
lean_closure_set(v___f_4286_, 16, v_t_4278_);
lean_closure_set(v___f_4286_, 17, v___x_4285_);
v___x_4287_ = 0;
v___x_4288_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4278_, v___x_4285_, v___f_4286_, v___x_4287_, v___x_4287_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
return v___x_4288_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4289_ = _args[0];
lean_object* v_indName_4290_ = _args[1];
lean_object* v_tail_4291_ = _args[2];
lean_object* v_params_4292_ = _args[3];
lean_object* v_head_4293_ = _args[4];
lean_object* v_ctors_4294_ = _args[5];
lean_object* v_numIndices_4295_ = _args[6];
lean_object* v___x_4296_ = _args[7];
lean_object* v___x_4297_ = _args[8];
lean_object* v_val_4298_ = _args[9];
lean_object* v_declName_4299_ = _args[10];
lean_object* v_levelParams_4300_ = _args[11];
lean_object* v_numParams_4301_ = _args[12];
lean_object* v___x_4302_ = _args[13];
lean_object* v_is_4303_ = _args[14];
lean_object* v_t_4304_ = _args[15];
lean_object* v___y_4305_ = _args[16];
lean_object* v___y_4306_ = _args[17];
lean_object* v___y_4307_ = _args[18];
lean_object* v___y_4308_ = _args[19];
lean_object* v___y_4309_ = _args[20];
_start:
{
lean_object* v_res_4310_; 
v_res_4310_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4289_, v_indName_4290_, v_tail_4291_, v_params_4292_, v_head_4293_, v_ctors_4294_, v_numIndices_4295_, v___x_4296_, v___x_4297_, v_val_4298_, v_declName_4299_, v_levelParams_4300_, v_numParams_4301_, v___x_4302_, v_is_4303_, v_t_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
lean_dec(v___y_4308_);
lean_dec_ref(v___y_4307_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4311_, lean_object* v_indName_4312_, lean_object* v_tail_4313_, lean_object* v_head_4314_, lean_object* v_ctors_4315_, lean_object* v_numIndices_4316_, lean_object* v___x_4317_, lean_object* v___x_4318_, lean_object* v_val_4319_, lean_object* v_declName_4320_, lean_object* v_levelParams_4321_, lean_object* v_numParams_4322_, lean_object* v_params_4323_, lean_object* v_t_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v___x_4330_; lean_object* v___f_4331_; lean_object* v___x_4332_; uint8_t v___x_4333_; lean_object* v___x_4334_; 
v___x_4330_ = l_Lean_Expr_bindingBody_x21(v_t_4324_);
lean_inc_ref(v___x_4330_);
lean_inc(v_numIndices_4316_);
v___f_4331_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4331_, 0, v___x_4311_);
lean_closure_set(v___f_4331_, 1, v_indName_4312_);
lean_closure_set(v___f_4331_, 2, v_tail_4313_);
lean_closure_set(v___f_4331_, 3, v_params_4323_);
lean_closure_set(v___f_4331_, 4, v_head_4314_);
lean_closure_set(v___f_4331_, 5, v_ctors_4315_);
lean_closure_set(v___f_4331_, 6, v_numIndices_4316_);
lean_closure_set(v___f_4331_, 7, v___x_4317_);
lean_closure_set(v___f_4331_, 8, v___x_4318_);
lean_closure_set(v___f_4331_, 9, v_val_4319_);
lean_closure_set(v___f_4331_, 10, v_declName_4320_);
lean_closure_set(v___f_4331_, 11, v_levelParams_4321_);
lean_closure_set(v___f_4331_, 12, v_numParams_4322_);
lean_closure_set(v___f_4331_, 13, v___x_4330_);
v___x_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4332_, 0, v_numIndices_4316_);
v___x_4333_ = 0;
v___x_4334_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4330_, v___x_4332_, v___f_4331_, v___x_4333_, v___x_4333_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4335_ = _args[0];
lean_object* v_indName_4336_ = _args[1];
lean_object* v_tail_4337_ = _args[2];
lean_object* v_head_4338_ = _args[3];
lean_object* v_ctors_4339_ = _args[4];
lean_object* v_numIndices_4340_ = _args[5];
lean_object* v___x_4341_ = _args[6];
lean_object* v___x_4342_ = _args[7];
lean_object* v_val_4343_ = _args[8];
lean_object* v_declName_4344_ = _args[9];
lean_object* v_levelParams_4345_ = _args[10];
lean_object* v_numParams_4346_ = _args[11];
lean_object* v_params_4347_ = _args[12];
lean_object* v_t_4348_ = _args[13];
lean_object* v___y_4349_ = _args[14];
lean_object* v___y_4350_ = _args[15];
lean_object* v___y_4351_ = _args[16];
lean_object* v___y_4352_ = _args[17];
lean_object* v___y_4353_ = _args[18];
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4335_, v_indName_4336_, v_tail_4337_, v_head_4338_, v_ctors_4339_, v_numIndices_4340_, v___x_4341_, v___x_4342_, v_val_4343_, v_declName_4344_, v_levelParams_4345_, v_numParams_4346_, v_params_4347_, v_t_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
lean_dec(v___y_4350_);
lean_dec_ref(v___y_4349_);
lean_dec_ref(v_t_4348_);
return v_res_4354_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; 
v___x_4359_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4360_ = lean_unsigned_to_nat(58u);
v___x_4361_ = lean_unsigned_to_nat(142u);
v___x_4362_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4363_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4364_ = l_mkPanicMessageWithDecl(v___x_4363_, v___x_4362_, v___x_4361_, v___x_4360_, v___x_4359_);
return v___x_4364_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4365_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4366_ = lean_unsigned_to_nat(60u);
v___x_4367_ = lean_unsigned_to_nat(136u);
v___x_4368_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4369_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4370_ = l_mkPanicMessageWithDecl(v___x_4369_, v___x_4368_, v___x_4367_, v___x_4366_, v___x_4365_);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4371_, lean_object* v_indName_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_){
_start:
{
lean_object* v___x_4378_; 
lean_inc(v_indName_4372_);
v___x_4378_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_object* v_a_4379_; 
v_a_4379_ = lean_ctor_get(v___x_4378_, 0);
lean_inc(v_a_4379_);
lean_dec_ref_known(v___x_4378_, 1);
if (lean_obj_tag(v_a_4379_) == 5)
{
lean_object* v_val_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; 
v_val_4380_ = lean_ctor_get(v_a_4379_, 0);
lean_inc_ref(v_val_4380_);
lean_dec_ref_known(v_a_4379_, 1);
v___x_4381_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4371_);
v___x_4382_ = l_Lean_Name_append(v_declName_4371_, v___x_4381_);
lean_inc(v_indName_4372_);
lean_inc(v___x_4382_);
v___x_4383_ = l_Lean_mkCasesOnSameCtorHet(v___x_4382_, v_indName_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4416_; 
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4383_);
if (v_isSharedCheck_4416_ == 0)
{
lean_object* v_unused_4417_; 
v_unused_4417_ = lean_ctor_get(v___x_4383_, 0);
lean_dec(v_unused_4417_);
v___x_4385_ = v___x_4383_;
v_isShared_4386_ = v_isSharedCheck_4416_;
goto v_resetjp_4384_;
}
else
{
lean_dec(v___x_4383_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4416_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4387_; lean_object* v___x_4388_; 
lean_inc(v_indName_4372_);
v___x_4387_ = l_Lean_mkCasesOnName(v_indName_4372_);
v___x_4388_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4387_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v_levelParams_4390_; lean_object* v_type_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v_levelParams_4390_ = lean_ctor_get(v_a_4389_, 1);
lean_inc_n(v_levelParams_4390_, 2);
v_type_4391_ = lean_ctor_get(v_a_4389_, 2);
lean_inc_ref(v_type_4391_);
lean_dec(v_a_4389_);
v___x_4392_ = lean_box(0);
v___x_4393_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4390_, v___x_4392_);
if (lean_obj_tag(v___x_4393_) == 1)
{
lean_object* v_head_4394_; lean_object* v_tail_4395_; lean_object* v_numParams_4396_; lean_object* v_numIndices_4397_; lean_object* v_ctors_4398_; lean_object* v___x_4399_; lean_object* v___f_4400_; lean_object* v___x_4402_; 
v_head_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc(v_head_4394_);
v_tail_4395_ = lean_ctor_get(v___x_4393_, 1);
lean_inc(v_tail_4395_);
v_numParams_4396_ = lean_ctor_get(v_val_4380_, 1);
lean_inc_n(v_numParams_4396_, 2);
v_numIndices_4397_ = lean_ctor_get(v_val_4380_, 2);
lean_inc(v_numIndices_4397_);
v_ctors_4398_ = lean_ctor_get(v_val_4380_, 4);
lean_inc(v_ctors_4398_);
v___x_4399_ = l_Lean_instInhabitedExpr;
v___f_4400_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4400_, 0, v___x_4399_);
lean_closure_set(v___f_4400_, 1, v_indName_4372_);
lean_closure_set(v___f_4400_, 2, v_tail_4395_);
lean_closure_set(v___f_4400_, 3, v_head_4394_);
lean_closure_set(v___f_4400_, 4, v_ctors_4398_);
lean_closure_set(v___f_4400_, 5, v_numIndices_4397_);
lean_closure_set(v___f_4400_, 6, v___x_4382_);
lean_closure_set(v___f_4400_, 7, v___x_4393_);
lean_closure_set(v___f_4400_, 8, v_val_4380_);
lean_closure_set(v___f_4400_, 9, v_declName_4371_);
lean_closure_set(v___f_4400_, 10, v_levelParams_4390_);
lean_closure_set(v___f_4400_, 11, v_numParams_4396_);
if (v_isShared_4386_ == 0)
{
lean_ctor_set_tag(v___x_4385_, 1);
lean_ctor_set(v___x_4385_, 0, v_numParams_4396_);
v___x_4402_ = v___x_4385_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_numParams_4396_);
v___x_4402_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
uint8_t v___x_4403_; lean_object* v___x_4404_; 
v___x_4403_ = 0;
v___x_4404_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4391_, v___x_4402_, v___f_4400_, v___x_4403_, v___x_4403_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
return v___x_4404_;
}
}
else
{
lean_object* v___x_4406_; lean_object* v___x_4407_; 
lean_dec(v___x_4393_);
lean_dec_ref(v_type_4391_);
lean_dec(v_levelParams_4390_);
lean_del_object(v___x_4385_);
lean_dec(v___x_4382_);
lean_dec_ref(v_val_4380_);
lean_dec(v_indName_4372_);
lean_dec(v_declName_4371_);
v___x_4406_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4407_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4406_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
return v___x_4407_;
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_del_object(v___x_4385_);
lean_dec(v___x_4382_);
lean_dec_ref(v_val_4380_);
lean_dec(v_indName_4372_);
lean_dec(v_declName_4371_);
v_a_4408_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4388_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4388_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
}
else
{
lean_dec(v___x_4382_);
lean_dec_ref(v_val_4380_);
lean_dec(v_indName_4372_);
lean_dec(v_declName_4371_);
return v___x_4383_;
}
}
else
{
lean_object* v___x_4418_; lean_object* v___x_4419_; 
lean_dec(v_a_4379_);
lean_dec(v_indName_4372_);
lean_dec(v_declName_4371_);
v___x_4418_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4419_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4418_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_);
return v___x_4419_;
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_dec(v_indName_4372_);
lean_dec(v_declName_4371_);
v_a_4420_ = lean_ctor_get(v___x_4378_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4378_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4378_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4378_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4428_, lean_object* v_indName_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_){
_start:
{
lean_object* v_res_4435_; 
v_res_4435_ = l_Lean_mkCasesOnSameCtor(v_declName_4428_, v_indName_4429_, v_a_4430_, v_a_4431_, v_a_4432_, v_a_4433_);
lean_dec(v_a_4433_);
lean_dec_ref(v_a_4432_);
lean_dec(v_a_4431_);
lean_dec_ref(v_a_4430_);
return v_res_4435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4436_, lean_object* v_params_4437_, lean_object* v_motive_4438_, lean_object* v_as_4439_, size_t v_sz_4440_, size_t v_i_4441_, lean_object* v_bs_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4436_, v_params_4437_, v_motive_4438_, v_sz_4440_, v_i_4441_, v_bs_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4449_, lean_object* v_params_4450_, lean_object* v_motive_4451_, lean_object* v_as_4452_, lean_object* v_sz_4453_, lean_object* v_i_4454_, lean_object* v_bs_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
size_t v_sz_boxed_4461_; size_t v_i_boxed_4462_; lean_object* v_res_4463_; 
v_sz_boxed_4461_ = lean_unbox_usize(v_sz_4453_);
lean_dec(v_sz_4453_);
v_i_boxed_4462_ = lean_unbox_usize(v_i_4454_);
lean_dec(v_i_4454_);
v_res_4463_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4449_, v_params_4450_, v_motive_4451_, v_as_4452_, v_sz_boxed_4461_, v_i_boxed_4462_, v_bs_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec_ref(v_as_4452_);
lean_dec_ref(v_params_4450_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4464_, lean_object* v_params_4465_, lean_object* v_a_4466_, lean_object* v_snd_4467_, lean_object* v_alts_4468_, lean_object* v_as_4469_, size_t v_sz_4470_, size_t v_i_4471_, lean_object* v_bs_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4464_, v_params_4465_, v_a_4466_, v_snd_4467_, v_alts_4468_, v_sz_4470_, v_i_4471_, v_bs_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4479_, lean_object* v_params_4480_, lean_object* v_a_4481_, lean_object* v_snd_4482_, lean_object* v_alts_4483_, lean_object* v_as_4484_, lean_object* v_sz_4485_, lean_object* v_i_4486_, lean_object* v_bs_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
size_t v_sz_boxed_4493_; size_t v_i_boxed_4494_; lean_object* v_res_4495_; 
v_sz_boxed_4493_ = lean_unbox_usize(v_sz_4485_);
lean_dec(v_sz_4485_);
v_i_boxed_4494_ = lean_unbox_usize(v_i_4486_);
lean_dec(v_i_4486_);
v_res_4495_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4479_, v_params_4480_, v_a_4481_, v_snd_4482_, v_alts_4483_, v_as_4484_, v_sz_boxed_4493_, v_i_boxed_4494_, v_bs_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec_ref(v_as_4484_);
lean_dec_ref(v_params_4480_);
return v_res_4495_;
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
