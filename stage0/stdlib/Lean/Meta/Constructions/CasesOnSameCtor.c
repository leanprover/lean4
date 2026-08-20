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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
v___x_302_ = lean_st_ref_put(v___y_280_, v___x_301_);
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
v___x_313_ = lean_st_ref_put(v___y_283_, v___x_312_);
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
lean_object* v___x_345_; lean_object* v_env_346_; lean_object* v___x_347_; uint8_t v_isModule_348_; 
v___x_345_ = lean_st_ref_get(v___y_343_);
v_env_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc_ref(v_env_346_);
lean_dec(v___x_345_);
v___x_347_ = l_Lean_Environment_header(v_env_346_);
v_isModule_348_ = lean_ctor_get_uint8(v___x_347_, sizeof(void*)*7 + 4);
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
v_isExporting_350_ = lean_ctor_get_uint8(v_env_346_, sizeof(void*)*8);
lean_dec_ref(v_env_346_);
if (v_isExporting_339_ == 0)
{
if (v_isExporting_350_ == 0)
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
lean_object* v___x_417_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v___x_417_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
return v___x_417_;
}
}
v___jp_351_:
{
lean_object* v___x_352_; lean_object* v_env_353_; lean_object* v_nextMacroScope_354_; lean_object* v_ngen_355_; lean_object* v_auxDeclNGen_356_; lean_object* v_traceState_357_; lean_object* v_messages_358_; lean_object* v_infoState_359_; lean_object* v_snapshotTasks_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_414_; 
v___x_352_ = lean_st_ref_take(v___y_343_);
v_env_353_ = lean_ctor_get(v___x_352_, 0);
v_nextMacroScope_354_ = lean_ctor_get(v___x_352_, 1);
v_ngen_355_ = lean_ctor_get(v___x_352_, 2);
v_auxDeclNGen_356_ = lean_ctor_get(v___x_352_, 3);
v_traceState_357_ = lean_ctor_get(v___x_352_, 4);
v_messages_358_ = lean_ctor_get(v___x_352_, 6);
v_infoState_359_ = lean_ctor_get(v___x_352_, 7);
v_snapshotTasks_360_ = lean_ctor_get(v___x_352_, 8);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v___x_352_, 5);
lean_dec(v_unused_415_);
v___x_362_ = v___x_352_;
v_isShared_363_ = v_isSharedCheck_414_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_snapshotTasks_360_);
lean_inc(v_infoState_359_);
lean_inc(v_messages_358_);
lean_inc(v_traceState_357_);
lean_inc(v_auxDeclNGen_356_);
lean_inc(v_ngen_355_);
lean_inc(v_nextMacroScope_354_);
lean_inc(v_env_353_);
lean_dec(v___x_352_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_414_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_364_ = l_Lean_Environment_setExporting(v_env_353_, v_isExporting_339_);
v___x_365_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 5, v___x_365_);
lean_ctor_set(v___x_362_, 0, v___x_364_);
v___x_367_ = v___x_362_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_364_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_nextMacroScope_354_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_ngen_355_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_auxDeclNGen_356_);
lean_ctor_set(v_reuseFailAlloc_413_, 4, v_traceState_357_);
lean_ctor_set(v_reuseFailAlloc_413_, 5, v___x_365_);
lean_ctor_set(v_reuseFailAlloc_413_, 6, v_messages_358_);
lean_ctor_set(v_reuseFailAlloc_413_, 7, v_infoState_359_);
lean_ctor_set(v_reuseFailAlloc_413_, 8, v_snapshotTasks_360_);
v___x_367_ = v_reuseFailAlloc_413_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v_mctx_370_; lean_object* v_zetaDeltaFVarIds_371_; lean_object* v_postponed_372_; lean_object* v_diag_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_411_; 
v___x_368_ = lean_st_ref_put(v___y_343_, v___x_367_);
v___x_369_ = lean_st_ref_take(v___y_341_);
v_mctx_370_ = lean_ctor_get(v___x_369_, 0);
v_zetaDeltaFVarIds_371_ = lean_ctor_get(v___x_369_, 2);
v_postponed_372_ = lean_ctor_get(v___x_369_, 3);
v_diag_373_ = lean_ctor_get(v___x_369_, 4);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_369_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_369_, 1);
lean_dec(v_unused_412_);
v___x_375_ = v___x_369_;
v_isShared_376_ = v_isSharedCheck_411_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_diag_373_);
lean_inc(v_postponed_372_);
lean_inc(v_zetaDeltaFVarIds_371_);
lean_inc(v_mctx_370_);
lean_dec(v___x_369_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_411_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_377_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 1, v___x_377_);
v___x_379_ = v___x_375_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_mctx_370_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_zetaDeltaFVarIds_371_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_postponed_372_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_diag_373_);
v___x_379_ = v_reuseFailAlloc_410_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v_r_381_; 
v___x_380_ = lean_st_ref_put(v___y_341_, v___x_379_);
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
v_r_381_ = lean_apply_5(v_x_338_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, lean_box(0));
if (lean_obj_tag(v_r_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_398_; 
v_a_382_ = lean_ctor_get(v_r_381_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_r_381_);
if (v_isSharedCheck_398_ == 0)
{
v___x_384_ = v_r_381_;
v_isShared_385_ = v_isSharedCheck_398_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v_r_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_398_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
lean_inc(v_a_382_);
if (v_isShared_385_ == 0)
{
lean_ctor_set_tag(v___x_384_, 1);
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_397_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
v___x_388_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_350_, v___x_365_, v___y_341_, v___x_377_, v___x_387_);
lean_dec_ref(v___x_387_);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_395_ == 0)
{
lean_object* v_unused_396_; 
v_unused_396_ = lean_ctor_get(v___x_388_, 0);
lean_dec(v_unused_396_);
v___x_390_ = v___x_388_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_dec(v___x_388_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v_a_382_);
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_382_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_408_; 
v_a_399_ = lean_ctor_get(v_r_381_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v_r_381_, 1);
v___x_400_ = lean_box(0);
v___x_401_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_343_, v_isExporting_350_, v___x_365_, v___y_341_, v___x_377_, v___x_400_);
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
lean_ctor_set_tag(v___x_403_, 1);
lean_ctor_set(v___x_403_, 0, v_a_399_);
v___x_406_ = v___x_403_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_a_399_);
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
lean_object* v___f_453_; lean_object* v___x_15624__overap_454_; lean_object* v___x_455_; 
v___f_453_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0));
v___x_15624__overap_454_ = lean_panic_fn_borrowed(v___f_453_, v_msg_447_);
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
lean_inc(v___y_449_);
lean_inc_ref(v___y_448_);
v___x_455_ = lean_apply_5(v___x_15624__overap_454_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, lean_box(0));
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
uint8_t v___x_20718__boxed_559_; uint8_t v___x_20719__boxed_560_; uint8_t v___x_20720__boxed_561_; lean_object* v_res_562_; 
v___x_20718__boxed_559_ = lean_unbox(v___x_540_);
v___x_20719__boxed_560_ = lean_unbox(v___x_541_);
v___x_20720__boxed_561_ = lean_unbox(v___x_542_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_537_, v_ism2_538_, v_motive_539_, v___x_20718__boxed_559_, v___x_20719__boxed_560_, v___x_20720__boxed_561_, v_a_543_, v___f_544_, v_zs1_545_, v_val_546_, v___x_547_, v_indName_548_, v_v_549_, v___x_550_, v_params_551_, v___x_552_, v_h_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
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
uint8_t v___x_20830__boxed_595_; uint8_t v___x_20831__boxed_596_; uint8_t v___x_20832__boxed_597_; lean_object* v_res_598_; 
v___x_20830__boxed_595_ = lean_unbox(v___x_585_);
v___x_20831__boxed_596_ = lean_unbox(v___x_586_);
v___x_20832__boxed_597_ = lean_unbox(v___x_587_);
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_581_, v_alts_582_, v___x_583_, v_zs1_584_, v___x_20830__boxed_595_, v___x_20831__boxed_596_, v___x_20832__boxed_597_, v_zs2_588_, v_x_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
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
uint8_t v___x_20891__boxed_693_; uint8_t v___x_20892__boxed_694_; uint8_t v___x_20893__boxed_695_; lean_object* v_res_696_; 
v___x_20891__boxed_693_ = lean_unbox(v___x_669_);
v___x_20892__boxed_694_ = lean_unbox(v___x_670_);
v___x_20893__boxed_695_ = lean_unbox(v___x_671_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_666_, v_alts_667_, v___x_668_, v___x_20891__boxed_693_, v___x_20892__boxed_694_, v___x_20893__boxed_695_, v___x_672_, v___x_673_, v___x_674_, v_ism2_675_, v_motive_676_, v_a_677_, v_val_678_, v_indName_679_, v_v_680_, v___x_681_, v_params_682_, v___x_683_, v___x_684_, v___x_685_, v_zs1_686_, v_ctorRet1_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
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
uint8_t v___x_21122__boxed_862_; uint8_t v___x_21123__boxed_863_; uint8_t v___x_21124__boxed_864_; lean_object* v_res_865_; 
v___x_21122__boxed_862_ = lean_unbox(v___x_840_);
v___x_21123__boxed_863_ = lean_unbox(v___x_841_);
v___x_21124__boxed_864_ = lean_unbox(v___x_842_);
v_res_865_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_836_, v___x_837_, v_a_838_, v_ism1_839_, v___x_21122__boxed_862_, v___x_21123__boxed_863_, v___x_21124__boxed_864_, v___x_843_, v_tail_844_, v_params_845_, v_alts_846_, v_numParams_847_, v_ism2_848_, v_val_849_, v_indName_850_, v___x_851_, v___x_852_, v___x_853_, v_name_854_, v___x_855_, v_heq_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
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
uint8_t v___x_21245__boxed_928_; uint8_t v___x_21246__boxed_929_; uint8_t v___x_21247__boxed_930_; lean_object* v_res_931_; 
v___x_21245__boxed_928_ = lean_unbox(v___x_912_);
v___x_21246__boxed_929_ = lean_unbox(v___x_913_);
v___x_21247__boxed_930_ = lean_unbox(v___x_914_);
v_res_931_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_905_, v_tail_906_, v_params_907_, v_ism1_908_, v_ism2_909_, v_motive_910_, v___x_911_, v___x_21245__boxed_928_, v___x_21246__boxed_929_, v___x_21247__boxed_930_, v___x_915_, v_numParams_916_, v_val_917_, v___x_918_, v___x_919_, v_name_920_, v___x_921_, v_alts_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(lean_object* v___x_975_, lean_object* v___x_976_, lean_object* v_a_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v___x_20129__overap_983_; lean_object* v___x_984_; 
v___x_20129__overap_983_ = l_instInhabitedOfMonad___redArg(v___x_975_, v___x_976_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
v___x_984_ = lean_apply_5(v___x_20129__overap_983_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, lean_box(0));
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(lean_object* v___x_985_, lean_object* v___x_986_, lean_object* v_a_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_985_, v___x_986_, v_a_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec_ref(v___y_990_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec_ref(v_a_987_);
return v_res_993_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0(void){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_instMonadEIO(lean_box(0));
return v___x_994_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0);
v___x_996_ = l_StateRefT_x27_instMonad___redArg(v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(lean_object* v_acc_1001_, lean_object* v_declInfos_1002_, lean_object* v_k_1003_, lean_object* v_kind_1004_, lean_object* v_x_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
uint8_t v_kind_boxed_1011_; lean_object* v_res_1012_; 
v_kind_boxed_1011_ = lean_unbox(v_kind_1004_);
v_res_1012_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_1001_, v_declInfos_1002_, v_k_1003_, v_kind_boxed_1011_, v_x_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(lean_object* v_declInfos_1013_, lean_object* v_k_1014_, uint8_t v_kind_1015_, lean_object* v_acc_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1022_; lean_object* v_toApplicative_1023_; lean_object* v_toFunctor_1024_; lean_object* v_toSeq_1025_; lean_object* v_toSeqLeft_1026_; lean_object* v_toSeqRight_1027_; lean_object* v___f_1028_; lean_object* v___f_1029_; lean_object* v___f_1030_; lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___f_1033_; lean_object* v___f_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v_toApplicative_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1089_; 
v___x_1022_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_1023_ = lean_ctor_get(v___x_1022_, 0);
v_toFunctor_1024_ = lean_ctor_get(v_toApplicative_1023_, 0);
v_toSeq_1025_ = lean_ctor_get(v_toApplicative_1023_, 2);
v_toSeqLeft_1026_ = lean_ctor_get(v_toApplicative_1023_, 3);
v_toSeqRight_1027_ = lean_ctor_get(v_toApplicative_1023_, 4);
v___f_1028_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_1029_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_1024_, 2);
v___f_1030_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1030_, 0, v_toFunctor_1024_);
v___f_1031_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1031_, 0, v_toFunctor_1024_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___f_1030_);
lean_ctor_set(v___x_1032_, 1, v___f_1031_);
lean_inc(v_toSeqRight_1027_);
v___f_1033_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1033_, 0, v_toSeqRight_1027_);
lean_inc(v_toSeqLeft_1026_);
v___f_1034_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1034_, 0, v_toSeqLeft_1026_);
lean_inc(v_toSeq_1025_);
v___f_1035_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1035_, 0, v_toSeq_1025_);
v___x_1036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1032_);
lean_ctor_set(v___x_1036_, 1, v___f_1028_);
lean_ctor_set(v___x_1036_, 2, v___f_1035_);
lean_ctor_set(v___x_1036_, 3, v___f_1034_);
lean_ctor_set(v___x_1036_, 4, v___f_1033_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___f_1029_);
v___x_1038_ = l_StateRefT_x27_instMonad___redArg(v___x_1037_);
v_toApplicative_1039_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1089_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1089_ == 0)
{
lean_object* v_unused_1090_; 
v_unused_1090_ = lean_ctor_get(v___x_1038_, 1);
lean_dec(v_unused_1090_);
v___x_1041_ = v___x_1038_;
v_isShared_1042_ = v_isSharedCheck_1089_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_toApplicative_1039_);
lean_dec(v___x_1038_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1089_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v_toFunctor_1043_; lean_object* v_toSeq_1044_; lean_object* v_toSeqLeft_1045_; lean_object* v_toSeqRight_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1087_; 
v_toFunctor_1043_ = lean_ctor_get(v_toApplicative_1039_, 0);
v_toSeq_1044_ = lean_ctor_get(v_toApplicative_1039_, 2);
v_toSeqLeft_1045_ = lean_ctor_get(v_toApplicative_1039_, 3);
v_toSeqRight_1046_ = lean_ctor_get(v_toApplicative_1039_, 4);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_toApplicative_1039_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v_toApplicative_1039_, 1);
lean_dec(v_unused_1088_);
v___x_1048_ = v_toApplicative_1039_;
v_isShared_1049_ = v_isSharedCheck_1087_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_toSeqRight_1046_);
lean_inc(v_toSeqLeft_1045_);
lean_inc(v_toSeq_1044_);
lean_inc(v_toFunctor_1043_);
lean_dec(v_toApplicative_1039_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1087_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___f_1050_; lean_object* v___f_1051_; lean_object* v___f_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; lean_object* v___f_1055_; lean_object* v___f_1056_; lean_object* v___f_1057_; lean_object* v___x_1059_; 
v___f_1050_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_1051_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_1043_);
v___f_1052_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1052_, 0, v_toFunctor_1043_);
v___f_1053_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1053_, 0, v_toFunctor_1043_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___f_1052_);
lean_ctor_set(v___x_1054_, 1, v___f_1053_);
v___f_1055_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1055_, 0, v_toSeqRight_1046_);
v___f_1056_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1056_, 0, v_toSeqLeft_1045_);
v___f_1057_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1057_, 0, v_toSeq_1044_);
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 4, v___f_1055_);
lean_ctor_set(v___x_1048_, 3, v___f_1056_);
lean_ctor_set(v___x_1048_, 2, v___f_1057_);
lean_ctor_set(v___x_1048_, 1, v___f_1050_);
lean_ctor_set(v___x_1048_, 0, v___x_1054_);
v___x_1059_ = v___x_1048_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v___f_1050_);
lean_ctor_set(v_reuseFailAlloc_1086_, 2, v___f_1057_);
lean_ctor_set(v_reuseFailAlloc_1086_, 3, v___f_1056_);
lean_ctor_set(v_reuseFailAlloc_1086_, 4, v___f_1055_);
v___x_1059_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
lean_object* v___x_1061_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 1, v___f_1051_);
lean_ctor_set(v___x_1041_, 0, v___x_1059_);
v___x_1061_ = v___x_1041_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v___f_1051_);
v___x_1061_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; uint8_t v___x_1064_; 
v___x_1062_ = lean_array_get_size(v_acc_1016_);
v___x_1063_ = lean_array_get_size(v_declInfos_1013_);
v___x_1064_ = lean_nat_dec_lt(v___x_1062_, v___x_1063_);
if (v___x_1064_ == 0)
{
lean_object* v___x_1065_; 
lean_dec_ref(v___x_1061_);
lean_dec_ref(v_declInfos_1013_);
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
v___x_1065_ = lean_apply_6(v_k_1014_, v_acc_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, lean_box(0));
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_snd_1075_; lean_object* v_fst_1076_; lean_object* v_fst_1077_; lean_object* v_snd_1078_; lean_object* v___x_1079_; 
v___x_1066_ = lean_box(0);
v___x_1067_ = 0;
v___x_1068_ = l_Lean_instInhabitedExpr;
v___f_1069_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1069_, 0, v___x_1061_);
lean_closure_set(v___f_1069_, 1, v___x_1068_);
v___f_1070_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1070_, 0, v___f_1069_);
v___x_1071_ = lean_box(v___x_1067_);
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___f_1070_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1066_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_array_get(v___x_1073_, v_declInfos_1013_, v___x_1062_);
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
lean_inc(v___y_1020_);
lean_inc_ref(v___y_1019_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc_ref(v_acc_1016_);
v___x_1079_ = lean_apply_6(v_snd_1078_, v_acc_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, lean_box(0));
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___x_1081_; lean_object* v___f_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v___x_1081_ = lean_box(v_kind_1015_);
v___f_1082_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed), 10, 4);
lean_closure_set(v___f_1082_, 0, v_acc_1016_);
lean_closure_set(v___f_1082_, 1, v_declInfos_1013_);
lean_closure_set(v___f_1082_, 2, v_k_1014_);
lean_closure_set(v___f_1082_, 3, v___x_1081_);
v___x_1083_ = lean_unbox(v_fst_1077_);
lean_dec(v_fst_1077_);
v___x_1084_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_1076_, v___x_1083_, v_a_1080_, v___f_1082_, v_kind_1015_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_);
return v___x_1084_;
}
else
{
lean_dec(v_fst_1077_);
lean_dec(v_fst_1076_);
lean_dec_ref(v_acc_1016_);
lean_dec_ref(v_k_1014_);
lean_dec_ref(v_declInfos_1013_);
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
uint8_t v___x_21684__boxed_1299_; uint8_t v___x_21685__boxed_1300_; uint8_t v___x_21686__boxed_1301_; lean_object* v_res_1302_; 
v___x_21684__boxed_1299_ = lean_unbox(v___x_1287_);
v___x_21685__boxed_1300_ = lean_unbox(v___x_1288_);
v___x_21686__boxed_1301_ = lean_unbox(v___x_1289_);
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1280_, v_dummy_1281_, v___x_1282_, v___x_1283_, v___x_1284_, v_motive_1285_, v_zs1_1286_, v___x_21684__boxed_1299_, v___x_21685__boxed_1300_, v___x_21686__boxed_1301_, v_v_1290_, v___x_1291_, v_zs2_1292_, v_ctorRet2_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
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
uint8_t v___x_21825__boxed_1362_; uint8_t v___x_21826__boxed_1363_; uint8_t v___x_21827__boxed_1364_; lean_object* v_res_1365_; 
v___x_21825__boxed_1362_ = lean_unbox(v___x_1349_);
v___x_21826__boxed_1363_ = lean_unbox(v___x_1350_);
v___x_21827__boxed_1364_ = lean_unbox(v___x_1351_);
v_res_1365_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1345_, v___x_1346_, v___x_1347_, v_motive_1348_, v___x_21825__boxed_1362_, v___x_21826__boxed_1363_, v___x_21827__boxed_1364_, v_v_1352_, v___x_1353_, v_a_1354_, v_zs1_1355_, v_ctorRet1_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
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
uint8_t v___x_22005__boxed_1495_; uint8_t v___x_22006__boxed_1496_; uint8_t v___x_22007__boxed_1497_; lean_object* v_res_1498_; 
v___x_22005__boxed_1495_ = lean_unbox(v___x_1481_);
v___x_22006__boxed_1496_ = lean_unbox(v___x_1482_);
v___x_22007__boxed_1497_ = lean_unbox(v___x_1483_);
v_res_1498_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1473_, v_tail_1474_, v_params_1475_, v_numParams_1476_, v_indName_1477_, v_ism1_1478_, v_ism2_1479_, v___x_1480_, v___x_22005__boxed_1495_, v___x_22006__boxed_1496_, v___x_22007__boxed_1497_, v_val_1484_, v___x_1485_, v___x_1486_, v_name_1487_, v___x_1488_, v_motive_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
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
uint8_t v___x_22293__boxed_1724_; lean_object* v_res_1725_; 
v___x_22293__boxed_1724_ = lean_unbox(v___x_1718_);
v_res_1725_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1715_, v_declName_1716_, v_levelParams_1717_, v___x_22293__boxed_1724_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
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
v___x_1825_ = lean_alloc_ctor(0, 11, 0);
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
lean_object* v___x_1864_; lean_object* v_env_1865_; uint8_t v___x_1866_; 
v___x_1864_ = lean_st_ref_get(v___y_1862_);
v_env_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc_ref(v_env_1865_);
lean_dec(v___x_1864_);
v___x_1866_ = l_Lean_Name_isAnonymous(v_declHint_1861_);
if (v___x_1866_ == 0)
{
uint8_t v_isExporting_1867_; 
v_isExporting_1867_ = lean_ctor_get_uint8(v_env_1865_, sizeof(void*)*8);
if (v_isExporting_1867_ == 0)
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
lean_object* v___x_1869_; uint8_t v___x_1870_; 
lean_inc_ref(v_env_1865_);
v___x_1869_ = l_Lean_Environment_setExporting(v_env_1865_, v___x_1866_);
lean_inc(v_declHint_1861_);
lean_inc_ref(v___x_1869_);
v___x_1870_ = l_Lean_Environment_contains(v___x_1869_, v_declHint_1861_, v_isExporting_1867_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; 
lean_dec_ref(v___x_1869_);
lean_dec_ref(v_env_1865_);
lean_dec(v_declHint_1861_);
v___x_1871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1871_, 0, v_msg_1860_);
return v___x_1871_;
}
else
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v_c_1877_; lean_object* v___x_1878_; 
v___x_1872_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1873_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5);
v___x_1874_ = l_Lean_Options_empty;
v___x_1875_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1869_);
lean_ctor_set(v___x_1875_, 1, v___x_1872_);
lean_ctor_set(v___x_1875_, 2, v___x_1873_);
lean_ctor_set(v___x_1875_, 3, v___x_1874_);
lean_inc(v_declHint_1861_);
v___x_1876_ = l_Lean_MessageData_ofConstName(v_declHint_1861_, v___x_1866_);
v_c_1877_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1877_, 0, v___x_1875_);
lean_ctor_set(v_c_1877_, 1, v___x_1876_);
v___x_1878_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1865_, v_declHint_1861_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec_ref(v_env_1865_);
lean_dec(v_declHint_1861_);
v___x_1879_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1879_);
lean_ctor_set(v___x_1880_, 1, v_c_1877_);
v___x_1881_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1880_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = l_Lean_MessageData_note(v___x_1882_);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_msg_1860_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
return v___x_1885_;
}
else
{
lean_object* v_val_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1921_; 
v_val_1886_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1888_ = v___x_1878_;
v_isShared_1889_ = v_isSharedCheck_1921_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_val_1886_);
lean_dec(v___x_1878_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1921_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v_mod_1893_; uint8_t v___x_1894_; 
v___x_1890_ = lean_box(0);
v___x_1891_ = l_Lean_Environment_header(v_env_1865_);
lean_dec_ref(v_env_1865_);
v___x_1892_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1891_);
v_mod_1893_ = lean_array_get(v___x_1890_, v___x_1892_, v_val_1886_);
lean_dec(v_val_1886_);
lean_dec_ref(v___x_1892_);
v___x_1894_ = l_Lean_isPrivateName(v_declHint_1861_);
lean_dec(v_declHint_1861_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1895_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v_c_1877_);
v___x_1897_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = l_Lean_MessageData_ofName(v_mod_1893_);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = l_Lean_MessageData_note(v___x_1902_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v_msg_1860_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1904_);
v___x_1906_ = v___x_1888_;
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
v___x_1908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1908_);
lean_ctor_set(v___x_1909_, 1, v_c_1877_);
v___x_1910_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = l_Lean_MessageData_ofName(v_mod_1893_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_MessageData_note(v___x_1915_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v_msg_1860_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set_tag(v___x_1888_, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1917_);
v___x_1919_ = v___x_1888_;
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
lean_dec_ref(v_env_1865_);
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
v_ref_2008_ = lean_ctor_get(v___y_2005_, 5);
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
lean_object* v___x_2048_; lean_object* v_env_2049_; lean_object* v_nextMacroScope_2050_; lean_object* v_ngen_2051_; lean_object* v_auxDeclNGen_2052_; lean_object* v_traceState_2053_; lean_object* v_messages_2054_; lean_object* v_infoState_2055_; lean_object* v_snapshotTasks_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2085_; 
v___x_2048_ = lean_st_ref_take(v___y_2046_);
v_env_2049_ = lean_ctor_get(v___x_2048_, 0);
v_nextMacroScope_2050_ = lean_ctor_get(v___x_2048_, 1);
v_ngen_2051_ = lean_ctor_get(v___x_2048_, 2);
v_auxDeclNGen_2052_ = lean_ctor_get(v___x_2048_, 3);
v_traceState_2053_ = lean_ctor_get(v___x_2048_, 4);
v_messages_2054_ = lean_ctor_get(v___x_2048_, 6);
v_infoState_2055_ = lean_ctor_get(v___x_2048_, 7);
v_snapshotTasks_2056_ = lean_ctor_get(v___x_2048_, 8);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2048_, 5);
lean_dec(v_unused_2086_);
v___x_2058_ = v___x_2048_;
v_isShared_2059_ = v_isSharedCheck_2085_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_snapshotTasks_2056_);
lean_inc(v_infoState_2055_);
lean_inc(v_messages_2054_);
lean_inc(v_traceState_2053_);
lean_inc(v_auxDeclNGen_2052_);
lean_inc(v_ngen_2051_);
lean_inc(v_nextMacroScope_2050_);
lean_inc(v_env_2049_);
lean_dec(v___x_2048_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2085_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2060_ = 0;
v___x_2061_ = lean_box(0);
v___x_2062_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2049_, v_declName_2043_, v_s_2044_, v___x_2060_, v___x_2061_);
v___x_2063_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 5, v___x_2063_);
lean_ctor_set(v___x_2058_, 0, v___x_2062_);
v___x_2065_ = v___x_2058_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_nextMacroScope_2050_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_ngen_2051_);
lean_ctor_set(v_reuseFailAlloc_2084_, 3, v_auxDeclNGen_2052_);
lean_ctor_set(v_reuseFailAlloc_2084_, 4, v_traceState_2053_);
lean_ctor_set(v_reuseFailAlloc_2084_, 5, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2084_, 6, v_messages_2054_);
lean_ctor_set(v_reuseFailAlloc_2084_, 7, v_infoState_2055_);
lean_ctor_set(v_reuseFailAlloc_2084_, 8, v_snapshotTasks_2056_);
v___x_2065_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v_mctx_2068_; lean_object* v_zetaDeltaFVarIds_2069_; lean_object* v_postponed_2070_; lean_object* v_diag_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2082_; 
v___x_2066_ = lean_st_ref_put(v___y_2046_, v___x_2065_);
v___x_2067_ = lean_st_ref_take(v___y_2045_);
v_mctx_2068_ = lean_ctor_get(v___x_2067_, 0);
v_zetaDeltaFVarIds_2069_ = lean_ctor_get(v___x_2067_, 2);
v_postponed_2070_ = lean_ctor_get(v___x_2067_, 3);
v_diag_2071_ = lean_ctor_get(v___x_2067_, 4);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v___x_2067_, 1);
lean_dec(v_unused_2083_);
v___x_2073_ = v___x_2067_;
v_isShared_2074_ = v_isSharedCheck_2082_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_diag_2071_);
lean_inc(v_postponed_2070_);
lean_inc(v_zetaDeltaFVarIds_2069_);
lean_inc(v_mctx_2068_);
lean_dec(v___x_2067_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2082_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v___x_2075_);
v___x_2077_ = v___x_2073_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_mctx_2068_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2081_, 2, v_zetaDeltaFVarIds_2069_);
lean_ctor_set(v_reuseFailAlloc_2081_, 3, v_postponed_2070_);
lean_ctor_set(v_reuseFailAlloc_2081_, 4, v_diag_2071_);
v___x_2077_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_st_ref_put(v___y_2045_, v___x_2077_);
v___x_2079_ = lean_box(0);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2087_, lean_object* v_s_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
uint8_t v_s_boxed_2092_; lean_object* v_res_2093_; 
v_s_boxed_2092_ = lean_unbox(v_s_2088_);
v_res_2093_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2087_, v_s_boxed_2092_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec(v___y_2089_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = 0;
v___x_2101_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2094_, v___x_2100_, v___y_2096_, v___y_2098_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
return v_res_2108_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2111_ = l_Lean_stringToMessageData(v___x_2110_);
return v___x_2111_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2114_ = l_Lean_stringToMessageData(v___x_2113_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2118_, lean_object* v_declName_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2125_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2126_ = l_Lean_MessageData_ofName(v_attrName_2118_);
v___x_2127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2125_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2129_, 0, v___x_2127_);
lean_ctor_set(v___x_2129_, 1, v___x_2128_);
v___x_2130_ = 0;
v___x_2131_ = l_Lean_MessageData_ofConstName(v_declName_2119_, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2129_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2132_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2134_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2136_, lean_object* v_declName_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2136_, v_declName_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
lean_dec(v___y_2139_);
lean_dec_ref(v___y_2138_);
return v_res_2143_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2146_ = l_Lean_stringToMessageData(v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2149_ = l_Lean_stringToMessageData(v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2150_, lean_object* v_declName_2151_, lean_object* v_asyncPrefix_x3f_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___y_2159_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2152_) == 0)
{
lean_object* v___x_2172_; 
v___x_2172_ = l_Lean_MessageData_nil;
v___y_2159_ = v___x_2172_;
goto v___jp_2158_;
}
else
{
lean_object* v_val_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v_val_2173_ = lean_ctor_get(v_asyncPrefix_x3f_2152_, 0);
lean_inc(v_val_2173_);
lean_dec_ref_known(v_asyncPrefix_x3f_2152_, 1);
v___x_2174_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2175_ = l_Lean_MessageData_ofName(v_val_2173_);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___y_2159_ = v___x_2178_;
goto v___jp_2158_;
}
v___jp_2158_:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2160_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2161_ = l_Lean_MessageData_ofName(v_attrName_2150_);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2160_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
v___x_2163_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = 0;
v___x_2166_ = l_Lean_MessageData_ofConstName(v_declName_2151_, v___x_2165_);
v___x_2167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2164_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v___y_2159_);
v___x_2171_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2170_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
return v___x_2171_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2179_, lean_object* v_declName_2180_, lean_object* v_asyncPrefix_x3f_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2179_, v_declName_2180_, v_asyncPrefix_x3f_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2188_, lean_object* v_decl_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___x_2238_; lean_object* v_env_2239_; lean_object* v___y_2241_; lean_object* v___y_2242_; lean_object* v___y_2243_; lean_object* v___y_2244_; lean_object* v___x_2254_; 
v___x_2238_ = lean_st_ref_get(v___y_2193_);
v_env_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc_ref(v_env_2239_);
lean_dec(v___x_2238_);
v___x_2254_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2239_, v_decl_2189_);
if (lean_obj_tag(v___x_2254_) == 0)
{
v___y_2241_ = v___y_2190_;
v___y_2242_ = v___y_2191_;
v___y_2243_ = v___y_2192_;
v___y_2244_ = v___y_2193_;
goto v___jp_2240_;
}
else
{
lean_object* v_attr_2255_; lean_object* v_toAttributeImplCore_2256_; lean_object* v_name_2257_; lean_object* v___x_2258_; 
lean_dec_ref_known(v___x_2254_, 1);
lean_dec_ref(v_env_2239_);
v_attr_2255_ = lean_ctor_get(v_attr_2188_, 0);
lean_inc_ref(v_attr_2255_);
lean_dec_ref(v_attr_2188_);
v_toAttributeImplCore_2256_ = lean_ctor_get(v_attr_2255_, 0);
lean_inc_ref(v_toAttributeImplCore_2256_);
lean_dec_ref(v_attr_2255_);
v_name_2257_ = lean_ctor_get(v_toAttributeImplCore_2256_, 1);
lean_inc(v_name_2257_);
lean_dec_ref(v_toAttributeImplCore_2256_);
v___x_2258_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2257_, v_decl_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
return v___x_2258_;
}
v___jp_2195_:
{
lean_object* v___x_2198_; lean_object* v_ext_2199_; lean_object* v_toEnvExtension_2200_; lean_object* v_env_2201_; lean_object* v_nextMacroScope_2202_; lean_object* v_ngen_2203_; lean_object* v_auxDeclNGen_2204_; lean_object* v_traceState_2205_; lean_object* v_messages_2206_; lean_object* v_infoState_2207_; lean_object* v_snapshotTasks_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2236_; 
v___x_2198_ = lean_st_ref_take(v___y_2197_);
v_ext_2199_ = lean_ctor_get(v_attr_2188_, 1);
lean_inc_ref(v_ext_2199_);
lean_dec_ref(v_attr_2188_);
v_toEnvExtension_2200_ = lean_ctor_get(v_ext_2199_, 0);
v_env_2201_ = lean_ctor_get(v___x_2198_, 0);
v_nextMacroScope_2202_ = lean_ctor_get(v___x_2198_, 1);
v_ngen_2203_ = lean_ctor_get(v___x_2198_, 2);
v_auxDeclNGen_2204_ = lean_ctor_get(v___x_2198_, 3);
v_traceState_2205_ = lean_ctor_get(v___x_2198_, 4);
v_messages_2206_ = lean_ctor_get(v___x_2198_, 6);
v_infoState_2207_ = lean_ctor_get(v___x_2198_, 7);
v_snapshotTasks_2208_ = lean_ctor_get(v___x_2198_, 8);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2236_ == 0)
{
lean_object* v_unused_2237_; 
v_unused_2237_ = lean_ctor_get(v___x_2198_, 5);
lean_dec(v_unused_2237_);
v___x_2210_ = v___x_2198_;
v_isShared_2211_ = v_isSharedCheck_2236_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_snapshotTasks_2208_);
lean_inc(v_infoState_2207_);
lean_inc(v_messages_2206_);
lean_inc(v_traceState_2205_);
lean_inc(v_auxDeclNGen_2204_);
lean_inc(v_ngen_2203_);
lean_inc(v_nextMacroScope_2202_);
lean_inc(v_env_2201_);
lean_dec(v___x_2198_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2236_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v_asyncMode_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2216_; 
v_asyncMode_2212_ = lean_ctor_get(v_toEnvExtension_2200_, 2);
lean_inc(v_asyncMode_2212_);
lean_inc(v_decl_2189_);
v___x_2213_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2199_, v_env_2201_, v_decl_2189_, v_asyncMode_2212_, v_decl_2189_);
lean_dec(v_asyncMode_2212_);
v___x_2214_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 5, v___x_2214_);
lean_ctor_set(v___x_2210_, 0, v___x_2213_);
v___x_2216_ = v___x_2210_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_nextMacroScope_2202_);
lean_ctor_set(v_reuseFailAlloc_2235_, 2, v_ngen_2203_);
lean_ctor_set(v_reuseFailAlloc_2235_, 3, v_auxDeclNGen_2204_);
lean_ctor_set(v_reuseFailAlloc_2235_, 4, v_traceState_2205_);
lean_ctor_set(v_reuseFailAlloc_2235_, 5, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2235_, 6, v_messages_2206_);
lean_ctor_set(v_reuseFailAlloc_2235_, 7, v_infoState_2207_);
lean_ctor_set(v_reuseFailAlloc_2235_, 8, v_snapshotTasks_2208_);
v___x_2216_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v_mctx_2219_; lean_object* v_zetaDeltaFVarIds_2220_; lean_object* v_postponed_2221_; lean_object* v_diag_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2233_; 
v___x_2217_ = lean_st_ref_put(v___y_2197_, v___x_2216_);
v___x_2218_ = lean_st_ref_take(v___y_2196_);
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
lean_object* v___x_2226_; lean_object* v___x_2228_; 
v___x_2226_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 1, v___x_2226_);
v___x_2228_ = v___x_2224_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_mctx_2219_);
lean_ctor_set(v_reuseFailAlloc_2232_, 1, v___x_2226_);
lean_ctor_set(v_reuseFailAlloc_2232_, 2, v_zetaDeltaFVarIds_2220_);
lean_ctor_set(v_reuseFailAlloc_2232_, 3, v_postponed_2221_);
lean_ctor_set(v_reuseFailAlloc_2232_, 4, v_diag_2222_);
v___x_2228_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2229_ = lean_st_ref_put(v___y_2196_, v___x_2228_);
v___x_2230_ = lean_box(0);
v___x_2231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2231_, 0, v___x_2230_);
return v___x_2231_;
}
}
}
}
}
v___jp_2240_:
{
lean_object* v_ext_2245_; lean_object* v_toEnvExtension_2246_; lean_object* v_attr_2247_; lean_object* v_asyncMode_2248_; uint8_t v___x_2249_; 
v_ext_2245_ = lean_ctor_get(v_attr_2188_, 1);
v_toEnvExtension_2246_ = lean_ctor_get(v_ext_2245_, 0);
v_attr_2247_ = lean_ctor_get(v_attr_2188_, 0);
v_asyncMode_2248_ = lean_ctor_get(v_toEnvExtension_2246_, 2);
lean_inc(v_decl_2189_);
lean_inc_ref(v_env_2239_);
v___x_2249_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2239_, v_decl_2189_, v_asyncMode_2248_);
if (v___x_2249_ == 0)
{
lean_object* v_toAttributeImplCore_2250_; lean_object* v_name_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_inc_ref(v_attr_2247_);
lean_dec_ref(v_attr_2188_);
v_toAttributeImplCore_2250_ = lean_ctor_get(v_attr_2247_, 0);
lean_inc_ref(v_toAttributeImplCore_2250_);
lean_dec_ref(v_attr_2247_);
v_name_2251_ = lean_ctor_get(v_toAttributeImplCore_2250_, 1);
lean_inc(v_name_2251_);
lean_dec_ref(v_toAttributeImplCore_2250_);
v___x_2252_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2239_);
v___x_2253_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2251_, v_decl_2189_, v___x_2252_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_);
return v___x_2253_;
}
else
{
lean_dec_ref(v_env_2239_);
v___y_2196_ = v___y_2242_;
v___y_2197_ = v___y_2244_;
goto v___jp_2195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2259_, lean_object* v_decl_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2259_, v_decl_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___x_2273_; lean_object* v_env_2274_; uint8_t v___x_2275_; lean_object* v___x_2276_; 
v___x_2273_ = lean_st_ref_get(v___y_2271_);
v_env_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc_ref(v_env_2274_);
lean_dec(v___x_2273_);
v___x_2275_ = 0;
lean_inc(v_constName_2267_);
v___x_2276_ = l_Lean_Environment_find_x3f(v_env_2274_, v_constName_2267_, v___x_2275_);
if (lean_obj_tag(v___x_2276_) == 0)
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2277_;
}
else
{
lean_object* v_val_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_dec(v_constName_2267_);
v_val_2278_ = lean_ctor_get(v___x_2276_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2276_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2276_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_val_2278_);
lean_dec(v___x_2276_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set_tag(v___x_2280_, 0);
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_val_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2292_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2296_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2297_ = lean_unsigned_to_nat(58u);
v___x_2298_ = lean_unsigned_to_nat(33u);
v___x_2299_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2300_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2301_ = l_mkPanicMessageWithDecl(v___x_2300_, v___x_2299_, v___x_2298_, v___x_2297_, v___x_2296_);
return v___x_2301_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2303_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2304_ = lean_unsigned_to_nat(60u);
v___x_2305_ = lean_unsigned_to_nat(30u);
v___x_2306_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2307_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2308_ = l_mkPanicMessageWithDecl(v___x_2307_, v___x_2306_, v___x_2305_, v___x_2304_, v___x_2303_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2309_, lean_object* v_indName_2310_, lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v___x_2316_; 
lean_inc(v_indName_2310_);
v___x_2316_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2310_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
if (lean_obj_tag(v_a_2317_) == 5)
{
lean_object* v_val_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2504_; 
v_val_2318_ = lean_ctor_get(v_a_2317_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_a_2317_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2320_ = v_a_2317_;
v_isShared_2321_ = v_isSharedCheck_2504_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_val_2318_);
lean_dec(v_a_2317_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2504_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_inc(v_indName_2310_);
v___x_2322_ = l_Lean_mkCasesOnName(v_indName_2310_);
lean_inc(v___x_2322_);
v___x_2323_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2322_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v_name_2325_; lean_object* v_levelParams_2326_; lean_object* v_type_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v_name_2325_ = lean_ctor_get(v_a_2324_, 0);
lean_inc(v_name_2325_);
v_levelParams_2326_ = lean_ctor_get(v_a_2324_, 1);
lean_inc_n(v_levelParams_2326_, 2);
v_type_2327_ = lean_ctor_get(v_a_2324_, 2);
lean_inc_ref(v_type_2327_);
lean_dec(v_a_2324_);
v___x_2328_ = lean_box(0);
v___x_2329_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2326_, v___x_2328_);
if (lean_obj_tag(v___x_2329_) == 1)
{
lean_object* v_head_2330_; lean_object* v_tail_2331_; lean_object* v_numParams_2332_; lean_object* v_numIndices_2333_; lean_object* v_ctors_2334_; lean_object* v___f_2335_; lean_object* v___x_2337_; 
v_head_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_head_2330_);
v_tail_2331_ = lean_ctor_get(v___x_2329_, 1);
lean_inc(v_tail_2331_);
v_numParams_2332_ = lean_ctor_get(v_val_2318_, 1);
lean_inc_n(v_numParams_2332_, 2);
v_numIndices_2333_ = lean_ctor_get(v_val_2318_, 2);
lean_inc(v_numIndices_2333_);
v_ctors_2334_ = lean_ctor_get(v_val_2318_, 4);
lean_inc(v_ctors_2334_);
v___f_2335_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2335_, 0, v_numIndices_2333_);
lean_closure_set(v___f_2335_, 1, v_head_2330_);
lean_closure_set(v___f_2335_, 2, v_ctors_2334_);
lean_closure_set(v___f_2335_, 3, v_tail_2331_);
lean_closure_set(v___f_2335_, 4, v_numParams_2332_);
lean_closure_set(v___f_2335_, 5, v_indName_2310_);
lean_closure_set(v___f_2335_, 6, v_val_2318_);
lean_closure_set(v___f_2335_, 7, v___x_2329_);
lean_closure_set(v___f_2335_, 8, v___x_2322_);
lean_closure_set(v___f_2335_, 9, v_name_2325_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set_tag(v___x_2320_, 1);
lean_ctor_set(v___x_2320_, 0, v_numParams_2332_);
v___x_2337_ = v___x_2320_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_numParams_2332_);
v___x_2337_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
uint8_t v___x_2338_; lean_object* v___x_2339_; 
v___x_2338_ = 0;
v___x_2339_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2327_, v___x_2337_, v___f_2335_, v___x_2338_, v___x_2338_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; lean_object* v___f_2342_; uint8_t v___y_2344_; uint8_t v___x_2483_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = lean_box(v___x_2338_);
lean_inc(v_declName_2309_);
v___f_2342_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2342_, 0, v_a_2340_);
lean_closure_set(v___f_2342_, 1, v_declName_2309_);
lean_closure_set(v___f_2342_, 2, v_levelParams_2326_);
lean_closure_set(v___f_2342_, 3, v___x_2341_);
v___x_2483_ = l_Lean_isPrivateName(v_declName_2309_);
if (v___x_2483_ == 0)
{
uint8_t v___x_2484_; 
v___x_2484_ = 1;
v___y_2344_ = v___x_2484_;
goto v___jp_2343_;
}
else
{
v___y_2344_ = v___x_2338_;
goto v___jp_2343_;
}
v___jp_2343_:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2342_, v___y_2344_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v___x_2346_; lean_object* v_env_2347_; lean_object* v_nextMacroScope_2348_; lean_object* v_ngen_2349_; lean_object* v_auxDeclNGen_2350_; lean_object* v_traceState_2351_; lean_object* v_messages_2352_; lean_object* v_infoState_2353_; lean_object* v_snapshotTasks_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2481_; 
lean_dec_ref_known(v___x_2345_, 1);
v___x_2346_ = lean_st_ref_take(v_a_2314_);
v_env_2347_ = lean_ctor_get(v___x_2346_, 0);
v_nextMacroScope_2348_ = lean_ctor_get(v___x_2346_, 1);
v_ngen_2349_ = lean_ctor_get(v___x_2346_, 2);
v_auxDeclNGen_2350_ = lean_ctor_get(v___x_2346_, 3);
v_traceState_2351_ = lean_ctor_get(v___x_2346_, 4);
v_messages_2352_ = lean_ctor_get(v___x_2346_, 6);
v_infoState_2353_ = lean_ctor_get(v___x_2346_, 7);
v_snapshotTasks_2354_ = lean_ctor_get(v___x_2346_, 8);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; 
v_unused_2482_ = lean_ctor_get(v___x_2346_, 5);
lean_dec(v_unused_2482_);
v___x_2356_ = v___x_2346_;
v_isShared_2357_ = v_isSharedCheck_2481_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_snapshotTasks_2354_);
lean_inc(v_infoState_2353_);
lean_inc(v_messages_2352_);
lean_inc(v_traceState_2351_);
lean_inc(v_auxDeclNGen_2350_);
lean_inc(v_ngen_2349_);
lean_inc(v_nextMacroScope_2348_);
lean_inc(v_env_2347_);
lean_dec(v___x_2346_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2481_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
lean_inc(v_declName_2309_);
v___x_2358_ = l_Lean_Meta_markMatcherLike(v_env_2347_, v_declName_2309_);
v___x_2359_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2357_ == 0)
{
lean_ctor_set(v___x_2356_, 5, v___x_2359_);
lean_ctor_set(v___x_2356_, 0, v___x_2358_);
v___x_2361_ = v___x_2356_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_nextMacroScope_2348_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v_ngen_2349_);
lean_ctor_set(v_reuseFailAlloc_2480_, 3, v_auxDeclNGen_2350_);
lean_ctor_set(v_reuseFailAlloc_2480_, 4, v_traceState_2351_);
lean_ctor_set(v_reuseFailAlloc_2480_, 5, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2480_, 6, v_messages_2352_);
lean_ctor_set(v_reuseFailAlloc_2480_, 7, v_infoState_2353_);
lean_ctor_set(v_reuseFailAlloc_2480_, 8, v_snapshotTasks_2354_);
v___x_2361_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v_mctx_2364_; lean_object* v_zetaDeltaFVarIds_2365_; lean_object* v_postponed_2366_; lean_object* v_diag_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2478_; 
v___x_2362_ = lean_st_ref_put(v_a_2314_, v___x_2361_);
v___x_2363_ = lean_st_ref_take(v_a_2312_);
v_mctx_2364_ = lean_ctor_get(v___x_2363_, 0);
v_zetaDeltaFVarIds_2365_ = lean_ctor_get(v___x_2363_, 2);
v_postponed_2366_ = lean_ctor_get(v___x_2363_, 3);
v_diag_2367_ = lean_ctor_get(v___x_2363_, 4);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v___x_2363_, 1);
lean_dec(v_unused_2479_);
v___x_2369_ = v___x_2363_;
v_isShared_2370_ = v_isSharedCheck_2478_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_diag_2367_);
lean_inc(v_postponed_2366_);
lean_inc(v_zetaDeltaFVarIds_2365_);
lean_inc(v_mctx_2364_);
lean_dec(v___x_2363_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2478_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2371_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 1, v___x_2371_);
v___x_2373_ = v___x_2369_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_mctx_2364_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2477_, 2, v_zetaDeltaFVarIds_2365_);
lean_ctor_set(v_reuseFailAlloc_2477_, 3, v_postponed_2366_);
lean_ctor_set(v_reuseFailAlloc_2477_, 4, v_diag_2367_);
v___x_2373_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v_env_2376_; lean_object* v_nextMacroScope_2377_; lean_object* v_ngen_2378_; lean_object* v_auxDeclNGen_2379_; lean_object* v_traceState_2380_; lean_object* v_messages_2381_; lean_object* v_infoState_2382_; lean_object* v_snapshotTasks_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2475_; 
v___x_2374_ = lean_st_ref_put(v_a_2312_, v___x_2373_);
v___x_2375_ = lean_st_ref_take(v_a_2314_);
v_env_2376_ = lean_ctor_get(v___x_2375_, 0);
v_nextMacroScope_2377_ = lean_ctor_get(v___x_2375_, 1);
v_ngen_2378_ = lean_ctor_get(v___x_2375_, 2);
v_auxDeclNGen_2379_ = lean_ctor_get(v___x_2375_, 3);
v_traceState_2380_ = lean_ctor_get(v___x_2375_, 4);
v_messages_2381_ = lean_ctor_get(v___x_2375_, 6);
v_infoState_2382_ = lean_ctor_get(v___x_2375_, 7);
v_snapshotTasks_2383_ = lean_ctor_get(v___x_2375_, 8);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v___x_2375_, 5);
lean_dec(v_unused_2476_);
v___x_2385_ = v___x_2375_;
v_isShared_2386_ = v_isSharedCheck_2475_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_snapshotTasks_2383_);
lean_inc(v_infoState_2382_);
lean_inc(v_messages_2381_);
lean_inc(v_traceState_2380_);
lean_inc(v_auxDeclNGen_2379_);
lean_inc(v_ngen_2378_);
lean_inc(v_nextMacroScope_2377_);
lean_inc(v_env_2376_);
lean_dec(v___x_2375_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2475_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2387_; lean_object* v___x_2389_; 
lean_inc(v_declName_2309_);
v___x_2387_ = l_Lean_markAuxRecursor(v_env_2376_, v_declName_2309_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set(v___x_2385_, 5, v___x_2359_);
lean_ctor_set(v___x_2385_, 0, v___x_2387_);
v___x_2389_ = v___x_2385_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2474_, 1, v_nextMacroScope_2377_);
lean_ctor_set(v_reuseFailAlloc_2474_, 2, v_ngen_2378_);
lean_ctor_set(v_reuseFailAlloc_2474_, 3, v_auxDeclNGen_2379_);
lean_ctor_set(v_reuseFailAlloc_2474_, 4, v_traceState_2380_);
lean_ctor_set(v_reuseFailAlloc_2474_, 5, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2474_, 6, v_messages_2381_);
lean_ctor_set(v_reuseFailAlloc_2474_, 7, v_infoState_2382_);
lean_ctor_set(v_reuseFailAlloc_2474_, 8, v_snapshotTasks_2383_);
v___x_2389_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v_mctx_2392_; lean_object* v_zetaDeltaFVarIds_2393_; lean_object* v_postponed_2394_; lean_object* v_diag_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2472_; 
v___x_2390_ = lean_st_ref_put(v_a_2314_, v___x_2389_);
v___x_2391_ = lean_st_ref_take(v_a_2312_);
v_mctx_2392_ = lean_ctor_get(v___x_2391_, 0);
v_zetaDeltaFVarIds_2393_ = lean_ctor_get(v___x_2391_, 2);
v_postponed_2394_ = lean_ctor_get(v___x_2391_, 3);
v_diag_2395_ = lean_ctor_get(v___x_2391_, 4);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2472_ == 0)
{
lean_object* v_unused_2473_; 
v_unused_2473_ = lean_ctor_get(v___x_2391_, 1);
lean_dec(v_unused_2473_);
v___x_2397_ = v___x_2391_;
v_isShared_2398_ = v_isSharedCheck_2472_;
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
v_isShared_2398_ = v_isSharedCheck_2472_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 1, v___x_2371_);
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_mctx_2392_);
lean_ctor_set(v_reuseFailAlloc_2471_, 1, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2471_, 2, v_zetaDeltaFVarIds_2393_);
lean_ctor_set(v_reuseFailAlloc_2471_, 3, v_postponed_2394_);
lean_ctor_set(v_reuseFailAlloc_2471_, 4, v_diag_2395_);
v___x_2400_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v_env_2403_; lean_object* v_nextMacroScope_2404_; lean_object* v_ngen_2405_; lean_object* v_auxDeclNGen_2406_; lean_object* v_traceState_2407_; lean_object* v_messages_2408_; lean_object* v_infoState_2409_; lean_object* v_snapshotTasks_2410_; lean_object* v___x_2412_; uint8_t v_isShared_2413_; uint8_t v_isSharedCheck_2469_; 
v___x_2401_ = lean_st_ref_put(v_a_2312_, v___x_2400_);
v___x_2402_ = lean_st_ref_take(v_a_2314_);
v_env_2403_ = lean_ctor_get(v___x_2402_, 0);
v_nextMacroScope_2404_ = lean_ctor_get(v___x_2402_, 1);
v_ngen_2405_ = lean_ctor_get(v___x_2402_, 2);
v_auxDeclNGen_2406_ = lean_ctor_get(v___x_2402_, 3);
v_traceState_2407_ = lean_ctor_get(v___x_2402_, 4);
v_messages_2408_ = lean_ctor_get(v___x_2402_, 6);
v_infoState_2409_ = lean_ctor_get(v___x_2402_, 7);
v_snapshotTasks_2410_ = lean_ctor_get(v___x_2402_, 8);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2402_);
if (v_isSharedCheck_2469_ == 0)
{
lean_object* v_unused_2470_; 
v_unused_2470_ = lean_ctor_get(v___x_2402_, 5);
lean_dec(v_unused_2470_);
v___x_2412_ = v___x_2402_;
v_isShared_2413_ = v_isSharedCheck_2469_;
goto v_resetjp_2411_;
}
else
{
lean_inc(v_snapshotTasks_2410_);
lean_inc(v_infoState_2409_);
lean_inc(v_messages_2408_);
lean_inc(v_traceState_2407_);
lean_inc(v_auxDeclNGen_2406_);
lean_inc(v_ngen_2405_);
lean_inc(v_nextMacroScope_2404_);
lean_inc(v_env_2403_);
lean_dec(v___x_2402_);
v___x_2412_ = lean_box(0);
v_isShared_2413_ = v_isSharedCheck_2469_;
goto v_resetjp_2411_;
}
v_resetjp_2411_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
lean_inc(v_declName_2309_);
v___x_2414_ = l_Lean_Meta_addToCompletionBlackList(v_env_2403_, v_declName_2309_);
if (v_isShared_2413_ == 0)
{
lean_ctor_set(v___x_2412_, 5, v___x_2359_);
lean_ctor_set(v___x_2412_, 0, v___x_2414_);
v___x_2416_ = v___x_2412_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_nextMacroScope_2404_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_ngen_2405_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_auxDeclNGen_2406_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v_traceState_2407_);
lean_ctor_set(v_reuseFailAlloc_2468_, 5, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2468_, 6, v_messages_2408_);
lean_ctor_set(v_reuseFailAlloc_2468_, 7, v_infoState_2409_);
lean_ctor_set(v_reuseFailAlloc_2468_, 8, v_snapshotTasks_2410_);
v___x_2416_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v_mctx_2419_; lean_object* v_zetaDeltaFVarIds_2420_; lean_object* v_postponed_2421_; lean_object* v_diag_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2466_; 
v___x_2417_ = lean_st_ref_put(v_a_2314_, v___x_2416_);
v___x_2418_ = lean_st_ref_take(v_a_2312_);
v_mctx_2419_ = lean_ctor_get(v___x_2418_, 0);
v_zetaDeltaFVarIds_2420_ = lean_ctor_get(v___x_2418_, 2);
v_postponed_2421_ = lean_ctor_get(v___x_2418_, 3);
v_diag_2422_ = lean_ctor_get(v___x_2418_, 4);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2466_ == 0)
{
lean_object* v_unused_2467_; 
v_unused_2467_ = lean_ctor_get(v___x_2418_, 1);
lean_dec(v_unused_2467_);
v___x_2424_ = v___x_2418_;
v_isShared_2425_ = v_isSharedCheck_2466_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_diag_2422_);
lean_inc(v_postponed_2421_);
lean_inc(v_zetaDeltaFVarIds_2420_);
lean_inc(v_mctx_2419_);
lean_dec(v___x_2418_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2466_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 1, v___x_2371_);
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_mctx_2419_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_zetaDeltaFVarIds_2420_);
lean_ctor_set(v_reuseFailAlloc_2465_, 3, v_postponed_2421_);
lean_ctor_set(v_reuseFailAlloc_2465_, 4, v_diag_2422_);
v___x_2427_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_env_2430_; lean_object* v_nextMacroScope_2431_; lean_object* v_ngen_2432_; lean_object* v_auxDeclNGen_2433_; lean_object* v_traceState_2434_; lean_object* v_messages_2435_; lean_object* v_infoState_2436_; lean_object* v_snapshotTasks_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2463_; 
v___x_2428_ = lean_st_ref_put(v_a_2312_, v___x_2427_);
v___x_2429_ = lean_st_ref_take(v_a_2314_);
v_env_2430_ = lean_ctor_get(v___x_2429_, 0);
v_nextMacroScope_2431_ = lean_ctor_get(v___x_2429_, 1);
v_ngen_2432_ = lean_ctor_get(v___x_2429_, 2);
v_auxDeclNGen_2433_ = lean_ctor_get(v___x_2429_, 3);
v_traceState_2434_ = lean_ctor_get(v___x_2429_, 4);
v_messages_2435_ = lean_ctor_get(v___x_2429_, 6);
v_infoState_2436_ = lean_ctor_get(v___x_2429_, 7);
v_snapshotTasks_2437_ = lean_ctor_get(v___x_2429_, 8);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v___x_2429_, 5);
lean_dec(v_unused_2464_);
v___x_2439_ = v___x_2429_;
v_isShared_2440_ = v_isSharedCheck_2463_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_snapshotTasks_2437_);
lean_inc(v_infoState_2436_);
lean_inc(v_messages_2435_);
lean_inc(v_traceState_2434_);
lean_inc(v_auxDeclNGen_2433_);
lean_inc(v_ngen_2432_);
lean_inc(v_nextMacroScope_2431_);
lean_inc(v_env_2430_);
lean_dec(v___x_2429_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2463_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
lean_inc(v_declName_2309_);
v___x_2441_ = l_Lean_addProtected(v_env_2430_, v_declName_2309_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 5, v___x_2359_);
lean_ctor_set(v___x_2439_, 0, v___x_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2441_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_nextMacroScope_2431_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_ngen_2432_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v_auxDeclNGen_2433_);
lean_ctor_set(v_reuseFailAlloc_2462_, 4, v_traceState_2434_);
lean_ctor_set(v_reuseFailAlloc_2462_, 5, v___x_2359_);
lean_ctor_set(v_reuseFailAlloc_2462_, 6, v_messages_2435_);
lean_ctor_set(v_reuseFailAlloc_2462_, 7, v_infoState_2436_);
lean_ctor_set(v_reuseFailAlloc_2462_, 8, v_snapshotTasks_2437_);
v___x_2443_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v_mctx_2446_; lean_object* v_zetaDeltaFVarIds_2447_; lean_object* v_postponed_2448_; lean_object* v_diag_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2460_; 
v___x_2444_ = lean_st_ref_put(v_a_2314_, v___x_2443_);
v___x_2445_ = lean_st_ref_take(v_a_2312_);
v_mctx_2446_ = lean_ctor_get(v___x_2445_, 0);
v_zetaDeltaFVarIds_2447_ = lean_ctor_get(v___x_2445_, 2);
v_postponed_2448_ = lean_ctor_get(v___x_2445_, 3);
v_diag_2449_ = lean_ctor_get(v___x_2445_, 4);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2460_ == 0)
{
lean_object* v_unused_2461_; 
v_unused_2461_ = lean_ctor_get(v___x_2445_, 1);
lean_dec(v_unused_2461_);
v___x_2451_ = v___x_2445_;
v_isShared_2452_ = v_isSharedCheck_2460_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_diag_2449_);
lean_inc(v_postponed_2448_);
lean_inc(v_zetaDeltaFVarIds_2447_);
lean_inc(v_mctx_2446_);
lean_dec(v___x_2445_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2460_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v___x_2371_);
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_mctx_2446_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_zetaDeltaFVarIds_2447_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_postponed_2448_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v_diag_2449_);
v___x_2454_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = lean_st_ref_put(v_a_2312_, v___x_2454_);
v___x_2456_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2309_);
v___x_2457_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2456_, v_declName_2309_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v___x_2458_; 
lean_dec_ref_known(v___x_2457_, 1);
v___x_2458_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2309_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
return v___x_2458_;
}
else
{
lean_dec(v_declName_2309_);
return v___x_2457_;
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
lean_dec(v_declName_2309_);
return v___x_2345_;
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_levelParams_2326_);
lean_dec(v_declName_2309_);
v_a_2485_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2339_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2339_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
else
{
lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_dec(v___x_2329_);
lean_dec_ref(v_type_2327_);
lean_dec(v_levelParams_2326_);
lean_dec(v_name_2325_);
lean_dec(v___x_2322_);
lean_del_object(v___x_2320_);
lean_dec_ref(v_val_2318_);
lean_dec(v_indName_2310_);
lean_dec(v_declName_2309_);
v___x_2494_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2495_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2494_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
return v___x_2495_;
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v___x_2322_);
lean_del_object(v___x_2320_);
lean_dec_ref(v_val_2318_);
lean_dec(v_indName_2310_);
lean_dec(v_declName_2309_);
v_a_2496_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2323_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2323_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
lean_dec(v_a_2317_);
lean_dec(v_indName_2310_);
lean_dec(v_declName_2309_);
v___x_2505_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2506_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2505_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
return v___x_2506_;
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_dec(v_indName_2310_);
lean_dec(v_declName_2309_);
v_a_2507_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2316_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2316_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2515_, lean_object* v_indName_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_, lean_object* v_a_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2515_, v_indName_2516_, v_a_2517_, v_a_2518_, v_a_2519_, v_a_2520_);
lean_dec(v_a_2520_);
lean_dec_ref(v_a_2519_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2523_, lean_object* v_name_2524_, lean_object* v_type_2525_, lean_object* v_k_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v___x_2532_; 
v___x_2532_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2524_, v_type_2525_, v_k_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2533_, lean_object* v_name_2534_, lean_object* v_type_2535_, lean_object* v_k_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2533_, v_name_2534_, v_type_2535_, v_k_2536_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_);
lean_dec(v___y_2540_);
lean_dec_ref(v___y_2539_);
lean_dec(v___y_2538_);
lean_dec_ref(v___y_2537_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2543_, lean_object* v_params_2544_, lean_object* v_alts_2545_, lean_object* v___x_2546_, lean_object* v_ism2_2547_, lean_object* v_motive_2548_, lean_object* v_val_2549_, lean_object* v_indName_2550_, lean_object* v___x_2551_, lean_object* v___x_2552_, lean_object* v___x_2553_, lean_object* v_as_2554_, size_t v_sz_2555_, size_t v_i_2556_, lean_object* v_bs_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2543_, v_params_2544_, v_alts_2545_, v___x_2546_, v_ism2_2547_, v_motive_2548_, v_val_2549_, v_indName_2550_, v___x_2551_, v___x_2552_, v___x_2553_, v_sz_2555_, v_i_2556_, v_bs_2557_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2564_ = _args[0];
lean_object* v_params_2565_ = _args[1];
lean_object* v_alts_2566_ = _args[2];
lean_object* v___x_2567_ = _args[3];
lean_object* v_ism2_2568_ = _args[4];
lean_object* v_motive_2569_ = _args[5];
lean_object* v_val_2570_ = _args[6];
lean_object* v_indName_2571_ = _args[7];
lean_object* v___x_2572_ = _args[8];
lean_object* v___x_2573_ = _args[9];
lean_object* v___x_2574_ = _args[10];
lean_object* v_as_2575_ = _args[11];
lean_object* v_sz_2576_ = _args[12];
lean_object* v_i_2577_ = _args[13];
lean_object* v_bs_2578_ = _args[14];
lean_object* v___y_2579_ = _args[15];
lean_object* v___y_2580_ = _args[16];
lean_object* v___y_2581_ = _args[17];
lean_object* v___y_2582_ = _args[18];
lean_object* v___y_2583_ = _args[19];
_start:
{
size_t v_sz_boxed_2584_; size_t v_i_boxed_2585_; lean_object* v_res_2586_; 
v_sz_boxed_2584_ = lean_unbox_usize(v_sz_2576_);
lean_dec(v_sz_2576_);
v_i_boxed_2585_ = lean_unbox_usize(v_i_2577_);
lean_dec(v_i_2577_);
v_res_2586_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2564_, v_params_2565_, v_alts_2566_, v___x_2567_, v_ism2_2568_, v_motive_2569_, v_val_2570_, v_indName_2571_, v___x_2572_, v___x_2573_, v___x_2574_, v_as_2575_, v_sz_boxed_2584_, v_i_boxed_2585_, v_bs_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec_ref(v_as_2575_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2587_, lean_object* v_params_2588_, lean_object* v___x_2589_, lean_object* v_motive_2590_, lean_object* v_as_2591_, size_t v_sz_2592_, size_t v_i_2593_, lean_object* v_bs_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2587_, v_params_2588_, v___x_2589_, v_motive_2590_, v_sz_2592_, v_i_2593_, v_bs_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2601_, lean_object* v_params_2602_, lean_object* v___x_2603_, lean_object* v_motive_2604_, lean_object* v_as_2605_, lean_object* v_sz_2606_, lean_object* v_i_2607_, lean_object* v_bs_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_){
_start:
{
size_t v_sz_boxed_2614_; size_t v_i_boxed_2615_; lean_object* v_res_2616_; 
v_sz_boxed_2614_ = lean_unbox_usize(v_sz_2606_);
lean_dec(v_sz_2606_);
v_i_boxed_2615_ = lean_unbox_usize(v_i_2607_);
lean_dec(v_i_2607_);
v_res_2616_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2601_, v_params_2602_, v___x_2603_, v_motive_2604_, v_as_2605_, v_sz_boxed_2614_, v_i_boxed_2615_, v_bs_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec(v___y_2612_);
lean_dec_ref(v___y_2611_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec_ref(v_as_2605_);
lean_dec_ref(v_params_2602_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2617_, uint8_t v_s_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2617_, v_s_2618_, v___y_2620_, v___y_2622_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2625_, lean_object* v_s_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v_s_boxed_2632_; lean_object* v_res_2633_; 
v_s_boxed_2632_ = lean_unbox(v_s_2626_);
v_res_2633_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2625_, v_s_boxed_2632_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2634_, lean_object* v_constName_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2642_, lean_object* v_constName_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2642_, v_constName_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
lean_dec_ref(v___y_2644_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2650_, lean_object* v_attrName_2651_, lean_object* v_declName_2652_, lean_object* v_asyncPrefix_x3f_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2651_, v_declName_2652_, v_asyncPrefix_x3f_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2660_, lean_object* v_attrName_2661_, lean_object* v_declName_2662_, lean_object* v_asyncPrefix_x3f_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2660_, v_attrName_2661_, v_declName_2662_, v_asyncPrefix_x3f_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2670_, lean_object* v_attrName_2671_, lean_object* v_declName_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2671_, v_declName_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2679_, lean_object* v_attrName_2680_, lean_object* v_declName_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2679_, v_attrName_2680_, v_declName_2681_, v___y_2682_, v___y_2683_, v___y_2684_, v___y_2685_);
lean_dec(v___y_2685_);
lean_dec_ref(v___y_2684_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2688_, lean_object* v_ref_2689_, lean_object* v_constName_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2689_, v_constName_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2697_, lean_object* v_ref_2698_, lean_object* v_constName_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2697_, v_ref_2698_, v_constName_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v_ref_2698_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2706_, lean_object* v_msg_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_msg_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2714_, v_msg_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2722_, lean_object* v_ref_2723_, lean_object* v_msg_2724_, lean_object* v_declHint_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2723_, v_msg_2724_, v_declHint_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2732_, lean_object* v_ref_2733_, lean_object* v_msg_2734_, lean_object* v_declHint_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2732_, v_ref_2733_, v_msg_2734_, v_declHint_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v_ref_2733_);
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2742_, lean_object* v_declHint_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2742_, v_declHint_2743_, v___y_2747_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2750_, lean_object* v_declHint_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2750_, v_declHint_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2758_, lean_object* v_ref_2759_, lean_object* v_msg_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2759_, v_msg_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2767_, lean_object* v_ref_2768_, lean_object* v_msg_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2767_, v_ref_2768_, v_msg_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v_ref_2768_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2776_, lean_object* v___y_2777_){
_start:
{
uint8_t v___x_2779_; 
v___x_2779_ = l_Lean_Expr_hasMVar(v_e_2776_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2780_, 0, v_e_2776_);
return v___x_2780_;
}
else
{
lean_object* v___x_2781_; lean_object* v_mctx_2782_; lean_object* v___x_2783_; lean_object* v_fst_2784_; lean_object* v_snd_2785_; lean_object* v___x_2786_; lean_object* v_cache_2787_; lean_object* v_zetaDeltaFVarIds_2788_; lean_object* v_postponed_2789_; lean_object* v_diag_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2799_; 
v___x_2781_ = lean_st_ref_get(v___y_2777_);
v_mctx_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc_ref(v_mctx_2782_);
lean_dec(v___x_2781_);
v___x_2783_ = l_Lean_instantiateMVarsCore(v_mctx_2782_, v_e_2776_);
v_fst_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_fst_2784_);
v_snd_2785_ = lean_ctor_get(v___x_2783_, 1);
lean_inc(v_snd_2785_);
lean_dec_ref(v___x_2783_);
v___x_2786_ = lean_st_ref_take(v___y_2777_);
v_cache_2787_ = lean_ctor_get(v___x_2786_, 1);
v_zetaDeltaFVarIds_2788_ = lean_ctor_get(v___x_2786_, 2);
v_postponed_2789_ = lean_ctor_get(v___x_2786_, 3);
v_diag_2790_ = lean_ctor_get(v___x_2786_, 4);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2786_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v___x_2786_, 0);
lean_dec(v_unused_2800_);
v___x_2792_ = v___x_2786_;
v_isShared_2793_ = v_isSharedCheck_2799_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_diag_2790_);
lean_inc(v_postponed_2789_);
lean_inc(v_zetaDeltaFVarIds_2788_);
lean_inc(v_cache_2787_);
lean_dec(v___x_2786_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2799_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v_snd_2785_);
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_snd_2785_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_cache_2787_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_zetaDeltaFVarIds_2788_);
lean_ctor_set(v_reuseFailAlloc_2798_, 3, v_postponed_2789_);
lean_ctor_set(v_reuseFailAlloc_2798_, 4, v_diag_2790_);
v___x_2795_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_st_ref_put(v___y_2777_, v___x_2795_);
v___x_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2797_, 0, v_fst_2784_);
return v___x_2797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2801_, v___y_2802_);
lean_dec(v___y_2802_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2805_, v___y_2807_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2819_, lean_object* v_info_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; lean_object* v_env_2825_; lean_object* v_nextMacroScope_2826_; lean_object* v_ngen_2827_; lean_object* v_auxDeclNGen_2828_; lean_object* v_traceState_2829_; lean_object* v_messages_2830_; lean_object* v_infoState_2831_; lean_object* v_snapshotTasks_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2859_; 
v___x_2824_ = lean_st_ref_take(v___y_2822_);
v_env_2825_ = lean_ctor_get(v___x_2824_, 0);
v_nextMacroScope_2826_ = lean_ctor_get(v___x_2824_, 1);
v_ngen_2827_ = lean_ctor_get(v___x_2824_, 2);
v_auxDeclNGen_2828_ = lean_ctor_get(v___x_2824_, 3);
v_traceState_2829_ = lean_ctor_get(v___x_2824_, 4);
v_messages_2830_ = lean_ctor_get(v___x_2824_, 6);
v_infoState_2831_ = lean_ctor_get(v___x_2824_, 7);
v_snapshotTasks_2832_ = lean_ctor_get(v___x_2824_, 8);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2859_ == 0)
{
lean_object* v_unused_2860_; 
v_unused_2860_ = lean_ctor_get(v___x_2824_, 5);
lean_dec(v_unused_2860_);
v___x_2834_ = v___x_2824_;
v_isShared_2835_ = v_isSharedCheck_2859_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_snapshotTasks_2832_);
lean_inc(v_infoState_2831_);
lean_inc(v_messages_2830_);
lean_inc(v_traceState_2829_);
lean_inc(v_auxDeclNGen_2828_);
lean_inc(v_ngen_2827_);
lean_inc(v_nextMacroScope_2826_);
lean_inc(v_env_2825_);
lean_dec(v___x_2824_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2859_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2836_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2825_, v_matcherName_2819_, v_info_2820_);
v___x_2837_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 5, v___x_2837_);
lean_ctor_set(v___x_2834_, 0, v___x_2836_);
v___x_2839_ = v___x_2834_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_nextMacroScope_2826_);
lean_ctor_set(v_reuseFailAlloc_2858_, 2, v_ngen_2827_);
lean_ctor_set(v_reuseFailAlloc_2858_, 3, v_auxDeclNGen_2828_);
lean_ctor_set(v_reuseFailAlloc_2858_, 4, v_traceState_2829_);
lean_ctor_set(v_reuseFailAlloc_2858_, 5, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2858_, 6, v_messages_2830_);
lean_ctor_set(v_reuseFailAlloc_2858_, 7, v_infoState_2831_);
lean_ctor_set(v_reuseFailAlloc_2858_, 8, v_snapshotTasks_2832_);
v___x_2839_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v_mctx_2842_; lean_object* v_zetaDeltaFVarIds_2843_; lean_object* v_postponed_2844_; lean_object* v_diag_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2856_; 
v___x_2840_ = lean_st_ref_put(v___y_2822_, v___x_2839_);
v___x_2841_ = lean_st_ref_take(v___y_2821_);
v_mctx_2842_ = lean_ctor_get(v___x_2841_, 0);
v_zetaDeltaFVarIds_2843_ = lean_ctor_get(v___x_2841_, 2);
v_postponed_2844_ = lean_ctor_get(v___x_2841_, 3);
v_diag_2845_ = lean_ctor_get(v___x_2841_, 4);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v___x_2841_, 1);
lean_dec(v_unused_2857_);
v___x_2847_ = v___x_2841_;
v_isShared_2848_ = v_isSharedCheck_2856_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_diag_2845_);
lean_inc(v_postponed_2844_);
lean_inc(v_zetaDeltaFVarIds_2843_);
lean_inc(v_mctx_2842_);
lean_dec(v___x_2841_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2856_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2849_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 1, v___x_2849_);
v___x_2851_ = v___x_2847_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_mctx_2842_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v___x_2849_);
lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_zetaDeltaFVarIds_2843_);
lean_ctor_set(v_reuseFailAlloc_2855_, 3, v_postponed_2844_);
lean_ctor_set(v_reuseFailAlloc_2855_, 4, v_diag_2845_);
v___x_2851_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2852_ = lean_st_ref_put(v___y_2821_, v___x_2851_);
v___x_2853_ = lean_box(0);
v___x_2854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
return v___x_2854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2861_, lean_object* v_info_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2861_, v_info_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec(v___y_2863_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2867_, lean_object* v_info_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2867_, v_info_2868_, v___y_2870_, v___y_2872_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2875_, lean_object* v_info_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2875_, v_info_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2883_, lean_object* v___x_2884_, lean_object* v_newEqs1_2885_, uint8_t v___x_2886_, uint8_t v___x_2887_, uint8_t v___x_2888_, lean_object* v_ism1_x27_2889_, lean_object* v_ism2_x27_2890_, lean_object* v_newRefls1_2891_, lean_object* v_newEqs2_2892_, lean_object* v_newRefls2_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = l_Lean_mkAppN(v_motive_2883_, v___x_2884_);
v___x_2900_ = l_Array_append___redArg(v_newEqs1_2885_, v_newEqs2_2892_);
v___x_2901_ = l_Lean_Meta_mkForallFVars(v___x_2900_, v___x_2899_, v___x_2886_, v___x_2887_, v___x_2887_, v___x_2888_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec_ref(v___x_2900_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref_known(v___x_2901_, 1);
v___x_2903_ = l_Array_append___redArg(v_ism1_x27_2889_, v_ism2_x27_2890_);
v___x_2904_ = l_Lean_Meta_mkLambdaFVars(v___x_2903_, v_a_2902_, v___x_2886_, v___x_2887_, v___x_2886_, v___x_2887_, v___x_2888_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec_ref(v___x_2903_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2914_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2907_ = v___x_2904_;
v_isShared_2908_ = v_isSharedCheck_2914_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2904_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2914_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v___x_2909_ = l_Array_append___redArg(v_newRefls1_2891_, v_newRefls2_2893_);
v___x_2910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2910_, 0, v_a_2905_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
if (v_isShared_2908_ == 0)
{
lean_ctor_set(v___x_2907_, 0, v___x_2910_);
v___x_2912_ = v___x_2907_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2910_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
else
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
lean_dec_ref(v_newRefls1_2891_);
v_a_2915_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2904_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2904_);
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
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec_ref(v_newRefls1_2891_);
lean_dec_ref(v_ism1_x27_2889_);
v_a_2923_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2901_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2901_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2931_, lean_object* v___x_2932_, lean_object* v_newEqs1_2933_, lean_object* v___x_2934_, lean_object* v___x_2935_, lean_object* v___x_2936_, lean_object* v_ism1_x27_2937_, lean_object* v_ism2_x27_2938_, lean_object* v_newRefls1_2939_, lean_object* v_newEqs2_2940_, lean_object* v_newRefls2_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v___x_14914__boxed_2947_; uint8_t v___x_14915__boxed_2948_; uint8_t v___x_14916__boxed_2949_; lean_object* v_res_2950_; 
v___x_14914__boxed_2947_ = lean_unbox(v___x_2934_);
v___x_14915__boxed_2948_ = lean_unbox(v___x_2935_);
v___x_14916__boxed_2949_ = lean_unbox(v___x_2936_);
v_res_2950_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2931_, v___x_2932_, v_newEqs1_2933_, v___x_14914__boxed_2947_, v___x_14915__boxed_2948_, v___x_14916__boxed_2949_, v_ism1_x27_2937_, v_ism2_x27_2938_, v_newRefls1_2939_, v_newEqs2_2940_, v_newRefls2_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec_ref(v_newRefls2_2941_);
lean_dec_ref(v_newEqs2_2940_);
lean_dec_ref(v_ism2_x27_2938_);
lean_dec_ref(v___x_2932_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2951_, lean_object* v___x_2952_, uint8_t v___x_2953_, uint8_t v___x_2954_, uint8_t v___x_2955_, lean_object* v_ism1_x27_2956_, lean_object* v_ism2_x27_2957_, lean_object* v_is_2958_, lean_object* v___x_2959_, lean_object* v_newEqs1_2960_, lean_object* v_newRefls1_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___f_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2967_ = lean_box(v___x_2953_);
v___x_2968_ = lean_box(v___x_2954_);
v___x_2969_ = lean_box(v___x_2955_);
lean_inc_ref(v_ism2_x27_2957_);
v___f_2970_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2970_, 0, v_motive_2951_);
lean_closure_set(v___f_2970_, 1, v___x_2952_);
lean_closure_set(v___f_2970_, 2, v_newEqs1_2960_);
lean_closure_set(v___f_2970_, 3, v___x_2967_);
lean_closure_set(v___f_2970_, 4, v___x_2968_);
lean_closure_set(v___f_2970_, 5, v___x_2969_);
lean_closure_set(v___f_2970_, 6, v_ism1_x27_2956_);
lean_closure_set(v___f_2970_, 7, v_ism2_x27_2957_);
lean_closure_set(v___f_2970_, 8, v_newRefls1_2961_);
v___x_2971_ = lean_array_push(v_is_2958_, v___x_2959_);
v___x_2972_ = l_Lean_Meta_withNewEqs___redArg(v___x_2971_, v_ism2_x27_2957_, v___f_2970_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2973_, lean_object* v___x_2974_, lean_object* v___x_2975_, lean_object* v___x_2976_, lean_object* v___x_2977_, lean_object* v_ism1_x27_2978_, lean_object* v_ism2_x27_2979_, lean_object* v_is_2980_, lean_object* v___x_2981_, lean_object* v_newEqs1_2982_, lean_object* v_newRefls1_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
uint8_t v___x_15005__boxed_2989_; uint8_t v___x_15006__boxed_2990_; uint8_t v___x_15007__boxed_2991_; lean_object* v_res_2992_; 
v___x_15005__boxed_2989_ = lean_unbox(v___x_2975_);
v___x_15006__boxed_2990_ = lean_unbox(v___x_2976_);
v___x_15007__boxed_2991_ = lean_unbox(v___x_2977_);
v_res_2992_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2973_, v___x_2974_, v___x_15005__boxed_2989_, v___x_15006__boxed_2990_, v___x_15007__boxed_2991_, v_ism1_x27_2978_, v_ism2_x27_2979_, v_is_2980_, v___x_2981_, v_newEqs1_2982_, v_newRefls1_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_2993_, uint8_t v___x_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Lean_addDecl(v___x_2993_, v___x_2994_, v___y_2997_, v___y_2998_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3001_, lean_object* v___x_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_){
_start:
{
uint8_t v___x_15047__boxed_3008_; lean_object* v_res_3009_; 
v___x_15047__boxed_3008_ = lean_unbox(v___x_3002_);
v_res_3009_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3001_, v___x_15047__boxed_3008_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_);
lean_dec(v___y_3006_);
lean_dec_ref(v___y_3005_);
lean_dec(v___y_3004_);
lean_dec_ref(v___y_3003_);
return v_res_3009_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3012_ = l_Lean_stringToMessageData(v___x_3011_);
return v___x_3012_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; 
v___x_3014_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3015_ = l_Lean_stringToMessageData(v___x_3014_);
return v___x_3015_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3021_ = lean_box(0);
v___x_3022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3023_ = l_Lean_mkConst(v___x_3022_, v___x_3021_);
return v___x_3023_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3026_ = l_Lean_stringToMessageData(v___x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3027_, lean_object* v_a_3028_, lean_object* v___x_3029_, lean_object* v_zs1_3030_, lean_object* v_snd_3031_, uint8_t v___x_3032_, uint8_t v___x_3033_, uint8_t v___x_3034_, lean_object* v_alts_3035_, lean_object* v_zs2_3036_, lean_object* v___ctorRet2_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = lean_array_get_borrowed(v___x_3027_, v_a_3028_, v___x_3029_);
lean_inc_ref(v_zs1_3030_);
v___x_3044_ = l_Array_append___redArg(v_zs1_3030_, v_zs2_3036_);
lean_inc(v___x_3043_);
v___x_3045_ = l_Lean_Meta_instantiateForall(v___x_3043_, v___x_3044_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
if (lean_obj_tag(v___x_3045_) == 0)
{
lean_object* v_a_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v_a_3046_ = lean_ctor_get(v___x_3045_, 0);
lean_inc(v_a_3046_);
lean_dec_ref_known(v___x_3045_, 1);
v___x_3047_ = lean_box(0);
v___x_3048_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3046_, v___x_3047_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v___x_3050_ = l_Lean_Expr_mvarId_x21(v_a_3049_);
v___x_3051_ = lean_array_get_size(v_snd_3031_);
v___x_3052_ = lean_box(0);
v___x_3053_ = lean_box(0);
lean_inc_ref(v___y_3040_);
v___x_3054_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3051_, v___x_3050_, v___x_3052_, v___x_3053_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_a_3055_);
lean_dec_ref_known(v___x_3054_, 1);
if (lean_obj_tag(v_a_3055_) == 1)
{
lean_object* v_val_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3103_; 
v_val_3056_ = lean_ctor_get(v_a_3055_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_a_3055_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3058_ = v_a_3055_;
v_isShared_3059_ = v_isSharedCheck_3103_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_val_3056_);
lean_dec(v_a_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3103_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v_fst_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3101_; 
v_fst_3060_ = lean_ctor_get(v_val_3056_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_val_3056_);
if (v_isSharedCheck_3101_ == 0)
{
lean_object* v_unused_3102_; 
v_unused_3102_ = lean_ctor_get(v_val_3056_, 1);
lean_dec(v_unused_3102_);
v___x_3062_ = v_val_3056_;
v_isShared_3063_ = v_isSharedCheck_3101_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_fst_3060_);
lean_dec(v_val_3056_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3101_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___y_3065_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; uint8_t v___x_3096_; 
v___x_3093_ = lean_array_get_borrowed(v___x_3027_, v_alts_3035_, v___x_3029_);
v___x_3094_ = lean_array_get_size(v_zs1_3030_);
lean_dec_ref(v_zs1_3030_);
v___x_3095_ = lean_unsigned_to_nat(0u);
v___x_3096_ = lean_nat_dec_eq(v___x_3094_, v___x_3095_);
if (v___x_3096_ == 0)
{
lean_inc(v___x_3093_);
v___y_3065_ = v___x_3093_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3097_; uint8_t v___x_3098_; 
v___x_3097_ = lean_array_get_size(v_zs2_3036_);
v___x_3098_ = lean_nat_dec_eq(v___x_3097_, v___x_3095_);
if (v___x_3098_ == 0)
{
lean_inc(v___x_3093_);
v___y_3065_ = v___x_3093_;
goto v___jp_3064_;
}
else
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3093_);
v___x_3100_ = l_Lean_Expr_app___override(v___x_3093_, v___x_3099_);
v___y_3065_ = v___x_3100_;
goto v___jp_3064_;
}
}
v___jp_3064_:
{
uint8_t v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = 0;
v___x_3067_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3067_, 0, v___x_3066_);
lean_ctor_set_uint8(v___x_3067_, 1, v___x_3032_);
lean_ctor_set_uint8(v___x_3067_, 2, v___x_3033_);
lean_ctor_set_uint8(v___x_3067_, 3, v___x_3032_);
lean_inc_ref(v___y_3065_);
lean_inc(v_fst_3060_);
v___x_3068_ = l_Lean_MVarId_apply(v_fst_3060_, v___y_3065_, v___x_3067_, v___x_3053_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_object* v_a_3069_; 
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v___x_3068_, 1);
if (lean_obj_tag(v_a_3069_) == 0)
{
lean_object* v___x_3070_; 
lean_dec_ref(v___y_3065_);
lean_del_object(v___x_3062_);
lean_dec(v_fst_3060_);
lean_del_object(v___x_3058_);
v___x_3070_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3049_, v___y_3039_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3072_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v___x_3072_ = l_Lean_Meta_mkLambdaFVars(v___x_3044_, v_a_3071_, v___x_3033_, v___x_3032_, v___x_3033_, v___x_3032_, v___x_3034_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
lean_dec_ref(v___x_3044_);
return v___x_3072_;
}
else
{
lean_dec_ref(v___x_3044_);
return v___x_3070_;
}
}
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3076_; 
lean_dec(v_a_3069_);
lean_dec(v_a_3049_);
lean_dec_ref(v___x_3044_);
v___x_3073_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3074_ = l_Lean_MessageData_ofExpr(v___y_3065_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set_tag(v___x_3062_, 7);
lean_ctor_set(v___x_3062_, 1, v___x_3074_);
lean_ctor_set(v___x_3062_, 0, v___x_3073_);
v___x_3076_ = v___x_3062_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3073_);
lean_ctor_set(v_reuseFailAlloc_3084_, 1, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3077_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3076_);
lean_ctor_set(v___x_3078_, 1, v___x_3077_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v_fst_3060_);
v___x_3080_ = v___x_3058_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_fst_3060_);
v___x_3080_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3078_);
lean_ctor_set(v___x_3081_, 1, v___x_3080_);
v___x_3082_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3081_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_dec_ref(v___y_3065_);
lean_del_object(v___x_3062_);
lean_dec(v_fst_3060_);
lean_del_object(v___x_3058_);
lean_dec(v_a_3049_);
lean_dec_ref(v___x_3044_);
v_a_3085_ = lean_ctor_get(v___x_3068_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3068_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3068_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3068_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; 
lean_dec(v_a_3055_);
lean_dec(v_a_3049_);
lean_dec_ref(v___x_3044_);
lean_dec_ref(v_zs1_3030_);
v___x_3104_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3105_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3104_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
return v___x_3105_;
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec(v_a_3049_);
lean_dec_ref(v___x_3044_);
lean_dec_ref(v_zs1_3030_);
v_a_3106_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3054_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3054_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
else
{
lean_dec_ref(v___x_3044_);
lean_dec_ref(v_zs1_3030_);
return v___x_3048_;
}
}
else
{
lean_dec_ref(v___x_3044_);
lean_dec_ref(v_zs1_3030_);
return v___x_3045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3114_, lean_object* v_a_3115_, lean_object* v___x_3116_, lean_object* v_zs1_3117_, lean_object* v_snd_3118_, lean_object* v___x_3119_, lean_object* v___x_3120_, lean_object* v___x_3121_, lean_object* v_alts_3122_, lean_object* v_zs2_3123_, lean_object* v___ctorRet2_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
uint8_t v___x_15107__boxed_3130_; uint8_t v___x_15108__boxed_3131_; uint8_t v___x_15109__boxed_3132_; lean_object* v_res_3133_; 
v___x_15107__boxed_3130_ = lean_unbox(v___x_3119_);
v___x_15108__boxed_3131_ = lean_unbox(v___x_3120_);
v___x_15109__boxed_3132_ = lean_unbox(v___x_3121_);
v_res_3133_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3114_, v_a_3115_, v___x_3116_, v_zs1_3117_, v_snd_3118_, v___x_15107__boxed_3130_, v___x_15108__boxed_3131_, v___x_15109__boxed_3132_, v_alts_3122_, v_zs2_3123_, v___ctorRet2_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec_ref(v___ctorRet2_3124_);
lean_dec_ref(v_zs2_3123_);
lean_dec_ref(v_alts_3122_);
lean_dec_ref(v_snd_3118_);
lean_dec(v___x_3116_);
lean_dec_ref(v_a_3115_);
lean_dec_ref(v___x_3114_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3134_, lean_object* v_a_3135_, lean_object* v___x_3136_, lean_object* v_snd_3137_, uint8_t v___x_3138_, uint8_t v___x_3139_, uint8_t v___x_3140_, lean_object* v_alts_3141_, lean_object* v_a_3142_, lean_object* v_zs1_3143_, lean_object* v___ctorRet1_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___f_3153_; lean_object* v___x_3154_; 
v___x_3150_ = lean_box(v___x_3138_);
v___x_3151_ = lean_box(v___x_3139_);
v___x_3152_ = lean_box(v___x_3140_);
v___f_3153_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3153_, 0, v___x_3134_);
lean_closure_set(v___f_3153_, 1, v_a_3135_);
lean_closure_set(v___f_3153_, 2, v___x_3136_);
lean_closure_set(v___f_3153_, 3, v_zs1_3143_);
lean_closure_set(v___f_3153_, 4, v_snd_3137_);
lean_closure_set(v___f_3153_, 5, v___x_3150_);
lean_closure_set(v___f_3153_, 6, v___x_3151_);
lean_closure_set(v___f_3153_, 7, v___x_3152_);
lean_closure_set(v___f_3153_, 8, v_alts_3141_);
v___x_3154_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3142_, v___f_3153_, v___x_3139_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v___x_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3155_, lean_object* v_a_3156_, lean_object* v___x_3157_, lean_object* v_snd_3158_, lean_object* v___x_3159_, lean_object* v___x_3160_, lean_object* v___x_3161_, lean_object* v_alts_3162_, lean_object* v_a_3163_, lean_object* v_zs1_3164_, lean_object* v___ctorRet1_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
uint8_t v___x_15306__boxed_3171_; uint8_t v___x_15307__boxed_3172_; uint8_t v___x_15308__boxed_3173_; lean_object* v_res_3174_; 
v___x_15306__boxed_3171_ = lean_unbox(v___x_3159_);
v___x_15307__boxed_3172_ = lean_unbox(v___x_3160_);
v___x_15308__boxed_3173_ = lean_unbox(v___x_3161_);
v_res_3174_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3155_, v_a_3156_, v___x_3157_, v_snd_3158_, v___x_15306__boxed_3171_, v___x_15307__boxed_3172_, v___x_15308__boxed_3173_, v_alts_3162_, v_a_3163_, v_zs1_3164_, v___ctorRet1_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec_ref(v___ctorRet1_3165_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3175_, lean_object* v_params_3176_, lean_object* v_a_3177_, lean_object* v_snd_3178_, lean_object* v_alts_3179_, size_t v_sz_3180_, size_t v_i_3181_, lean_object* v_bs_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
uint8_t v___x_3188_; 
v___x_3188_ = lean_usize_dec_lt(v_i_3181_, v_sz_3180_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; 
lean_dec_ref(v_alts_3179_);
lean_dec_ref(v_snd_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_tail_3175_);
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v_bs_3182_);
return v___x_3189_;
}
else
{
lean_object* v_v_3190_; lean_object* v___x_3191_; lean_object* v_bs_x27_3192_; lean_object* v___y_3194_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v_v_3190_ = lean_array_uget(v_bs_3182_, v_i_3181_);
v___x_3191_ = lean_unsigned_to_nat(0u);
v_bs_x27_3192_ = lean_array_uset(v_bs_3182_, v_i_3181_, v___x_3191_);
lean_inc(v_tail_3175_);
v___x_3208_ = l_Lean_mkConst(v_v_3190_, v_tail_3175_);
v___x_3209_ = l_Lean_mkAppN(v___x_3208_, v_params_3176_);
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
lean_inc(v___y_3184_);
lean_inc_ref(v___y_3183_);
v___x_3210_ = lean_infer_type(v___x_3209_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; uint8_t v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc_n(v_a_3211_, 2);
lean_dec_ref_known(v___x_3210_, 1);
v___x_3212_ = l_Lean_instInhabitedExpr;
v___x_3213_ = 0;
v___x_3214_ = 1;
v___x_3215_ = lean_usize_to_nat(v_i_3181_);
v___x_3216_ = lean_box(v___x_3188_);
v___x_3217_ = lean_box(v___x_3213_);
v___x_3218_ = lean_box(v___x_3214_);
lean_inc_ref(v_alts_3179_);
lean_inc_ref(v_snd_3178_);
lean_inc_ref(v_a_3177_);
v___f_3219_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3219_, 0, v___x_3212_);
lean_closure_set(v___f_3219_, 1, v_a_3177_);
lean_closure_set(v___f_3219_, 2, v___x_3215_);
lean_closure_set(v___f_3219_, 3, v_snd_3178_);
lean_closure_set(v___f_3219_, 4, v___x_3216_);
lean_closure_set(v___f_3219_, 5, v___x_3217_);
lean_closure_set(v___f_3219_, 6, v___x_3218_);
lean_closure_set(v___f_3219_, 7, v_alts_3179_);
lean_closure_set(v___f_3219_, 8, v_a_3211_);
v___x_3220_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3211_, v___f_3219_, v___x_3213_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
v___y_3194_ = v___x_3220_;
goto v___jp_3193_;
}
else
{
v___y_3194_ = v___x_3210_;
goto v___jp_3193_;
}
v___jp_3193_:
{
if (lean_obj_tag(v___y_3194_) == 0)
{
lean_object* v_a_3195_; size_t v___x_3196_; size_t v___x_3197_; lean_object* v___x_3198_; 
v_a_3195_ = lean_ctor_get(v___y_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v___y_3194_, 1);
v___x_3196_ = ((size_t)1ULL);
v___x_3197_ = lean_usize_add(v_i_3181_, v___x_3196_);
v___x_3198_ = lean_array_uset(v_bs_x27_3192_, v_i_3181_, v_a_3195_);
v_i_3181_ = v___x_3197_;
v_bs_3182_ = v___x_3198_;
goto _start;
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec_ref(v_bs_x27_3192_);
lean_dec_ref(v_alts_3179_);
lean_dec_ref(v_snd_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_tail_3175_);
v_a_3200_ = lean_ctor_get(v___y_3194_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___y_3194_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___y_3194_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___y_3194_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3221_, lean_object* v_params_3222_, lean_object* v_a_3223_, lean_object* v_snd_3224_, lean_object* v_alts_3225_, lean_object* v_sz_3226_, lean_object* v_i_3227_, lean_object* v_bs_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
size_t v_sz_boxed_3234_; size_t v_i_boxed_3235_; lean_object* v_res_3236_; 
v_sz_boxed_3234_ = lean_unbox_usize(v_sz_3226_);
lean_dec(v_sz_3226_);
v_i_boxed_3235_ = lean_unbox_usize(v_i_3227_);
lean_dec(v_i_3227_);
v_res_3236_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3221_, v_params_3222_, v_a_3223_, v_snd_3224_, v_alts_3225_, v_sz_boxed_3234_, v_i_boxed_3235_, v_bs_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v_params_3222_);
return v_res_3236_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3237_ = lean_box(0);
v___x_3238_ = lean_unsigned_to_nat(16u);
v___x_3239_ = lean_mk_array(v___x_3238_, v___x_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3240_, lean_object* v___x_3241_, uint8_t v___x_3242_, uint8_t v___x_3243_, uint8_t v___x_3244_, lean_object* v_ism1_x27_3245_, lean_object* v_is_3246_, lean_object* v___x_3247_, lean_object* v___x_3248_, lean_object* v___x_3249_, lean_object* v___x_3250_, lean_object* v_params_3251_, lean_object* v___x_3252_, lean_object* v___x_3253_, lean_object* v_heq_3254_, lean_object* v_val_3255_, lean_object* v_tail_3256_, lean_object* v_alts_3257_, size_t v_sz_3258_, size_t v___x_3259_, lean_object* v___x_3260_, lean_object* v___x_3261_, lean_object* v_declName_3262_, lean_object* v_levelParams_3263_, lean_object* v_numIndices_3264_, lean_object* v___x_3265_, lean_object* v___x_3266_, lean_object* v_numParams_3267_, lean_object* v_snd_3268_, lean_object* v_ism2_x27_3269_, lean_object* v_x_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3276_ = lean_box(v___x_3242_);
v___x_3277_ = lean_box(v___x_3243_);
v___x_3278_ = lean_box(v___x_3244_);
lean_inc_ref(v___x_3247_);
lean_inc_ref_n(v_is_3246_, 2);
lean_inc_ref(v_ism1_x27_3245_);
lean_inc_ref(v_motive_3240_);
v___f_3279_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3279_, 0, v_motive_3240_);
lean_closure_set(v___f_3279_, 1, v___x_3241_);
lean_closure_set(v___f_3279_, 2, v___x_3276_);
lean_closure_set(v___f_3279_, 3, v___x_3277_);
lean_closure_set(v___f_3279_, 4, v___x_3278_);
lean_closure_set(v___f_3279_, 5, v_ism1_x27_3245_);
lean_closure_set(v___f_3279_, 6, v_ism2_x27_3269_);
lean_closure_set(v___f_3279_, 7, v_is_3246_);
lean_closure_set(v___f_3279_, 8, v___x_3247_);
lean_inc_ref(v___x_3248_);
v___x_3280_ = lean_array_push(v_is_3246_, v___x_3248_);
v___x_3281_ = l_Lean_Meta_withNewEqs___redArg(v___x_3280_, v_ism1_x27_3245_, v___f_3279_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3281_) == 0)
{
lean_object* v_a_3282_; lean_object* v_fst_3283_; lean_object* v_snd_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3385_; 
v_a_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc(v_a_3282_);
lean_dec_ref_known(v___x_3281_, 1);
v_fst_3283_ = lean_ctor_get(v_a_3282_, 0);
v_snd_3284_ = lean_ctor_get(v_a_3282_, 1);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_a_3282_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3286_ = v_a_3282_;
v_isShared_3287_ = v_isSharedCheck_3385_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_snd_3284_);
lean_inc(v_fst_3283_);
lean_dec(v_a_3282_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3385_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3288_ = l_Lean_mkConst(v___x_3249_, v___x_3250_);
v___x_3289_ = l_Lean_mkAppN(v___x_3288_, v_params_3251_);
v___x_3290_ = l_Lean_Expr_app___override(v___x_3289_, v_fst_3283_);
lean_inc_ref(v_is_3246_);
v___x_3291_ = l_Array_append___redArg(v_is_3246_, v___x_3252_);
v___x_3292_ = l_Array_append___redArg(v___x_3291_, v_is_3246_);
v___x_3293_ = l_Array_append___redArg(v___x_3292_, v___x_3253_);
v___x_3294_ = l_Lean_mkAppN(v___x_3290_, v___x_3293_);
lean_dec_ref(v___x_3293_);
lean_inc_ref(v_heq_3254_);
v___x_3295_ = l_Lean_Expr_app___override(v___x_3294_, v_heq_3254_);
v___x_3296_ = l_Lean_InductiveVal_numCtors(v_val_3255_);
lean_inc_ref(v___x_3295_);
v___x_3297_ = l_Lean_Meta_inferArgumentTypesN(v___x_3296_, v___x_3295_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
lean_inc_ref(v_alts_3257_);
lean_inc(v_snd_3284_);
v___x_3299_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3256_, v_params_3251_, v_a_3298_, v_snd_3284_, v_alts_3257_, v_sz_3258_, v___x_3259_, v___x_3260_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
v___x_3301_ = l_Lean_mkAppN(v___x_3295_, v_a_3300_);
lean_dec(v_a_3300_);
v___x_3302_ = l_Lean_mkAppN(v___x_3301_, v_snd_3284_);
lean_dec(v_snd_3284_);
lean_inc_ref(v___x_3261_);
v___x_3303_ = lean_array_push(v___x_3261_, v_motive_3240_);
v___x_3304_ = l_Array_append___redArg(v_params_3251_, v___x_3303_);
lean_dec_ref(v___x_3303_);
v___x_3305_ = l_Array_append___redArg(v___x_3304_, v_is_3246_);
lean_dec_ref(v_is_3246_);
v___x_3306_ = lean_unsigned_to_nat(2u);
v___x_3307_ = lean_mk_empty_array_with_capacity(v___x_3306_);
v___x_3308_ = lean_array_push(v___x_3307_, v___x_3248_);
v___x_3309_ = lean_array_push(v___x_3308_, v___x_3247_);
v___x_3310_ = l_Array_append___redArg(v___x_3305_, v___x_3309_);
lean_dec_ref(v___x_3309_);
v___x_3311_ = lean_array_push(v___x_3261_, v_heq_3254_);
v___x_3312_ = l_Array_append___redArg(v___x_3310_, v___x_3311_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = l_Array_append___redArg(v___x_3312_, v_alts_3257_);
lean_dec_ref(v_alts_3257_);
v___x_3314_ = l_Lean_Meta_mkLambdaFVars(v___x_3313_, v___x_3302_, v___x_3242_, v___x_3243_, v___x_3242_, v___x_3243_, v___x_3244_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec_ref(v___x_3313_);
if (lean_obj_tag(v___x_3314_) == 0)
{
lean_object* v_a_3315_; lean_object* v___x_3316_; 
v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc_n(v_a_3315_, 2);
lean_dec_ref_known(v___x_3314_, 1);
lean_inc(v___y_3274_);
lean_inc_ref(v___y_3273_);
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3271_);
v___x_3316_ = lean_infer_type(v_a_3315_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v_a_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3352_; 
v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_a_3317_);
lean_dec_ref_known(v___x_3316_, 1);
v___x_3318_ = lean_box(1);
lean_inc(v_declName_3262_);
v___x_3319_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3262_, v_levelParams_3263_, v_a_3317_, v_a_3315_, v___x_3318_, v___y_3274_);
v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3352_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3352_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3325_; 
if (v_isShared_3323_ == 0)
{
lean_ctor_set_tag(v___x_3322_, 1);
v___x_3325_ = v___x_3322_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3320_);
v___x_3325_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3326_; lean_object* v___f_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
v___x_3326_ = lean_box(v___x_3242_);
lean_inc_ref(v___x_3325_);
v___f_3327_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3327_, 0, v___x_3325_);
lean_closure_set(v___f_3327_, 1, v___x_3326_);
v___x_3328_ = lean_nat_add(v_numIndices_3264_, v___x_3265_);
lean_inc(v___x_3266_);
v___x_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3266_);
v___x_3330_ = lean_box(0);
v___x_3331_ = lean_mk_empty_array_with_capacity(v___x_3265_);
v___x_3332_ = lean_array_push(v___x_3331_, v___x_3330_);
v___x_3333_ = lean_array_push(v___x_3332_, v___x_3330_);
v___x_3334_ = lean_array_push(v___x_3333_, v___x_3330_);
v___x_3335_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 1, v___x_3335_);
lean_ctor_set(v___x_3286_, 0, v___x_3266_);
v___x_3337_ = v___x_3286_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3350_; 
v_reuseFailAlloc_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3350_, 0, v___x_3266_);
lean_ctor_set(v_reuseFailAlloc_3350_, 1, v___x_3335_);
v___x_3337_ = v_reuseFailAlloc_3350_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3338_; uint8_t v___y_3340_; uint8_t v___x_3349_; 
v___x_3338_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3338_, 0, v_numParams_3267_);
lean_ctor_set(v___x_3338_, 1, v___x_3328_);
lean_ctor_set(v___x_3338_, 2, v_snd_3268_);
lean_ctor_set(v___x_3338_, 3, v___x_3329_);
lean_ctor_set(v___x_3338_, 4, v___x_3334_);
lean_ctor_set(v___x_3338_, 5, v___x_3337_);
v___x_3349_ = l_Lean_isPrivateName(v_declName_3262_);
if (v___x_3349_ == 0)
{
v___y_3340_ = v___x_3243_;
goto v___jp_3339_;
}
else
{
v___y_3340_ = v___x_3242_;
goto v___jp_3339_;
}
v___jp_3339_:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3327_, v___y_3340_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; 
lean_dec_ref_known(v___x_3341_, 1);
v___x_3342_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3262_);
v___x_3343_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3342_, v_declName_3262_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v___x_3344_; uint8_t v___x_3345_; lean_object* v___x_3346_; 
lean_dec_ref_known(v___x_3343_, 1);
lean_inc_n(v_declName_3262_, 2);
v___x_3344_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3262_, v___x_3338_, v___y_3272_, v___y_3274_);
lean_dec_ref(v___x_3344_);
v___x_3345_ = 0;
v___x_3346_ = l_Lean_Meta_setInlineAttribute(v_declName_3262_, v___x_3345_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_object* v___x_3347_; 
lean_dec_ref_known(v___x_3346_, 1);
v___x_3347_ = l_Lean_enableRealizationsForConst(v_declName_3262_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v___x_3348_; 
lean_dec_ref_known(v___x_3347_, 1);
v___x_3348_ = l_Lean_compileDecl(v___x_3325_, v___x_3243_, v___y_3273_, v___y_3274_);
return v___x_3348_;
}
else
{
lean_dec_ref(v___x_3325_);
return v___x_3347_;
}
}
else
{
lean_dec_ref(v___x_3325_);
lean_dec(v_declName_3262_);
return v___x_3346_;
}
}
else
{
lean_dec_ref_known(v___x_3338_, 6);
lean_dec_ref(v___x_3325_);
lean_dec(v_declName_3262_);
return v___x_3343_;
}
}
else
{
lean_dec_ref_known(v___x_3338_, 6);
lean_dec_ref(v___x_3325_);
lean_dec(v_declName_3262_);
return v___x_3341_;
}
}
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec(v_a_3315_);
lean_del_object(v___x_3286_);
lean_dec_ref(v_snd_3268_);
lean_dec(v_numParams_3267_);
lean_dec(v___x_3266_);
lean_dec(v_levelParams_3263_);
lean_dec(v_declName_3262_);
v_a_3353_ = lean_ctor_get(v___x_3316_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3316_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3316_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3316_);
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
lean_del_object(v___x_3286_);
lean_dec_ref(v_snd_3268_);
lean_dec(v_numParams_3267_);
lean_dec(v___x_3266_);
lean_dec(v_levelParams_3263_);
lean_dec(v_declName_3262_);
v_a_3361_ = lean_ctor_get(v___x_3314_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3314_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3363_ = v___x_3314_;
v_isShared_3364_ = v_isSharedCheck_3368_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3314_);
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
lean_dec_ref(v___x_3295_);
lean_del_object(v___x_3286_);
lean_dec(v_snd_3284_);
lean_dec_ref(v_snd_3268_);
lean_dec(v_numParams_3267_);
lean_dec(v___x_3266_);
lean_dec(v_levelParams_3263_);
lean_dec(v_declName_3262_);
lean_dec_ref(v___x_3261_);
lean_dec_ref(v_alts_3257_);
lean_dec_ref(v_heq_3254_);
lean_dec_ref(v_params_3251_);
lean_dec_ref(v___x_3248_);
lean_dec_ref(v___x_3247_);
lean_dec_ref(v_is_3246_);
lean_dec_ref(v_motive_3240_);
v_a_3369_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3299_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3299_);
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
lean_dec_ref(v___x_3295_);
lean_del_object(v___x_3286_);
lean_dec(v_snd_3284_);
lean_dec_ref(v_snd_3268_);
lean_dec(v_numParams_3267_);
lean_dec(v___x_3266_);
lean_dec(v_levelParams_3263_);
lean_dec(v_declName_3262_);
lean_dec_ref(v___x_3261_);
lean_dec_ref(v___x_3260_);
lean_dec_ref(v_alts_3257_);
lean_dec(v_tail_3256_);
lean_dec_ref(v_heq_3254_);
lean_dec_ref(v_params_3251_);
lean_dec_ref(v___x_3248_);
lean_dec_ref(v___x_3247_);
lean_dec_ref(v_is_3246_);
lean_dec_ref(v_motive_3240_);
v_a_3377_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3297_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3297_);
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
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec_ref(v_snd_3268_);
lean_dec(v_numParams_3267_);
lean_dec(v___x_3266_);
lean_dec(v_levelParams_3263_);
lean_dec(v_declName_3262_);
lean_dec_ref(v___x_3261_);
lean_dec_ref(v___x_3260_);
lean_dec_ref(v_alts_3257_);
lean_dec(v_tail_3256_);
lean_dec_ref(v_heq_3254_);
lean_dec_ref(v_params_3251_);
lean_dec(v___x_3250_);
lean_dec(v___x_3249_);
lean_dec_ref(v___x_3248_);
lean_dec_ref(v___x_3247_);
lean_dec_ref(v_is_3246_);
lean_dec_ref(v_motive_3240_);
v_a_3386_ = lean_ctor_get(v___x_3281_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3281_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3281_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3394_ = _args[0];
lean_object* v___x_3395_ = _args[1];
lean_object* v___x_3396_ = _args[2];
lean_object* v___x_3397_ = _args[3];
lean_object* v___x_3398_ = _args[4];
lean_object* v_ism1_x27_3399_ = _args[5];
lean_object* v_is_3400_ = _args[6];
lean_object* v___x_3401_ = _args[7];
lean_object* v___x_3402_ = _args[8];
lean_object* v___x_3403_ = _args[9];
lean_object* v___x_3404_ = _args[10];
lean_object* v_params_3405_ = _args[11];
lean_object* v___x_3406_ = _args[12];
lean_object* v___x_3407_ = _args[13];
lean_object* v_heq_3408_ = _args[14];
lean_object* v_val_3409_ = _args[15];
lean_object* v_tail_3410_ = _args[16];
lean_object* v_alts_3411_ = _args[17];
lean_object* v_sz_3412_ = _args[18];
lean_object* v___x_3413_ = _args[19];
lean_object* v___x_3414_ = _args[20];
lean_object* v___x_3415_ = _args[21];
lean_object* v_declName_3416_ = _args[22];
lean_object* v_levelParams_3417_ = _args[23];
lean_object* v_numIndices_3418_ = _args[24];
lean_object* v___x_3419_ = _args[25];
lean_object* v___x_3420_ = _args[26];
lean_object* v_numParams_3421_ = _args[27];
lean_object* v_snd_3422_ = _args[28];
lean_object* v_ism2_x27_3423_ = _args[29];
lean_object* v_x_3424_ = _args[30];
lean_object* v___y_3425_ = _args[31];
lean_object* v___y_3426_ = _args[32];
lean_object* v___y_3427_ = _args[33];
lean_object* v___y_3428_ = _args[34];
lean_object* v___y_3429_ = _args[35];
_start:
{
uint8_t v___x_15445__boxed_3430_; uint8_t v___x_15446__boxed_3431_; uint8_t v___x_15447__boxed_3432_; size_t v_sz_boxed_3433_; size_t v___x_15456__boxed_3434_; lean_object* v_res_3435_; 
v___x_15445__boxed_3430_ = lean_unbox(v___x_3396_);
v___x_15446__boxed_3431_ = lean_unbox(v___x_3397_);
v___x_15447__boxed_3432_ = lean_unbox(v___x_3398_);
v_sz_boxed_3433_ = lean_unbox_usize(v_sz_3412_);
lean_dec(v_sz_3412_);
v___x_15456__boxed_3434_ = lean_unbox_usize(v___x_3413_);
lean_dec(v___x_3413_);
v_res_3435_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3394_, v___x_3395_, v___x_15445__boxed_3430_, v___x_15446__boxed_3431_, v___x_15447__boxed_3432_, v_ism1_x27_3399_, v_is_3400_, v___x_3401_, v___x_3402_, v___x_3403_, v___x_3404_, v_params_3405_, v___x_3406_, v___x_3407_, v_heq_3408_, v_val_3409_, v_tail_3410_, v_alts_3411_, v_sz_boxed_3433_, v___x_15456__boxed_3434_, v___x_3414_, v___x_3415_, v_declName_3416_, v_levelParams_3417_, v_numIndices_3418_, v___x_3419_, v___x_3420_, v_numParams_3421_, v_snd_3422_, v_ism2_x27_3423_, v_x_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
lean_dec(v___y_3426_);
lean_dec_ref(v___y_3425_);
lean_dec_ref(v_x_3424_);
lean_dec(v___x_3419_);
lean_dec(v_numIndices_3418_);
lean_dec_ref(v_val_3409_);
lean_dec_ref(v___x_3407_);
lean_dec_ref(v___x_3406_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3436_, lean_object* v___x_3437_, uint8_t v___x_3438_, uint8_t v___x_3439_, uint8_t v___x_3440_, lean_object* v_is_3441_, lean_object* v___x_3442_, lean_object* v___x_3443_, lean_object* v___x_3444_, lean_object* v___x_3445_, lean_object* v_params_3446_, lean_object* v___x_3447_, lean_object* v___x_3448_, lean_object* v_heq_3449_, lean_object* v_val_3450_, lean_object* v_tail_3451_, lean_object* v_alts_3452_, size_t v_sz_3453_, size_t v___x_3454_, lean_object* v___x_3455_, lean_object* v___x_3456_, lean_object* v_declName_3457_, lean_object* v_levelParams_3458_, lean_object* v_numIndices_3459_, lean_object* v___x_3460_, lean_object* v___x_3461_, lean_object* v_numParams_3462_, lean_object* v_snd_3463_, lean_object* v___x_3464_, lean_object* v___x_3465_, lean_object* v_ism1_x27_3466_, lean_object* v_x_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___f_3478_; lean_object* v___x_3479_; 
v___x_3473_ = lean_box(v___x_3438_);
v___x_3474_ = lean_box(v___x_3439_);
v___x_3475_ = lean_box(v___x_3440_);
v___x_3476_ = lean_box_usize(v_sz_3453_);
v___x_3477_ = lean_box_usize(v___x_3454_);
v___f_3478_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3478_, 0, v_motive_3436_);
lean_closure_set(v___f_3478_, 1, v___x_3437_);
lean_closure_set(v___f_3478_, 2, v___x_3473_);
lean_closure_set(v___f_3478_, 3, v___x_3474_);
lean_closure_set(v___f_3478_, 4, v___x_3475_);
lean_closure_set(v___f_3478_, 5, v_ism1_x27_3466_);
lean_closure_set(v___f_3478_, 6, v_is_3441_);
lean_closure_set(v___f_3478_, 7, v___x_3442_);
lean_closure_set(v___f_3478_, 8, v___x_3443_);
lean_closure_set(v___f_3478_, 9, v___x_3444_);
lean_closure_set(v___f_3478_, 10, v___x_3445_);
lean_closure_set(v___f_3478_, 11, v_params_3446_);
lean_closure_set(v___f_3478_, 12, v___x_3447_);
lean_closure_set(v___f_3478_, 13, v___x_3448_);
lean_closure_set(v___f_3478_, 14, v_heq_3449_);
lean_closure_set(v___f_3478_, 15, v_val_3450_);
lean_closure_set(v___f_3478_, 16, v_tail_3451_);
lean_closure_set(v___f_3478_, 17, v_alts_3452_);
lean_closure_set(v___f_3478_, 18, v___x_3476_);
lean_closure_set(v___f_3478_, 19, v___x_3477_);
lean_closure_set(v___f_3478_, 20, v___x_3455_);
lean_closure_set(v___f_3478_, 21, v___x_3456_);
lean_closure_set(v___f_3478_, 22, v_declName_3457_);
lean_closure_set(v___f_3478_, 23, v_levelParams_3458_);
lean_closure_set(v___f_3478_, 24, v_numIndices_3459_);
lean_closure_set(v___f_3478_, 25, v___x_3460_);
lean_closure_set(v___f_3478_, 26, v___x_3461_);
lean_closure_set(v___f_3478_, 27, v_numParams_3462_);
lean_closure_set(v___f_3478_, 28, v_snd_3463_);
v___x_3479_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3464_, v___x_3465_, v___f_3478_, v___x_3438_, v___x_3438_, v___y_3468_, v___y_3469_, v___y_3470_, v___y_3471_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3480_ = _args[0];
lean_object* v___x_3481_ = _args[1];
lean_object* v___x_3482_ = _args[2];
lean_object* v___x_3483_ = _args[3];
lean_object* v___x_3484_ = _args[4];
lean_object* v_is_3485_ = _args[5];
lean_object* v___x_3486_ = _args[6];
lean_object* v___x_3487_ = _args[7];
lean_object* v___x_3488_ = _args[8];
lean_object* v___x_3489_ = _args[9];
lean_object* v_params_3490_ = _args[10];
lean_object* v___x_3491_ = _args[11];
lean_object* v___x_3492_ = _args[12];
lean_object* v_heq_3493_ = _args[13];
lean_object* v_val_3494_ = _args[14];
lean_object* v_tail_3495_ = _args[15];
lean_object* v_alts_3496_ = _args[16];
lean_object* v_sz_3497_ = _args[17];
lean_object* v___x_3498_ = _args[18];
lean_object* v___x_3499_ = _args[19];
lean_object* v___x_3500_ = _args[20];
lean_object* v_declName_3501_ = _args[21];
lean_object* v_levelParams_3502_ = _args[22];
lean_object* v_numIndices_3503_ = _args[23];
lean_object* v___x_3504_ = _args[24];
lean_object* v___x_3505_ = _args[25];
lean_object* v_numParams_3506_ = _args[26];
lean_object* v_snd_3507_ = _args[27];
lean_object* v___x_3508_ = _args[28];
lean_object* v___x_3509_ = _args[29];
lean_object* v_ism1_x27_3510_ = _args[30];
lean_object* v_x_3511_ = _args[31];
lean_object* v___y_3512_ = _args[32];
lean_object* v___y_3513_ = _args[33];
lean_object* v___y_3514_ = _args[34];
lean_object* v___y_3515_ = _args[35];
lean_object* v___y_3516_ = _args[36];
_start:
{
uint8_t v___x_15767__boxed_3517_; uint8_t v___x_15768__boxed_3518_; uint8_t v___x_15769__boxed_3519_; size_t v_sz_boxed_3520_; size_t v___x_15778__boxed_3521_; lean_object* v_res_3522_; 
v___x_15767__boxed_3517_ = lean_unbox(v___x_3482_);
v___x_15768__boxed_3518_ = lean_unbox(v___x_3483_);
v___x_15769__boxed_3519_ = lean_unbox(v___x_3484_);
v_sz_boxed_3520_ = lean_unbox_usize(v_sz_3497_);
lean_dec(v_sz_3497_);
v___x_15778__boxed_3521_ = lean_unbox_usize(v___x_3498_);
lean_dec(v___x_3498_);
v_res_3522_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3480_, v___x_3481_, v___x_15767__boxed_3517_, v___x_15768__boxed_3518_, v___x_15769__boxed_3519_, v_is_3485_, v___x_3486_, v___x_3487_, v___x_3488_, v___x_3489_, v_params_3490_, v___x_3491_, v___x_3492_, v_heq_3493_, v_val_3494_, v_tail_3495_, v_alts_3496_, v_sz_boxed_3520_, v___x_15778__boxed_3521_, v___x_3499_, v___x_3500_, v_declName_3501_, v_levelParams_3502_, v_numIndices_3503_, v___x_3504_, v___x_3505_, v_numParams_3506_, v_snd_3507_, v___x_3508_, v___x_3509_, v_ism1_x27_3510_, v_x_3511_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec_ref(v_x_3511_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3523_, lean_object* v___x_3524_, lean_object* v_motive_3525_, lean_object* v___x_3526_, uint8_t v___x_3527_, uint8_t v___x_3528_, uint8_t v___x_3529_, lean_object* v_is_3530_, lean_object* v___x_3531_, lean_object* v___x_3532_, lean_object* v___x_3533_, lean_object* v___x_3534_, lean_object* v_params_3535_, lean_object* v___x_3536_, lean_object* v___x_3537_, lean_object* v_heq_3538_, lean_object* v_val_3539_, lean_object* v_tail_3540_, size_t v_sz_3541_, size_t v___x_3542_, lean_object* v___x_3543_, lean_object* v___x_3544_, lean_object* v_declName_3545_, lean_object* v_levelParams_3546_, lean_object* v___x_3547_, lean_object* v___x_3548_, lean_object* v_numParams_3549_, lean_object* v_snd_3550_, lean_object* v___x_3551_, lean_object* v_alts_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___f_3565_; lean_object* v___x_3566_; 
v___x_3558_ = lean_nat_add(v_numIndices_3523_, v___x_3524_);
v___x_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3558_);
v___x_3560_ = lean_box(v___x_3527_);
v___x_3561_ = lean_box(v___x_3528_);
v___x_3562_ = lean_box(v___x_3529_);
v___x_3563_ = lean_box_usize(v_sz_3541_);
v___x_3564_ = lean_box_usize(v___x_3542_);
lean_inc_ref(v___x_3559_);
lean_inc_ref(v___x_3551_);
v___f_3565_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3565_, 0, v_motive_3525_);
lean_closure_set(v___f_3565_, 1, v___x_3526_);
lean_closure_set(v___f_3565_, 2, v___x_3560_);
lean_closure_set(v___f_3565_, 3, v___x_3561_);
lean_closure_set(v___f_3565_, 4, v___x_3562_);
lean_closure_set(v___f_3565_, 5, v_is_3530_);
lean_closure_set(v___f_3565_, 6, v___x_3531_);
lean_closure_set(v___f_3565_, 7, v___x_3532_);
lean_closure_set(v___f_3565_, 8, v___x_3533_);
lean_closure_set(v___f_3565_, 9, v___x_3534_);
lean_closure_set(v___f_3565_, 10, v_params_3535_);
lean_closure_set(v___f_3565_, 11, v___x_3536_);
lean_closure_set(v___f_3565_, 12, v___x_3537_);
lean_closure_set(v___f_3565_, 13, v_heq_3538_);
lean_closure_set(v___f_3565_, 14, v_val_3539_);
lean_closure_set(v___f_3565_, 15, v_tail_3540_);
lean_closure_set(v___f_3565_, 16, v_alts_3552_);
lean_closure_set(v___f_3565_, 17, v___x_3563_);
lean_closure_set(v___f_3565_, 18, v___x_3564_);
lean_closure_set(v___f_3565_, 19, v___x_3543_);
lean_closure_set(v___f_3565_, 20, v___x_3544_);
lean_closure_set(v___f_3565_, 21, v_declName_3545_);
lean_closure_set(v___f_3565_, 22, v_levelParams_3546_);
lean_closure_set(v___f_3565_, 23, v_numIndices_3523_);
lean_closure_set(v___f_3565_, 24, v___x_3547_);
lean_closure_set(v___f_3565_, 25, v___x_3548_);
lean_closure_set(v___f_3565_, 26, v_numParams_3549_);
lean_closure_set(v___f_3565_, 27, v_snd_3550_);
lean_closure_set(v___f_3565_, 28, v___x_3551_);
lean_closure_set(v___f_3565_, 29, v___x_3559_);
v___x_3566_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3551_, v___x_3559_, v___f_3565_, v___x_3527_, v___x_3527_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3567_ = _args[0];
lean_object* v___x_3568_ = _args[1];
lean_object* v_motive_3569_ = _args[2];
lean_object* v___x_3570_ = _args[3];
lean_object* v___x_3571_ = _args[4];
lean_object* v___x_3572_ = _args[5];
lean_object* v___x_3573_ = _args[6];
lean_object* v_is_3574_ = _args[7];
lean_object* v___x_3575_ = _args[8];
lean_object* v___x_3576_ = _args[9];
lean_object* v___x_3577_ = _args[10];
lean_object* v___x_3578_ = _args[11];
lean_object* v_params_3579_ = _args[12];
lean_object* v___x_3580_ = _args[13];
lean_object* v___x_3581_ = _args[14];
lean_object* v_heq_3582_ = _args[15];
lean_object* v_val_3583_ = _args[16];
lean_object* v_tail_3584_ = _args[17];
lean_object* v_sz_3585_ = _args[18];
lean_object* v___x_3586_ = _args[19];
lean_object* v___x_3587_ = _args[20];
lean_object* v___x_3588_ = _args[21];
lean_object* v_declName_3589_ = _args[22];
lean_object* v_levelParams_3590_ = _args[23];
lean_object* v___x_3591_ = _args[24];
lean_object* v___x_3592_ = _args[25];
lean_object* v_numParams_3593_ = _args[26];
lean_object* v_snd_3594_ = _args[27];
lean_object* v___x_3595_ = _args[28];
lean_object* v_alts_3596_ = _args[29];
lean_object* v___y_3597_ = _args[30];
lean_object* v___y_3598_ = _args[31];
lean_object* v___y_3599_ = _args[32];
lean_object* v___y_3600_ = _args[33];
lean_object* v___y_3601_ = _args[34];
_start:
{
uint8_t v___x_15860__boxed_3602_; uint8_t v___x_15861__boxed_3603_; uint8_t v___x_15862__boxed_3604_; size_t v_sz_boxed_3605_; size_t v___x_15871__boxed_3606_; lean_object* v_res_3607_; 
v___x_15860__boxed_3602_ = lean_unbox(v___x_3571_);
v___x_15861__boxed_3603_ = lean_unbox(v___x_3572_);
v___x_15862__boxed_3604_ = lean_unbox(v___x_3573_);
v_sz_boxed_3605_ = lean_unbox_usize(v_sz_3585_);
lean_dec(v_sz_3585_);
v___x_15871__boxed_3606_ = lean_unbox_usize(v___x_3586_);
lean_dec(v___x_3586_);
v_res_3607_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3567_, v___x_3568_, v_motive_3569_, v___x_3570_, v___x_15860__boxed_3602_, v___x_15861__boxed_3603_, v___x_15862__boxed_3604_, v_is_3574_, v___x_3575_, v___x_3576_, v___x_3577_, v___x_3578_, v_params_3579_, v___x_3580_, v___x_3581_, v_heq_3582_, v_val_3583_, v_tail_3584_, v_sz_boxed_3605_, v___x_15871__boxed_3606_, v___x_3587_, v___x_3588_, v_declName_3589_, v_levelParams_3590_, v___x_3591_, v___x_3592_, v_numParams_3593_, v_snd_3594_, v___x_3595_, v_alts_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec_ref(v___y_3597_);
lean_dec(v___x_3568_);
return v_res_3607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3608_, lean_object* v_declInfos_3609_, lean_object* v_k_3610_, lean_object* v_kind_3611_, lean_object* v_x_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
uint8_t v_kind_boxed_3618_; lean_object* v_res_3619_; 
v_kind_boxed_3618_ = lean_unbox(v_kind_3611_);
v_res_3619_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3608_, v_declInfos_3609_, v_k_3610_, v_kind_boxed_3618_, v_x_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
return v_res_3619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3620_, lean_object* v_k_3621_, uint8_t v_kind_3622_, lean_object* v_acc_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___x_3629_; lean_object* v_toApplicative_3630_; lean_object* v_toFunctor_3631_; lean_object* v_toSeq_3632_; lean_object* v_toSeqLeft_3633_; lean_object* v_toSeqRight_3634_; lean_object* v___f_3635_; lean_object* v___f_3636_; lean_object* v___f_3637_; lean_object* v___f_3638_; lean_object* v___x_3639_; lean_object* v___f_3640_; lean_object* v___f_3641_; lean_object* v___f_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v_toApplicative_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3704_; 
v___x_3629_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3630_ = lean_ctor_get(v___x_3629_, 0);
v_toFunctor_3631_ = lean_ctor_get(v_toApplicative_3630_, 0);
v_toSeq_3632_ = lean_ctor_get(v_toApplicative_3630_, 2);
v_toSeqLeft_3633_ = lean_ctor_get(v_toApplicative_3630_, 3);
v_toSeqRight_3634_ = lean_ctor_get(v_toApplicative_3630_, 4);
v___f_3635_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3636_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3631_, 2);
v___f_3637_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3637_, 0, v_toFunctor_3631_);
v___f_3638_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3638_, 0, v_toFunctor_3631_);
v___x_3639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___f_3637_);
lean_ctor_set(v___x_3639_, 1, v___f_3638_);
lean_inc(v_toSeqRight_3634_);
v___f_3640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3640_, 0, v_toSeqRight_3634_);
lean_inc(v_toSeqLeft_3633_);
v___f_3641_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3641_, 0, v_toSeqLeft_3633_);
lean_inc(v_toSeq_3632_);
v___f_3642_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3642_, 0, v_toSeq_3632_);
v___x_3643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3639_);
lean_ctor_set(v___x_3643_, 1, v___f_3635_);
lean_ctor_set(v___x_3643_, 2, v___f_3642_);
lean_ctor_set(v___x_3643_, 3, v___f_3641_);
lean_ctor_set(v___x_3643_, 4, v___f_3640_);
v___x_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
lean_ctor_set(v___x_3644_, 1, v___f_3636_);
v___x_3645_ = l_StateRefT_x27_instMonad___redArg(v___x_3644_);
v_toApplicative_3646_ = lean_ctor_get(v___x_3645_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3645_);
if (v_isSharedCheck_3704_ == 0)
{
lean_object* v_unused_3705_; 
v_unused_3705_ = lean_ctor_get(v___x_3645_, 1);
lean_dec(v_unused_3705_);
v___x_3648_ = v___x_3645_;
v_isShared_3649_ = v_isSharedCheck_3704_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_toApplicative_3646_);
lean_dec(v___x_3645_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3704_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v_toFunctor_3650_; lean_object* v_toSeq_3651_; lean_object* v_toSeqLeft_3652_; lean_object* v_toSeqRight_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3702_; 
v_toFunctor_3650_ = lean_ctor_get(v_toApplicative_3646_, 0);
v_toSeq_3651_ = lean_ctor_get(v_toApplicative_3646_, 2);
v_toSeqLeft_3652_ = lean_ctor_get(v_toApplicative_3646_, 3);
v_toSeqRight_3653_ = lean_ctor_get(v_toApplicative_3646_, 4);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_toApplicative_3646_);
if (v_isSharedCheck_3702_ == 0)
{
lean_object* v_unused_3703_; 
v_unused_3703_ = lean_ctor_get(v_toApplicative_3646_, 1);
lean_dec(v_unused_3703_);
v___x_3655_ = v_toApplicative_3646_;
v_isShared_3656_ = v_isSharedCheck_3702_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_toSeqRight_3653_);
lean_inc(v_toSeqLeft_3652_);
lean_inc(v_toSeq_3651_);
lean_inc(v_toFunctor_3650_);
lean_dec(v_toApplicative_3646_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3702_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___f_3657_; lean_object* v___f_3658_; lean_object* v___f_3659_; lean_object* v___f_3660_; lean_object* v___x_3661_; lean_object* v___f_3662_; lean_object* v___f_3663_; lean_object* v___f_3664_; lean_object* v___x_3666_; 
v___f_3657_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3658_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3650_);
v___f_3659_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3659_, 0, v_toFunctor_3650_);
v___f_3660_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3660_, 0, v_toFunctor_3650_);
v___x_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___f_3659_);
lean_ctor_set(v___x_3661_, 1, v___f_3660_);
v___f_3662_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3662_, 0, v_toSeqRight_3653_);
v___f_3663_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3663_, 0, v_toSeqLeft_3652_);
v___f_3664_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3664_, 0, v_toSeq_3651_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 4, v___f_3662_);
lean_ctor_set(v___x_3655_, 3, v___f_3663_);
lean_ctor_set(v___x_3655_, 2, v___f_3664_);
lean_ctor_set(v___x_3655_, 1, v___f_3657_);
lean_ctor_set(v___x_3655_, 0, v___x_3661_);
v___x_3666_ = v___x_3655_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v___f_3657_);
lean_ctor_set(v_reuseFailAlloc_3701_, 2, v___f_3664_);
lean_ctor_set(v_reuseFailAlloc_3701_, 3, v___f_3663_);
lean_ctor_set(v_reuseFailAlloc_3701_, 4, v___f_3662_);
v___x_3666_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3668_; 
if (v_isShared_3649_ == 0)
{
lean_ctor_set(v___x_3648_, 1, v___f_3658_);
lean_ctor_set(v___x_3648_, 0, v___x_3666_);
v___x_3668_ = v___x_3648_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___x_3666_);
lean_ctor_set(v_reuseFailAlloc_3700_, 1, v___f_3658_);
v___x_3668_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3669_ = lean_array_get_size(v_acc_3623_);
v___x_3670_ = lean_array_get_size(v_declInfos_3620_);
v___x_3671_ = lean_nat_dec_lt(v___x_3669_, v___x_3670_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; 
lean_dec_ref(v___x_3668_);
lean_dec_ref(v_declInfos_3620_);
lean_inc(v___y_3627_);
lean_inc_ref(v___y_3626_);
lean_inc(v___y_3625_);
lean_inc_ref(v___y_3624_);
v___x_3672_ = lean_apply_6(v_k_3621_, v_acc_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, lean_box(0));
return v___x_3672_;
}
else
{
lean_object* v___x_3673_; uint8_t v___x_3674_; lean_object* v___x_3675_; lean_object* v___f_3676_; lean_object* v___f_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v_snd_3682_; lean_object* v_fst_3683_; lean_object* v_fst_3684_; lean_object* v_snd_3685_; lean_object* v___x_3686_; 
v___x_3673_ = lean_box(0);
v___x_3674_ = 0;
v___x_3675_ = l_Lean_instInhabitedExpr;
v___f_3676_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3676_, 0, v___x_3668_);
lean_closure_set(v___f_3676_, 1, v___x_3675_);
v___f_3677_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3677_, 0, v___f_3676_);
v___x_3678_ = lean_box(v___x_3674_);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
lean_ctor_set(v___x_3679_, 1, v___f_3677_);
v___x_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3673_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___x_3681_ = lean_array_get(v___x_3680_, v_declInfos_3620_, v___x_3669_);
lean_dec_ref_known(v___x_3680_, 2);
v_snd_3682_ = lean_ctor_get(v___x_3681_, 1);
lean_inc(v_snd_3682_);
v_fst_3683_ = lean_ctor_get(v___x_3681_, 0);
lean_inc(v_fst_3683_);
lean_dec(v___x_3681_);
v_fst_3684_ = lean_ctor_get(v_snd_3682_, 0);
lean_inc(v_fst_3684_);
v_snd_3685_ = lean_ctor_get(v_snd_3682_, 1);
lean_inc(v_snd_3685_);
lean_dec(v_snd_3682_);
lean_inc(v___y_3627_);
lean_inc_ref(v___y_3626_);
lean_inc(v___y_3625_);
lean_inc_ref(v___y_3624_);
lean_inc_ref(v_acc_3623_);
v___x_3686_ = lean_apply_6(v_snd_3685_, v_acc_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, lean_box(0));
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3688_; lean_object* v___f_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref_known(v___x_3686_, 1);
v___x_3688_ = lean_box(v_kind_3622_);
v___f_3689_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3689_, 0, v_acc_3623_);
lean_closure_set(v___f_3689_, 1, v_declInfos_3620_);
lean_closure_set(v___f_3689_, 2, v_k_3621_);
lean_closure_set(v___f_3689_, 3, v___x_3688_);
v___x_3690_ = lean_unbox(v_fst_3684_);
lean_dec(v_fst_3684_);
v___x_3691_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3683_, v___x_3690_, v_a_3687_, v___f_3689_, v_kind_3622_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
return v___x_3691_;
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec(v_fst_3684_);
lean_dec(v_fst_3683_);
lean_dec_ref(v_acc_3623_);
lean_dec_ref(v_k_3621_);
lean_dec_ref(v_declInfos_3620_);
v_a_3692_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3686_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3686_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3706_, lean_object* v_declInfos_3707_, lean_object* v_k_3708_, uint8_t v_kind_3709_, lean_object* v_x_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = lean_array_push(v_acc_3706_, v_x_3710_);
v___x_3717_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3707_, v_k_3708_, v_kind_3709_, v___x_3716_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3718_, lean_object* v_k_3719_, lean_object* v_kind_3720_, lean_object* v_acc_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
uint8_t v_kind_boxed_3727_; lean_object* v_res_3728_; 
v_kind_boxed_3727_ = lean_unbox(v_kind_3720_);
v_res_3728_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3718_, v_k_3719_, v_kind_boxed_3727_, v_acc_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec(v___y_3723_);
lean_dec_ref(v___y_3722_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3729_, lean_object* v_k_3730_, uint8_t v_kind_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3737_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3738_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3729_, v_k_3730_, v_kind_3731_, v___x_3737_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3739_, lean_object* v_k_3740_, lean_object* v_kind_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
uint8_t v_kind_boxed_3747_; lean_object* v_res_3748_; 
v_kind_boxed_3747_ = lean_unbox(v_kind_3741_);
v_res_3748_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3739_, v_k_3740_, v_kind_boxed_3747_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3749_, lean_object* v_k_3750_, uint8_t v_kind_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
size_t v_sz_3757_; size_t v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v_sz_3757_ = lean_array_size(v_declInfos_3749_);
v___x_3758_ = ((size_t)0ULL);
v___x_3759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3757_, v___x_3758_, v_declInfos_3749_);
v___x_3760_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3759_, v_k_3750_, v_kind_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3761_, lean_object* v_k_3762_, lean_object* v_kind_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
uint8_t v_kind_boxed_3769_; lean_object* v_res_3770_; 
v_kind_boxed_3769_ = lean_unbox(v_kind_3763_);
v_res_3770_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3761_, v_k_3762_, v_kind_boxed_3769_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3771_, lean_object* v_k_3772_, uint8_t v_kind_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
size_t v_sz_3779_; size_t v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v_sz_3779_ = lean_array_size(v_declInfos_3771_);
v___x_3780_ = ((size_t)0ULL);
v___x_3781_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3779_, v___x_3780_, v_declInfos_3771_);
v___x_3782_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3781_, v_k_3772_, v_kind_3773_, v___y_3774_, v___y_3775_, v___y_3776_, v___y_3777_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3783_, lean_object* v_k_3784_, lean_object* v_kind_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
uint8_t v_kind_boxed_3791_; lean_object* v_res_3792_; 
v_kind_boxed_3791_ = lean_unbox(v_kind_3785_);
v_res_3792_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3783_, v_k_3784_, v_kind_boxed_3791_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
return v_res_3792_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; 
v___x_3795_ = lean_box(0);
v___x_3796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3797_ = l_Lean_mkConst(v___x_3796_, v___x_3795_);
return v___x_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3798_, lean_object* v___x_3799_, lean_object* v_motive_3800_, uint8_t v___x_3801_, uint8_t v___x_3802_, uint8_t v___x_3803_, lean_object* v___x_3804_, lean_object* v_v_3805_, lean_object* v___x_3806_, lean_object* v_zs12_3807_, lean_object* v_is_3808_, lean_object* v_fields1_3809_, lean_object* v_fields2_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v_e_3826_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
lean_inc(v___x_3798_);
v___x_3836_ = l_Lean_mkNatLit(v___x_3798_);
v___x_3837_ = l_Lean_Meta_mkEqRefl(v___x_3836_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3837_, 1);
lean_inc_ref(v___x_3799_);
v___x_3839_ = l_Lean_mkAppN(v___x_3799_, v_fields1_3809_);
v___x_3840_ = l_Lean_mkAppN(v___x_3799_, v_fields2_3810_);
v___x_3841_ = lean_unsigned_to_nat(3u);
v___x_3842_ = lean_mk_empty_array_with_capacity(v___x_3841_);
v___x_3843_ = lean_array_push(v___x_3842_, v___x_3839_);
v___x_3844_ = lean_array_push(v___x_3843_, v___x_3840_);
v___x_3845_ = lean_array_push(v___x_3844_, v_a_3838_);
v___x_3846_ = l_Array_append___redArg(v_is_3808_, v___x_3845_);
lean_dec_ref(v___x_3845_);
v___x_3847_ = l_Lean_mkAppN(v_motive_3800_, v___x_3846_);
lean_dec_ref(v___x_3846_);
v___x_3848_ = l_Lean_Meta_mkForallFVars(v_zs12_3807_, v___x_3847_, v___x_3801_, v___x_3802_, v___x_3802_, v___x_3803_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3848_, 1);
v___x_3850_ = lean_array_get_size(v_zs12_3807_);
v___x_3851_ = lean_nat_dec_eq(v___x_3850_, v___x_3804_);
if (v___x_3851_ == 0)
{
v_e_3826_ = v_a_3849_;
goto v___jp_3825_;
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3853_ = l_Lean_mkArrow(v___x_3852_, v_a_3849_, v___y_3813_, v___y_3814_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
v_e_3826_ = v_a_3854_;
goto v___jp_3825_;
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
lean_dec(v_v_3805_);
lean_dec(v___x_3804_);
lean_dec(v___x_3798_);
v_a_3855_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___x_3853_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3853_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
else
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec(v_v_3805_);
lean_dec(v___x_3804_);
lean_dec(v___x_3798_);
v_a_3863_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3848_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3848_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
else
{
lean_object* v_a_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3878_; 
lean_dec_ref(v_is_3808_);
lean_dec(v_v_3805_);
lean_dec(v___x_3804_);
lean_dec_ref(v_motive_3800_);
lean_dec_ref(v___x_3799_);
lean_dec(v___x_3798_);
v_a_3871_ = lean_ctor_get(v___x_3837_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3837_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3873_ = v___x_3837_;
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_a_3871_);
lean_dec(v___x_3837_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3878_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3876_; 
if (v_isShared_3874_ == 0)
{
v___x_3876_ = v___x_3873_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v_a_3871_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
v___jp_3816_:
{
lean_object* v___x_3819_; uint8_t v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3819_ = lean_array_get_size(v_zs12_3807_);
v___x_3820_ = lean_nat_dec_eq(v___x_3819_, v___x_3804_);
v___x_3821_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3821_, 0, v___x_3819_);
lean_ctor_set(v___x_3821_, 1, v___x_3804_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*2, v___x_3820_);
v___x_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___y_3818_);
lean_ctor_set(v___x_3822_, 1, v___y_3817_);
v___x_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
lean_ctor_set(v___x_3823_, 1, v___x_3821_);
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3823_);
return v___x_3824_;
}
v___jp_3825_:
{
if (lean_obj_tag(v_v_3805_) == 1)
{
lean_object* v_str_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
lean_dec(v___x_3798_);
v_str_3827_ = lean_ctor_get(v_v_3805_, 1);
lean_inc_ref(v_str_3827_);
lean_dec_ref_known(v_v_3805_, 2);
v___x_3828_ = lean_box(0);
v___x_3829_ = l_Lean_Name_str___override(v___x_3828_, v_str_3827_);
v___y_3817_ = v_e_3826_;
v___y_3818_ = v___x_3829_;
goto v___jp_3816_;
}
else
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
lean_dec(v_v_3805_);
v___x_3830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3831_ = lean_nat_add(v___x_3798_, v___x_3806_);
lean_dec(v___x_3798_);
v___x_3832_ = l_Nat_reprFast(v___x_3831_);
v___x_3833_ = lean_string_append(v___x_3830_, v___x_3832_);
lean_dec_ref(v___x_3832_);
v___x_3834_ = lean_box(0);
v___x_3835_ = l_Lean_Name_str___override(v___x_3834_, v___x_3833_);
v___y_3817_ = v_e_3826_;
v___y_3818_ = v___x_3835_;
goto v___jp_3816_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3879_ = _args[0];
lean_object* v___x_3880_ = _args[1];
lean_object* v_motive_3881_ = _args[2];
lean_object* v___x_3882_ = _args[3];
lean_object* v___x_3883_ = _args[4];
lean_object* v___x_3884_ = _args[5];
lean_object* v___x_3885_ = _args[6];
lean_object* v_v_3886_ = _args[7];
lean_object* v___x_3887_ = _args[8];
lean_object* v_zs12_3888_ = _args[9];
lean_object* v_is_3889_ = _args[10];
lean_object* v_fields1_3890_ = _args[11];
lean_object* v_fields2_3891_ = _args[12];
lean_object* v___y_3892_ = _args[13];
lean_object* v___y_3893_ = _args[14];
lean_object* v___y_3894_ = _args[15];
lean_object* v___y_3895_ = _args[16];
lean_object* v___y_3896_ = _args[17];
_start:
{
uint8_t v___x_16205__boxed_3897_; uint8_t v___x_16206__boxed_3898_; uint8_t v___x_16207__boxed_3899_; lean_object* v_res_3900_; 
v___x_16205__boxed_3897_ = lean_unbox(v___x_3882_);
v___x_16206__boxed_3898_ = lean_unbox(v___x_3883_);
v___x_16207__boxed_3899_ = lean_unbox(v___x_3884_);
v_res_3900_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3879_, v___x_3880_, v_motive_3881_, v___x_16205__boxed_3897_, v___x_16206__boxed_3898_, v___x_16207__boxed_3899_, v___x_3885_, v_v_3886_, v___x_3887_, v_zs12_3888_, v_is_3889_, v_fields1_3890_, v_fields2_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec_ref(v_fields2_3891_);
lean_dec_ref(v_fields1_3890_);
lean_dec_ref(v_zs12_3888_);
lean_dec(v___x_3887_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3901_, lean_object* v_params_3902_, lean_object* v_motive_3903_, size_t v_sz_3904_, size_t v_i_3905_, lean_object* v_bs_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
uint8_t v___x_3912_; 
v___x_3912_ = lean_usize_dec_lt(v_i_3905_, v_sz_3904_);
if (v___x_3912_ == 0)
{
lean_object* v___x_3913_; 
lean_dec_ref(v_motive_3903_);
lean_dec(v_tail_3901_);
v___x_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3913_, 0, v_bs_3906_);
return v___x_3913_;
}
else
{
lean_object* v___x_3914_; lean_object* v___x_3915_; uint8_t v___x_3916_; uint8_t v___x_3917_; lean_object* v_v_3918_; lean_object* v_bs_x27_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___f_3926_; lean_object* v___x_3927_; 
v___x_3914_ = lean_unsigned_to_nat(0u);
v___x_3915_ = lean_unsigned_to_nat(1u);
v___x_3916_ = 0;
v___x_3917_ = 1;
v_v_3918_ = lean_array_uget(v_bs_3906_, v_i_3905_);
v_bs_x27_3919_ = lean_array_uset(v_bs_3906_, v_i_3905_, v___x_3914_);
v___x_3920_ = lean_usize_to_nat(v_i_3905_);
lean_inc(v_tail_3901_);
lean_inc(v_v_3918_);
v___x_3921_ = l_Lean_mkConst(v_v_3918_, v_tail_3901_);
v___x_3922_ = l_Lean_mkAppN(v___x_3921_, v_params_3902_);
v___x_3923_ = lean_box(v___x_3916_);
v___x_3924_ = lean_box(v___x_3912_);
v___x_3925_ = lean_box(v___x_3917_);
lean_inc_ref(v_motive_3903_);
lean_inc_ref(v___x_3922_);
v___f_3926_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3926_, 0, v___x_3920_);
lean_closure_set(v___f_3926_, 1, v___x_3922_);
lean_closure_set(v___f_3926_, 2, v_motive_3903_);
lean_closure_set(v___f_3926_, 3, v___x_3923_);
lean_closure_set(v___f_3926_, 4, v___x_3924_);
lean_closure_set(v___f_3926_, 5, v___x_3925_);
lean_closure_set(v___f_3926_, 6, v___x_3914_);
lean_closure_set(v___f_3926_, 7, v_v_3918_);
lean_closure_set(v___f_3926_, 8, v___x_3915_);
v___x_3927_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3922_, v___f_3926_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; size_t v___x_3929_; size_t v___x_3930_; lean_object* v___x_3931_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_a_3928_);
lean_dec_ref_known(v___x_3927_, 1);
v___x_3929_ = ((size_t)1ULL);
v___x_3930_ = lean_usize_add(v_i_3905_, v___x_3929_);
v___x_3931_ = lean_array_uset(v_bs_x27_3919_, v_i_3905_, v_a_3928_);
v_i_3905_ = v___x_3930_;
v_bs_3906_ = v___x_3931_;
goto _start;
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec_ref(v_bs_x27_3919_);
lean_dec_ref(v_motive_3903_);
lean_dec(v_tail_3901_);
v_a_3933_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3927_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3927_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3941_, lean_object* v_params_3942_, lean_object* v_motive_3943_, lean_object* v_sz_3944_, lean_object* v_i_3945_, lean_object* v_bs_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
size_t v_sz_boxed_3952_; size_t v_i_boxed_3953_; lean_object* v_res_3954_; 
v_sz_boxed_3952_ = lean_unbox_usize(v_sz_3944_);
lean_dec(v_sz_3944_);
v_i_boxed_3953_ = lean_unbox_usize(v_i_3945_);
lean_dec(v_i_3945_);
v_res_3954_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3941_, v_params_3942_, v_motive_3943_, v_sz_boxed_3952_, v_i_boxed_3953_, v_bs_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec_ref(v_params_3942_);
return v_res_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3957_, lean_object* v_tail_3958_, lean_object* v_params_3959_, lean_object* v_numIndices_3960_, lean_object* v___x_3961_, lean_object* v___x_3962_, uint8_t v___x_3963_, uint8_t v___x_3964_, uint8_t v___x_3965_, lean_object* v_is_3966_, lean_object* v___x_3967_, lean_object* v___x_3968_, lean_object* v___x_3969_, lean_object* v___x_3970_, lean_object* v___x_3971_, lean_object* v___x_3972_, lean_object* v_heq_3973_, lean_object* v_val_3974_, lean_object* v___x_3975_, lean_object* v_declName_3976_, lean_object* v_levelParams_3977_, lean_object* v___x_3978_, lean_object* v___x_3979_, lean_object* v_numParams_3980_, lean_object* v___x_3981_, lean_object* v_motive_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v___x_3988_; size_t v_sz_3989_; size_t v___x_3990_; lean_object* v___x_3991_; 
v___x_3988_ = lean_array_mk(v_ctors_3957_);
v_sz_3989_ = lean_array_size(v___x_3988_);
v___x_3990_ = ((size_t)0ULL);
lean_inc_ref(v___x_3988_);
lean_inc_ref(v_motive_3982_);
lean_inc(v_tail_3958_);
v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3958_, v_params_3959_, v_motive_3982_, v_sz_3989_, v___x_3990_, v___x_3988_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v___x_3993_; lean_object* v_fst_3994_; lean_object* v_snd_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___f_4001_; uint8_t v___x_4002_; lean_object* v___x_4003_; 
v_a_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_a_3992_);
lean_dec_ref_known(v___x_3991_, 1);
v___x_3993_ = l_Array_unzip___redArg(v_a_3992_);
lean_dec(v_a_3992_);
v_fst_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_fst_3994_);
v_snd_3995_ = lean_ctor_get(v___x_3993_, 1);
lean_inc(v_snd_3995_);
lean_dec_ref(v___x_3993_);
v___x_3996_ = lean_box(v___x_3963_);
v___x_3997_ = lean_box(v___x_3964_);
v___x_3998_ = lean_box(v___x_3965_);
v___x_3999_ = lean_box_usize(v_sz_3989_);
v___x_4000_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4001_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4001_, 0, v_numIndices_3960_);
lean_closure_set(v___f_4001_, 1, v___x_3961_);
lean_closure_set(v___f_4001_, 2, v_motive_3982_);
lean_closure_set(v___f_4001_, 3, v___x_3962_);
lean_closure_set(v___f_4001_, 4, v___x_3996_);
lean_closure_set(v___f_4001_, 5, v___x_3997_);
lean_closure_set(v___f_4001_, 6, v___x_3998_);
lean_closure_set(v___f_4001_, 7, v_is_3966_);
lean_closure_set(v___f_4001_, 8, v___x_3967_);
lean_closure_set(v___f_4001_, 9, v___x_3968_);
lean_closure_set(v___f_4001_, 10, v___x_3969_);
lean_closure_set(v___f_4001_, 11, v___x_3970_);
lean_closure_set(v___f_4001_, 12, v_params_3959_);
lean_closure_set(v___f_4001_, 13, v___x_3971_);
lean_closure_set(v___f_4001_, 14, v___x_3972_);
lean_closure_set(v___f_4001_, 15, v_heq_3973_);
lean_closure_set(v___f_4001_, 16, v_val_3974_);
lean_closure_set(v___f_4001_, 17, v_tail_3958_);
lean_closure_set(v___f_4001_, 18, v___x_3999_);
lean_closure_set(v___f_4001_, 19, v___x_4000_);
lean_closure_set(v___f_4001_, 20, v___x_3988_);
lean_closure_set(v___f_4001_, 21, v___x_3975_);
lean_closure_set(v___f_4001_, 22, v_declName_3976_);
lean_closure_set(v___f_4001_, 23, v_levelParams_3977_);
lean_closure_set(v___f_4001_, 24, v___x_3978_);
lean_closure_set(v___f_4001_, 25, v___x_3979_);
lean_closure_set(v___f_4001_, 26, v_numParams_3980_);
lean_closure_set(v___f_4001_, 27, v_snd_3995_);
lean_closure_set(v___f_4001_, 28, v___x_3981_);
v___x_4002_ = 0;
v___x_4003_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_3994_, v___f_4001_, v___x_4002_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
return v___x_4003_;
}
else
{
lean_object* v_a_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4011_; 
lean_dec_ref(v___x_3988_);
lean_dec_ref(v_motive_3982_);
lean_dec_ref(v___x_3981_);
lean_dec(v_numParams_3980_);
lean_dec(v___x_3979_);
lean_dec(v___x_3978_);
lean_dec(v_levelParams_3977_);
lean_dec(v_declName_3976_);
lean_dec_ref(v___x_3975_);
lean_dec_ref(v_val_3974_);
lean_dec_ref(v_heq_3973_);
lean_dec_ref(v___x_3972_);
lean_dec_ref(v___x_3971_);
lean_dec(v___x_3970_);
lean_dec(v___x_3969_);
lean_dec_ref(v___x_3968_);
lean_dec_ref(v___x_3967_);
lean_dec_ref(v_is_3966_);
lean_dec_ref(v___x_3962_);
lean_dec(v___x_3961_);
lean_dec(v_numIndices_3960_);
lean_dec_ref(v_params_3959_);
lean_dec(v_tail_3958_);
v_a_4004_ = lean_ctor_get(v___x_3991_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3991_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_4006_ = v___x_3991_;
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_a_4004_);
lean_dec(v___x_3991_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4011_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4009_; 
if (v_isShared_4007_ == 0)
{
v___x_4009_ = v___x_4006_;
goto v_reusejp_4008_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
v___x_4009_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4008_;
}
v_reusejp_4008_:
{
return v___x_4009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4012_ = _args[0];
lean_object* v_tail_4013_ = _args[1];
lean_object* v_params_4014_ = _args[2];
lean_object* v_numIndices_4015_ = _args[3];
lean_object* v___x_4016_ = _args[4];
lean_object* v___x_4017_ = _args[5];
lean_object* v___x_4018_ = _args[6];
lean_object* v___x_4019_ = _args[7];
lean_object* v___x_4020_ = _args[8];
lean_object* v_is_4021_ = _args[9];
lean_object* v___x_4022_ = _args[10];
lean_object* v___x_4023_ = _args[11];
lean_object* v___x_4024_ = _args[12];
lean_object* v___x_4025_ = _args[13];
lean_object* v___x_4026_ = _args[14];
lean_object* v___x_4027_ = _args[15];
lean_object* v_heq_4028_ = _args[16];
lean_object* v_val_4029_ = _args[17];
lean_object* v___x_4030_ = _args[18];
lean_object* v_declName_4031_ = _args[19];
lean_object* v_levelParams_4032_ = _args[20];
lean_object* v___x_4033_ = _args[21];
lean_object* v___x_4034_ = _args[22];
lean_object* v_numParams_4035_ = _args[23];
lean_object* v___x_4036_ = _args[24];
lean_object* v_motive_4037_ = _args[25];
lean_object* v___y_4038_ = _args[26];
lean_object* v___y_4039_ = _args[27];
lean_object* v___y_4040_ = _args[28];
lean_object* v___y_4041_ = _args[29];
lean_object* v___y_4042_ = _args[30];
_start:
{
uint8_t v___x_16444__boxed_4043_; uint8_t v___x_16445__boxed_4044_; uint8_t v___x_16446__boxed_4045_; lean_object* v_res_4046_; 
v___x_16444__boxed_4043_ = lean_unbox(v___x_4018_);
v___x_16445__boxed_4044_ = lean_unbox(v___x_4019_);
v___x_16446__boxed_4045_ = lean_unbox(v___x_4020_);
v_res_4046_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4012_, v_tail_4013_, v_params_4014_, v_numIndices_4015_, v___x_4016_, v___x_4017_, v___x_16444__boxed_4043_, v___x_16445__boxed_4044_, v___x_16446__boxed_4045_, v_is_4021_, v___x_4022_, v___x_4023_, v___x_4024_, v___x_4025_, v___x_4026_, v___x_4027_, v_heq_4028_, v_val_4029_, v___x_4030_, v_declName_4031_, v_levelParams_4032_, v___x_4033_, v___x_4034_, v_numParams_4035_, v___x_4036_, v_motive_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v___y_4039_);
lean_dec_ref(v___y_4038_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4047_, lean_object* v___x_4048_, lean_object* v_is_4049_, lean_object* v_head_4050_, lean_object* v_ctors_4051_, lean_object* v_tail_4052_, lean_object* v_params_4053_, lean_object* v_numIndices_4054_, lean_object* v___x_4055_, lean_object* v___x_4056_, lean_object* v___x_4057_, lean_object* v___x_4058_, lean_object* v___x_4059_, lean_object* v_val_4060_, lean_object* v___x_4061_, lean_object* v_declName_4062_, lean_object* v_levelParams_4063_, lean_object* v___x_4064_, lean_object* v_numParams_4065_, lean_object* v___x_4066_, lean_object* v_heq_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; uint8_t v___x_4081_; uint8_t v___x_4082_; lean_object* v___x_4083_; 
v___x_4073_ = lean_unsigned_to_nat(3u);
v___x_4074_ = lean_mk_empty_array_with_capacity(v___x_4073_);
lean_inc_ref(v___x_4047_);
v___x_4075_ = lean_array_push(v___x_4074_, v___x_4047_);
lean_inc_ref(v___x_4048_);
v___x_4076_ = lean_array_push(v___x_4075_, v___x_4048_);
lean_inc_ref(v_heq_4067_);
v___x_4077_ = lean_array_push(v___x_4076_, v_heq_4067_);
lean_inc_ref(v_is_4049_);
v___x_4078_ = l_Array_append___redArg(v_is_4049_, v___x_4077_);
lean_dec_ref(v___x_4077_);
v___x_4079_ = l_Lean_mkSort(v_head_4050_);
v___x_4080_ = 0;
v___x_4081_ = 1;
v___x_4082_ = 1;
v___x_4083_ = l_Lean_Meta_mkForallFVars(v___x_4078_, v___x_4079_, v___x_4080_, v___x_4081_, v___x_4081_, v___x_4082_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___f_4088_; lean_object* v___x_4089_; uint8_t v___x_4090_; lean_object* v___x_4091_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4083_, 1);
v___x_4085_ = lean_box(v___x_4080_);
v___x_4086_ = lean_box(v___x_4081_);
v___x_4087_ = lean_box(v___x_4082_);
v___f_4088_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4088_, 0, v_ctors_4051_);
lean_closure_set(v___f_4088_, 1, v_tail_4052_);
lean_closure_set(v___f_4088_, 2, v_params_4053_);
lean_closure_set(v___f_4088_, 3, v_numIndices_4054_);
lean_closure_set(v___f_4088_, 4, v___x_4055_);
lean_closure_set(v___f_4088_, 5, v___x_4078_);
lean_closure_set(v___f_4088_, 6, v___x_4085_);
lean_closure_set(v___f_4088_, 7, v___x_4086_);
lean_closure_set(v___f_4088_, 8, v___x_4087_);
lean_closure_set(v___f_4088_, 9, v_is_4049_);
lean_closure_set(v___f_4088_, 10, v___x_4048_);
lean_closure_set(v___f_4088_, 11, v___x_4047_);
lean_closure_set(v___f_4088_, 12, v___x_4056_);
lean_closure_set(v___f_4088_, 13, v___x_4057_);
lean_closure_set(v___f_4088_, 14, v___x_4058_);
lean_closure_set(v___f_4088_, 15, v___x_4059_);
lean_closure_set(v___f_4088_, 16, v_heq_4067_);
lean_closure_set(v___f_4088_, 17, v_val_4060_);
lean_closure_set(v___f_4088_, 18, v___x_4061_);
lean_closure_set(v___f_4088_, 19, v_declName_4062_);
lean_closure_set(v___f_4088_, 20, v_levelParams_4063_);
lean_closure_set(v___f_4088_, 21, v___x_4073_);
lean_closure_set(v___f_4088_, 22, v___x_4064_);
lean_closure_set(v___f_4088_, 23, v_numParams_4065_);
lean_closure_set(v___f_4088_, 24, v___x_4066_);
v___x_4089_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4090_ = 0;
v___x_4091_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4089_, v___x_4082_, v_a_4084_, v___f_4088_, v___x_4090_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
return v___x_4091_;
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec_ref(v___x_4078_);
lean_dec_ref(v_heq_4067_);
lean_dec_ref(v___x_4066_);
lean_dec(v_numParams_4065_);
lean_dec(v___x_4064_);
lean_dec(v_levelParams_4063_);
lean_dec(v_declName_4062_);
lean_dec_ref(v___x_4061_);
lean_dec_ref(v_val_4060_);
lean_dec_ref(v___x_4059_);
lean_dec_ref(v___x_4058_);
lean_dec(v___x_4057_);
lean_dec(v___x_4056_);
lean_dec(v___x_4055_);
lean_dec(v_numIndices_4054_);
lean_dec_ref(v_params_4053_);
lean_dec(v_tail_4052_);
lean_dec(v_ctors_4051_);
lean_dec_ref(v_is_4049_);
lean_dec_ref(v___x_4048_);
lean_dec_ref(v___x_4047_);
v_a_4092_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4083_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4083_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4100_ = _args[0];
lean_object* v___x_4101_ = _args[1];
lean_object* v_is_4102_ = _args[2];
lean_object* v_head_4103_ = _args[3];
lean_object* v_ctors_4104_ = _args[4];
lean_object* v_tail_4105_ = _args[5];
lean_object* v_params_4106_ = _args[6];
lean_object* v_numIndices_4107_ = _args[7];
lean_object* v___x_4108_ = _args[8];
lean_object* v___x_4109_ = _args[9];
lean_object* v___x_4110_ = _args[10];
lean_object* v___x_4111_ = _args[11];
lean_object* v___x_4112_ = _args[12];
lean_object* v_val_4113_ = _args[13];
lean_object* v___x_4114_ = _args[14];
lean_object* v_declName_4115_ = _args[15];
lean_object* v_levelParams_4116_ = _args[16];
lean_object* v___x_4117_ = _args[17];
lean_object* v_numParams_4118_ = _args[18];
lean_object* v___x_4119_ = _args[19];
lean_object* v_heq_4120_ = _args[20];
lean_object* v___y_4121_ = _args[21];
lean_object* v___y_4122_ = _args[22];
lean_object* v___y_4123_ = _args[23];
lean_object* v___y_4124_ = _args[24];
lean_object* v___y_4125_ = _args[25];
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4100_, v___x_4101_, v_is_4102_, v_head_4103_, v_ctors_4104_, v_tail_4105_, v_params_4106_, v_numIndices_4107_, v___x_4108_, v___x_4109_, v___x_4110_, v___x_4111_, v___x_4112_, v_val_4113_, v___x_4114_, v_declName_4115_, v_levelParams_4116_, v___x_4117_, v_numParams_4118_, v___x_4119_, v_heq_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4127_, lean_object* v_x1_4128_, lean_object* v_indName_4129_, lean_object* v_tail_4130_, lean_object* v_params_4131_, lean_object* v_is_4132_, lean_object* v___x_4133_, lean_object* v_head_4134_, lean_object* v_ctors_4135_, lean_object* v_numIndices_4136_, lean_object* v___x_4137_, lean_object* v___x_4138_, lean_object* v_val_4139_, lean_object* v_declName_4140_, lean_object* v_levelParams_4141_, lean_object* v_numParams_4142_, lean_object* v___x_4143_, lean_object* v_x2_4144_, lean_object* v_x_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4151_ = lean_unsigned_to_nat(0u);
v___x_4152_ = lean_array_get_borrowed(v___x_4127_, v_x1_4128_, v___x_4151_);
v___x_4153_ = lean_array_get_borrowed(v___x_4127_, v_x2_4144_, v___x_4151_);
v___x_4154_ = l_Lean_mkCtorIdxName(v_indName_4129_);
lean_inc(v_tail_4130_);
v___x_4155_ = l_Lean_mkConst(v___x_4154_, v_tail_4130_);
lean_inc_ref(v_params_4131_);
v___x_4156_ = l_Array_append___redArg(v_params_4131_, v_is_4132_);
v___x_4157_ = lean_mk_empty_array_with_capacity(v___x_4133_);
lean_inc(v___x_4152_);
lean_inc_ref_n(v___x_4157_, 2);
v___x_4158_ = lean_array_push(v___x_4157_, v___x_4152_);
lean_inc_ref(v___x_4156_);
v___x_4159_ = l_Array_append___redArg(v___x_4156_, v___x_4158_);
lean_inc_ref(v___x_4155_);
v___x_4160_ = l_Lean_mkAppN(v___x_4155_, v___x_4159_);
lean_dec_ref(v___x_4159_);
lean_inc(v___x_4153_);
v___x_4161_ = lean_array_push(v___x_4157_, v___x_4153_);
v___x_4162_ = l_Array_append___redArg(v___x_4156_, v___x_4161_);
v___x_4163_ = l_Lean_mkAppN(v___x_4155_, v___x_4162_);
lean_dec_ref(v___x_4162_);
v___x_4164_ = l_Lean_Meta_mkEq(v___x_4160_, v___x_4163_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___f_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
lean_inc(v___x_4153_);
lean_inc(v___x_4152_);
v___f_4166_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4166_, 0, v___x_4152_);
lean_closure_set(v___f_4166_, 1, v___x_4153_);
lean_closure_set(v___f_4166_, 2, v_is_4132_);
lean_closure_set(v___f_4166_, 3, v_head_4134_);
lean_closure_set(v___f_4166_, 4, v_ctors_4135_);
lean_closure_set(v___f_4166_, 5, v_tail_4130_);
lean_closure_set(v___f_4166_, 6, v_params_4131_);
lean_closure_set(v___f_4166_, 7, v_numIndices_4136_);
lean_closure_set(v___f_4166_, 8, v___x_4133_);
lean_closure_set(v___f_4166_, 9, v___x_4137_);
lean_closure_set(v___f_4166_, 10, v___x_4138_);
lean_closure_set(v___f_4166_, 11, v___x_4158_);
lean_closure_set(v___f_4166_, 12, v___x_4161_);
lean_closure_set(v___f_4166_, 13, v_val_4139_);
lean_closure_set(v___f_4166_, 14, v___x_4157_);
lean_closure_set(v___f_4166_, 15, v_declName_4140_);
lean_closure_set(v___f_4166_, 16, v_levelParams_4141_);
lean_closure_set(v___f_4166_, 17, v___x_4151_);
lean_closure_set(v___f_4166_, 18, v_numParams_4142_);
lean_closure_set(v___f_4166_, 19, v___x_4143_);
v___x_4167_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4168_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4167_, v_a_4165_, v___f_4166_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4168_;
}
else
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4176_; 
lean_dec_ref(v___x_4161_);
lean_dec_ref(v___x_4158_);
lean_dec_ref(v___x_4157_);
lean_dec_ref(v___x_4143_);
lean_dec(v_numParams_4142_);
lean_dec(v_levelParams_4141_);
lean_dec(v_declName_4140_);
lean_dec_ref(v_val_4139_);
lean_dec(v___x_4138_);
lean_dec(v___x_4137_);
lean_dec(v_numIndices_4136_);
lean_dec(v_ctors_4135_);
lean_dec(v_head_4134_);
lean_dec(v___x_4133_);
lean_dec_ref(v_is_4132_);
lean_dec_ref(v_params_4131_);
lean_dec(v_tail_4130_);
v_a_4169_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4176_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4176_ == 0)
{
v___x_4171_ = v___x_4164_;
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4164_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4176_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v___x_4174_; 
if (v_isShared_4172_ == 0)
{
v___x_4174_ = v___x_4171_;
goto v_reusejp_4173_;
}
else
{
lean_object* v_reuseFailAlloc_4175_; 
v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
v___x_4174_ = v_reuseFailAlloc_4175_;
goto v_reusejp_4173_;
}
v_reusejp_4173_:
{
return v___x_4174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4177_ = _args[0];
lean_object* v_x1_4178_ = _args[1];
lean_object* v_indName_4179_ = _args[2];
lean_object* v_tail_4180_ = _args[3];
lean_object* v_params_4181_ = _args[4];
lean_object* v_is_4182_ = _args[5];
lean_object* v___x_4183_ = _args[6];
lean_object* v_head_4184_ = _args[7];
lean_object* v_ctors_4185_ = _args[8];
lean_object* v_numIndices_4186_ = _args[9];
lean_object* v___x_4187_ = _args[10];
lean_object* v___x_4188_ = _args[11];
lean_object* v_val_4189_ = _args[12];
lean_object* v_declName_4190_ = _args[13];
lean_object* v_levelParams_4191_ = _args[14];
lean_object* v_numParams_4192_ = _args[15];
lean_object* v___x_4193_ = _args[16];
lean_object* v_x2_4194_ = _args[17];
lean_object* v_x_4195_ = _args[18];
lean_object* v___y_4196_ = _args[19];
lean_object* v___y_4197_ = _args[20];
lean_object* v___y_4198_ = _args[21];
lean_object* v___y_4199_ = _args[22];
lean_object* v___y_4200_ = _args[23];
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4177_, v_x1_4178_, v_indName_4179_, v_tail_4180_, v_params_4181_, v_is_4182_, v___x_4183_, v_head_4184_, v_ctors_4185_, v_numIndices_4186_, v___x_4187_, v___x_4188_, v_val_4189_, v_declName_4190_, v_levelParams_4191_, v_numParams_4192_, v___x_4193_, v_x2_4194_, v_x_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec_ref(v_x_4195_);
lean_dec_ref(v_x2_4194_);
lean_dec_ref(v_x1_4178_);
lean_dec_ref(v___x_4177_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4202_, lean_object* v_indName_4203_, lean_object* v_tail_4204_, lean_object* v_params_4205_, lean_object* v_is_4206_, lean_object* v___x_4207_, lean_object* v_head_4208_, lean_object* v_ctors_4209_, lean_object* v_numIndices_4210_, lean_object* v___x_4211_, lean_object* v___x_4212_, lean_object* v_val_4213_, lean_object* v_declName_4214_, lean_object* v_levelParams_4215_, lean_object* v_numParams_4216_, lean_object* v___x_4217_, lean_object* v_t_4218_, lean_object* v___x_4219_, lean_object* v_x1_4220_, lean_object* v_x_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v___f_4227_; uint8_t v___x_4228_; lean_object* v___x_4229_; 
v___f_4227_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4227_, 0, v___x_4202_);
lean_closure_set(v___f_4227_, 1, v_x1_4220_);
lean_closure_set(v___f_4227_, 2, v_indName_4203_);
lean_closure_set(v___f_4227_, 3, v_tail_4204_);
lean_closure_set(v___f_4227_, 4, v_params_4205_);
lean_closure_set(v___f_4227_, 5, v_is_4206_);
lean_closure_set(v___f_4227_, 6, v___x_4207_);
lean_closure_set(v___f_4227_, 7, v_head_4208_);
lean_closure_set(v___f_4227_, 8, v_ctors_4209_);
lean_closure_set(v___f_4227_, 9, v_numIndices_4210_);
lean_closure_set(v___f_4227_, 10, v___x_4211_);
lean_closure_set(v___f_4227_, 11, v___x_4212_);
lean_closure_set(v___f_4227_, 12, v_val_4213_);
lean_closure_set(v___f_4227_, 13, v_declName_4214_);
lean_closure_set(v___f_4227_, 14, v_levelParams_4215_);
lean_closure_set(v___f_4227_, 15, v_numParams_4216_);
lean_closure_set(v___f_4227_, 16, v___x_4217_);
v___x_4228_ = 0;
v___x_4229_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4218_, v___x_4219_, v___f_4227_, v___x_4228_, v___x_4228_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4230_ = _args[0];
lean_object* v_indName_4231_ = _args[1];
lean_object* v_tail_4232_ = _args[2];
lean_object* v_params_4233_ = _args[3];
lean_object* v_is_4234_ = _args[4];
lean_object* v___x_4235_ = _args[5];
lean_object* v_head_4236_ = _args[6];
lean_object* v_ctors_4237_ = _args[7];
lean_object* v_numIndices_4238_ = _args[8];
lean_object* v___x_4239_ = _args[9];
lean_object* v___x_4240_ = _args[10];
lean_object* v_val_4241_ = _args[11];
lean_object* v_declName_4242_ = _args[12];
lean_object* v_levelParams_4243_ = _args[13];
lean_object* v_numParams_4244_ = _args[14];
lean_object* v___x_4245_ = _args[15];
lean_object* v_t_4246_ = _args[16];
lean_object* v___x_4247_ = _args[17];
lean_object* v_x1_4248_ = _args[18];
lean_object* v_x_4249_ = _args[19];
lean_object* v___y_4250_ = _args[20];
lean_object* v___y_4251_ = _args[21];
lean_object* v___y_4252_ = _args[22];
lean_object* v___y_4253_ = _args[23];
lean_object* v___y_4254_ = _args[24];
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4230_, v_indName_4231_, v_tail_4232_, v_params_4233_, v_is_4234_, v___x_4235_, v_head_4236_, v_ctors_4237_, v_numIndices_4238_, v___x_4239_, v___x_4240_, v_val_4241_, v_declName_4242_, v_levelParams_4243_, v_numParams_4244_, v___x_4245_, v_t_4246_, v___x_4247_, v_x1_4248_, v_x_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4251_);
lean_dec_ref(v___y_4250_);
lean_dec_ref(v_x_4249_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4256_, lean_object* v_indName_4257_, lean_object* v_tail_4258_, lean_object* v_params_4259_, lean_object* v_head_4260_, lean_object* v_ctors_4261_, lean_object* v_numIndices_4262_, lean_object* v___x_4263_, lean_object* v___x_4264_, lean_object* v_val_4265_, lean_object* v_declName_4266_, lean_object* v_levelParams_4267_, lean_object* v_numParams_4268_, lean_object* v___x_4269_, lean_object* v_is_4270_, lean_object* v_t_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___f_4279_; uint8_t v___x_4280_; lean_object* v___x_4281_; 
v___x_4277_ = lean_unsigned_to_nat(1u);
v___x_4278_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4271_);
v___f_4279_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4279_, 0, v___x_4256_);
lean_closure_set(v___f_4279_, 1, v_indName_4257_);
lean_closure_set(v___f_4279_, 2, v_tail_4258_);
lean_closure_set(v___f_4279_, 3, v_params_4259_);
lean_closure_set(v___f_4279_, 4, v_is_4270_);
lean_closure_set(v___f_4279_, 5, v___x_4277_);
lean_closure_set(v___f_4279_, 6, v_head_4260_);
lean_closure_set(v___f_4279_, 7, v_ctors_4261_);
lean_closure_set(v___f_4279_, 8, v_numIndices_4262_);
lean_closure_set(v___f_4279_, 9, v___x_4263_);
lean_closure_set(v___f_4279_, 10, v___x_4264_);
lean_closure_set(v___f_4279_, 11, v_val_4265_);
lean_closure_set(v___f_4279_, 12, v_declName_4266_);
lean_closure_set(v___f_4279_, 13, v_levelParams_4267_);
lean_closure_set(v___f_4279_, 14, v_numParams_4268_);
lean_closure_set(v___f_4279_, 15, v___x_4269_);
lean_closure_set(v___f_4279_, 16, v_t_4271_);
lean_closure_set(v___f_4279_, 17, v___x_4278_);
v___x_4280_ = 0;
v___x_4281_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4271_, v___x_4278_, v___f_4279_, v___x_4280_, v___x_4280_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4282_ = _args[0];
lean_object* v_indName_4283_ = _args[1];
lean_object* v_tail_4284_ = _args[2];
lean_object* v_params_4285_ = _args[3];
lean_object* v_head_4286_ = _args[4];
lean_object* v_ctors_4287_ = _args[5];
lean_object* v_numIndices_4288_ = _args[6];
lean_object* v___x_4289_ = _args[7];
lean_object* v___x_4290_ = _args[8];
lean_object* v_val_4291_ = _args[9];
lean_object* v_declName_4292_ = _args[10];
lean_object* v_levelParams_4293_ = _args[11];
lean_object* v_numParams_4294_ = _args[12];
lean_object* v___x_4295_ = _args[13];
lean_object* v_is_4296_ = _args[14];
lean_object* v_t_4297_ = _args[15];
lean_object* v___y_4298_ = _args[16];
lean_object* v___y_4299_ = _args[17];
lean_object* v___y_4300_ = _args[18];
lean_object* v___y_4301_ = _args[19];
lean_object* v___y_4302_ = _args[20];
_start:
{
lean_object* v_res_4303_; 
v_res_4303_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4282_, v_indName_4283_, v_tail_4284_, v_params_4285_, v_head_4286_, v_ctors_4287_, v_numIndices_4288_, v___x_4289_, v___x_4290_, v_val_4291_, v_declName_4292_, v_levelParams_4293_, v_numParams_4294_, v___x_4295_, v_is_4296_, v_t_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
lean_dec(v___y_4299_);
lean_dec_ref(v___y_4298_);
return v_res_4303_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4304_, lean_object* v_indName_4305_, lean_object* v_tail_4306_, lean_object* v_head_4307_, lean_object* v_ctors_4308_, lean_object* v_numIndices_4309_, lean_object* v___x_4310_, lean_object* v___x_4311_, lean_object* v_val_4312_, lean_object* v_declName_4313_, lean_object* v_levelParams_4314_, lean_object* v_numParams_4315_, lean_object* v_params_4316_, lean_object* v_t_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v___x_4323_; lean_object* v___f_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; lean_object* v___x_4327_; 
v___x_4323_ = l_Lean_Expr_bindingBody_x21(v_t_4317_);
lean_inc_ref(v___x_4323_);
lean_inc(v_numIndices_4309_);
v___f_4324_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4324_, 0, v___x_4304_);
lean_closure_set(v___f_4324_, 1, v_indName_4305_);
lean_closure_set(v___f_4324_, 2, v_tail_4306_);
lean_closure_set(v___f_4324_, 3, v_params_4316_);
lean_closure_set(v___f_4324_, 4, v_head_4307_);
lean_closure_set(v___f_4324_, 5, v_ctors_4308_);
lean_closure_set(v___f_4324_, 6, v_numIndices_4309_);
lean_closure_set(v___f_4324_, 7, v___x_4310_);
lean_closure_set(v___f_4324_, 8, v___x_4311_);
lean_closure_set(v___f_4324_, 9, v_val_4312_);
lean_closure_set(v___f_4324_, 10, v_declName_4313_);
lean_closure_set(v___f_4324_, 11, v_levelParams_4314_);
lean_closure_set(v___f_4324_, 12, v_numParams_4315_);
lean_closure_set(v___f_4324_, 13, v___x_4323_);
v___x_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4325_, 0, v_numIndices_4309_);
v___x_4326_ = 0;
v___x_4327_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4323_, v___x_4325_, v___f_4324_, v___x_4326_, v___x_4326_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
return v___x_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4328_ = _args[0];
lean_object* v_indName_4329_ = _args[1];
lean_object* v_tail_4330_ = _args[2];
lean_object* v_head_4331_ = _args[3];
lean_object* v_ctors_4332_ = _args[4];
lean_object* v_numIndices_4333_ = _args[5];
lean_object* v___x_4334_ = _args[6];
lean_object* v___x_4335_ = _args[7];
lean_object* v_val_4336_ = _args[8];
lean_object* v_declName_4337_ = _args[9];
lean_object* v_levelParams_4338_ = _args[10];
lean_object* v_numParams_4339_ = _args[11];
lean_object* v_params_4340_ = _args[12];
lean_object* v_t_4341_ = _args[13];
lean_object* v___y_4342_ = _args[14];
lean_object* v___y_4343_ = _args[15];
lean_object* v___y_4344_ = _args[16];
lean_object* v___y_4345_ = _args[17];
lean_object* v___y_4346_ = _args[18];
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4328_, v_indName_4329_, v_tail_4330_, v_head_4331_, v_ctors_4332_, v_numIndices_4333_, v___x_4334_, v___x_4335_, v_val_4336_, v_declName_4337_, v_levelParams_4338_, v_numParams_4339_, v_params_4340_, v_t_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
lean_dec_ref(v_t_4341_);
return v_res_4347_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4352_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4353_ = lean_unsigned_to_nat(58u);
v___x_4354_ = lean_unsigned_to_nat(142u);
v___x_4355_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4356_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4357_ = l_mkPanicMessageWithDecl(v___x_4356_, v___x_4355_, v___x_4354_, v___x_4353_, v___x_4352_);
return v___x_4357_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v___x_4358_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4359_ = lean_unsigned_to_nat(60u);
v___x_4360_ = lean_unsigned_to_nat(136u);
v___x_4361_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4362_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4363_ = l_mkPanicMessageWithDecl(v___x_4362_, v___x_4361_, v___x_4360_, v___x_4359_, v___x_4358_);
return v___x_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4364_, lean_object* v_indName_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_){
_start:
{
lean_object* v___x_4371_; 
lean_inc(v_indName_4365_);
v___x_4371_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
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
lean_inc(v_declName_4364_);
v___x_4375_ = l_Lean_Name_append(v_declName_4364_, v___x_4374_);
lean_inc(v_indName_4365_);
lean_inc(v___x_4375_);
v___x_4376_ = l_Lean_mkCasesOnSameCtorHet(v___x_4375_, v_indName_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_object* v___x_4378_; uint8_t v_isShared_4379_; uint8_t v_isSharedCheck_4409_; 
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4409_ == 0)
{
lean_object* v_unused_4410_; 
v_unused_4410_ = lean_ctor_get(v___x_4376_, 0);
lean_dec(v_unused_4410_);
v___x_4378_ = v___x_4376_;
v_isShared_4379_ = v_isSharedCheck_4409_;
goto v_resetjp_4377_;
}
else
{
lean_dec(v___x_4376_);
v___x_4378_ = lean_box(0);
v_isShared_4379_ = v_isSharedCheck_4409_;
goto v_resetjp_4377_;
}
v_resetjp_4377_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; 
lean_inc(v_indName_4365_);
v___x_4380_ = l_Lean_mkCasesOnName(v_indName_4365_);
v___x_4381_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4380_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
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
lean_object* v_head_4387_; lean_object* v_tail_4388_; lean_object* v_numParams_4389_; lean_object* v_numIndices_4390_; lean_object* v_ctors_4391_; lean_object* v___x_4392_; lean_object* v___f_4393_; lean_object* v___x_4395_; 
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
v___x_4392_ = l_Lean_instInhabitedExpr;
v___f_4393_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4393_, 0, v___x_4392_);
lean_closure_set(v___f_4393_, 1, v_indName_4365_);
lean_closure_set(v___f_4393_, 2, v_tail_4388_);
lean_closure_set(v___f_4393_, 3, v_head_4387_);
lean_closure_set(v___f_4393_, 4, v_ctors_4391_);
lean_closure_set(v___f_4393_, 5, v_numIndices_4390_);
lean_closure_set(v___f_4393_, 6, v___x_4375_);
lean_closure_set(v___f_4393_, 7, v___x_4386_);
lean_closure_set(v___f_4393_, 8, v_val_4373_);
lean_closure_set(v___f_4393_, 9, v_declName_4364_);
lean_closure_set(v___f_4393_, 10, v_levelParams_4383_);
lean_closure_set(v___f_4393_, 11, v_numParams_4389_);
if (v_isShared_4379_ == 0)
{
lean_ctor_set_tag(v___x_4378_, 1);
lean_ctor_set(v___x_4378_, 0, v_numParams_4389_);
v___x_4395_ = v___x_4378_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_numParams_4389_);
v___x_4395_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
uint8_t v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = 0;
v___x_4397_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4384_, v___x_4395_, v___f_4393_, v___x_4396_, v___x_4396_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
return v___x_4397_;
}
}
else
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
lean_dec(v___x_4386_);
lean_dec_ref(v_type_4384_);
lean_dec(v_levelParams_4383_);
lean_del_object(v___x_4378_);
lean_dec(v___x_4375_);
lean_dec_ref(v_val_4373_);
lean_dec(v_indName_4365_);
lean_dec(v_declName_4364_);
v___x_4399_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4400_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4399_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
return v___x_4400_;
}
}
else
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4408_; 
lean_del_object(v___x_4378_);
lean_dec(v___x_4375_);
lean_dec_ref(v_val_4373_);
lean_dec(v_indName_4365_);
lean_dec(v_declName_4364_);
v_a_4401_ = lean_ctor_get(v___x_4381_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4381_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4403_ = v___x_4381_;
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4381_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4408_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
lean_object* v___x_4406_; 
if (v_isShared_4404_ == 0)
{
v___x_4406_ = v___x_4403_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v_a_4401_);
v___x_4406_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
return v___x_4406_;
}
}
}
}
}
else
{
lean_dec(v___x_4375_);
lean_dec_ref(v_val_4373_);
lean_dec(v_indName_4365_);
lean_dec(v_declName_4364_);
return v___x_4376_;
}
}
else
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
lean_dec(v_a_4372_);
lean_dec(v_indName_4365_);
lean_dec(v_declName_4364_);
v___x_4411_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4412_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4411_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
return v___x_4412_;
}
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v_indName_4365_);
lean_dec(v_declName_4364_);
v_a_4413_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4371_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4371_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4421_, lean_object* v_indName_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_, lean_object* v_a_4426_, lean_object* v_a_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Lean_mkCasesOnSameCtor(v_declName_4421_, v_indName_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_);
lean_dec(v_a_4426_);
lean_dec_ref(v_a_4425_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4429_, lean_object* v_params_4430_, lean_object* v_motive_4431_, lean_object* v_as_4432_, size_t v_sz_4433_, size_t v_i_4434_, lean_object* v_bs_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4429_, v_params_4430_, v_motive_4431_, v_sz_4433_, v_i_4434_, v_bs_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4442_, lean_object* v_params_4443_, lean_object* v_motive_4444_, lean_object* v_as_4445_, lean_object* v_sz_4446_, lean_object* v_i_4447_, lean_object* v_bs_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
size_t v_sz_boxed_4454_; size_t v_i_boxed_4455_; lean_object* v_res_4456_; 
v_sz_boxed_4454_ = lean_unbox_usize(v_sz_4446_);
lean_dec(v_sz_4446_);
v_i_boxed_4455_ = lean_unbox_usize(v_i_4447_);
lean_dec(v_i_4447_);
v_res_4456_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4442_, v_params_4443_, v_motive_4444_, v_as_4445_, v_sz_boxed_4454_, v_i_boxed_4455_, v_bs_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec_ref(v_as_4445_);
lean_dec_ref(v_params_4443_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4457_, lean_object* v_params_4458_, lean_object* v_a_4459_, lean_object* v_snd_4460_, lean_object* v_alts_4461_, lean_object* v_as_4462_, size_t v_sz_4463_, size_t v_i_4464_, lean_object* v_bs_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_){
_start:
{
lean_object* v___x_4471_; 
v___x_4471_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4457_, v_params_4458_, v_a_4459_, v_snd_4460_, v_alts_4461_, v_sz_4463_, v_i_4464_, v_bs_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_);
return v___x_4471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4472_, lean_object* v_params_4473_, lean_object* v_a_4474_, lean_object* v_snd_4475_, lean_object* v_alts_4476_, lean_object* v_as_4477_, lean_object* v_sz_4478_, lean_object* v_i_4479_, lean_object* v_bs_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
size_t v_sz_boxed_4486_; size_t v_i_boxed_4487_; lean_object* v_res_4488_; 
v_sz_boxed_4486_ = lean_unbox_usize(v_sz_4478_);
lean_dec(v_sz_4478_);
v_i_boxed_4487_ = lean_unbox_usize(v_i_4479_);
lean_dec(v_i_4479_);
v_res_4488_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4472_, v_params_4473_, v_a_4474_, v_snd_4475_, v_alts_4476_, v_as_4477_, v_sz_boxed_4486_, v_i_boxed_4487_, v_bs_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
lean_dec_ref(v_as_4477_);
lean_dec_ref(v_params_4473_);
return v_res_4488_;
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
