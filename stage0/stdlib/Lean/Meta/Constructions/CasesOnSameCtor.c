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
uint8_t v___x_20568__boxed_559_; uint8_t v___x_20569__boxed_560_; uint8_t v___x_20570__boxed_561_; lean_object* v_res_562_; 
v___x_20568__boxed_559_ = lean_unbox(v___x_540_);
v___x_20569__boxed_560_ = lean_unbox(v___x_541_);
v___x_20570__boxed_561_ = lean_unbox(v___x_542_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_537_, v_ism2_538_, v_motive_539_, v___x_20568__boxed_559_, v___x_20569__boxed_560_, v___x_20570__boxed_561_, v_a_543_, v___f_544_, v_zs1_545_, v_val_546_, v___x_547_, v_indName_548_, v_v_549_, v___x_550_, v_params_551_, v___x_552_, v_h_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
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
uint8_t v___x_20680__boxed_595_; uint8_t v___x_20681__boxed_596_; uint8_t v___x_20682__boxed_597_; lean_object* v_res_598_; 
v___x_20680__boxed_595_ = lean_unbox(v___x_585_);
v___x_20681__boxed_596_ = lean_unbox(v___x_586_);
v___x_20682__boxed_597_ = lean_unbox(v___x_587_);
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_581_, v_alts_582_, v___x_583_, v_zs1_584_, v___x_20680__boxed_595_, v___x_20681__boxed_596_, v___x_20682__boxed_597_, v_zs2_588_, v_x_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_);
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
uint8_t v___x_20741__boxed_693_; uint8_t v___x_20742__boxed_694_; uint8_t v___x_20743__boxed_695_; lean_object* v_res_696_; 
v___x_20741__boxed_693_ = lean_unbox(v___x_669_);
v___x_20742__boxed_694_ = lean_unbox(v___x_670_);
v___x_20743__boxed_695_ = lean_unbox(v___x_671_);
v_res_696_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_666_, v_alts_667_, v___x_668_, v___x_20741__boxed_693_, v___x_20742__boxed_694_, v___x_20743__boxed_695_, v___x_672_, v___x_673_, v___x_674_, v_ism2_675_, v_motive_676_, v_a_677_, v_val_678_, v_indName_679_, v_v_680_, v___x_681_, v_params_682_, v___x_683_, v___x_684_, v___x_685_, v_zs1_686_, v_ctorRet1_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
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
uint8_t v___x_20972__boxed_862_; uint8_t v___x_20973__boxed_863_; uint8_t v___x_20974__boxed_864_; lean_object* v_res_865_; 
v___x_20972__boxed_862_ = lean_unbox(v___x_840_);
v___x_20973__boxed_863_ = lean_unbox(v___x_841_);
v___x_20974__boxed_864_ = lean_unbox(v___x_842_);
v_res_865_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_836_, v___x_837_, v_a_838_, v_ism1_839_, v___x_20972__boxed_862_, v___x_20973__boxed_863_, v___x_20974__boxed_864_, v___x_843_, v_tail_844_, v_params_845_, v_alts_846_, v_numParams_847_, v_ism2_848_, v_val_849_, v_indName_850_, v___x_851_, v___x_852_, v___x_853_, v_name_854_, v___x_855_, v_heq_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
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
uint8_t v___x_21095__boxed_928_; uint8_t v___x_21096__boxed_929_; uint8_t v___x_21097__boxed_930_; lean_object* v_res_931_; 
v___x_21095__boxed_928_ = lean_unbox(v___x_912_);
v___x_21096__boxed_929_ = lean_unbox(v___x_913_);
v___x_21097__boxed_930_ = lean_unbox(v___x_914_);
v_res_931_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_905_, v_tail_906_, v_params_907_, v_ism1_908_, v_ism2_909_, v_motive_910_, v___x_911_, v___x_21095__boxed_928_, v___x_21096__boxed_929_, v___x_21097__boxed_930_, v___x_915_, v_numParams_916_, v_val_917_, v___x_918_, v___x_919_, v_name_920_, v___x_921_, v_alts_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
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
lean_object* v___x_19979__overap_983_; lean_object* v___x_984_; 
v___x_19979__overap_983_ = l_instInhabitedOfMonad___redArg(v___x_975_, v___x_976_);
lean_inc(v___y_981_);
lean_inc_ref(v___y_980_);
lean_inc(v___y_979_);
lean_inc_ref(v___y_978_);
v___x_984_ = lean_apply_5(v___x_19979__overap_983_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, lean_box(0));
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
uint8_t v___x_21534__boxed_1299_; uint8_t v___x_21535__boxed_1300_; uint8_t v___x_21536__boxed_1301_; lean_object* v_res_1302_; 
v___x_21534__boxed_1299_ = lean_unbox(v___x_1287_);
v___x_21535__boxed_1300_ = lean_unbox(v___x_1288_);
v___x_21536__boxed_1301_ = lean_unbox(v___x_1289_);
v_res_1302_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1280_, v_dummy_1281_, v___x_1282_, v___x_1283_, v___x_1284_, v_motive_1285_, v_zs1_1286_, v___x_21534__boxed_1299_, v___x_21535__boxed_1300_, v___x_21536__boxed_1301_, v_v_1290_, v___x_1291_, v_zs2_1292_, v_ctorRet2_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
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
uint8_t v___x_21675__boxed_1362_; uint8_t v___x_21676__boxed_1363_; uint8_t v___x_21677__boxed_1364_; lean_object* v_res_1365_; 
v___x_21675__boxed_1362_ = lean_unbox(v___x_1349_);
v___x_21676__boxed_1363_ = lean_unbox(v___x_1350_);
v___x_21677__boxed_1364_ = lean_unbox(v___x_1351_);
v_res_1365_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1345_, v___x_1346_, v___x_1347_, v_motive_1348_, v___x_21675__boxed_1362_, v___x_21676__boxed_1363_, v___x_21677__boxed_1364_, v_v_1352_, v___x_1353_, v_a_1354_, v_zs1_1355_, v_ctorRet1_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
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
uint8_t v___x_21855__boxed_1495_; uint8_t v___x_21856__boxed_1496_; uint8_t v___x_21857__boxed_1497_; lean_object* v_res_1498_; 
v___x_21855__boxed_1495_ = lean_unbox(v___x_1481_);
v___x_21856__boxed_1496_ = lean_unbox(v___x_1482_);
v___x_21857__boxed_1497_ = lean_unbox(v___x_1483_);
v_res_1498_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1473_, v_tail_1474_, v_params_1475_, v_numParams_1476_, v_indName_1477_, v_ism1_1478_, v_ism2_1479_, v___x_1480_, v___x_21855__boxed_1495_, v___x_21856__boxed_1496_, v___x_21857__boxed_1497_, v_val_1484_, v___x_1485_, v___x_1486_, v_name_1487_, v___x_1488_, v_motive_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
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
uint8_t v___x_22143__boxed_1724_; lean_object* v_res_1725_; 
v___x_22143__boxed_1724_ = lean_unbox(v___x_1718_);
v_res_1725_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1715_, v_declName_1716_, v_levelParams_1717_, v___x_22143__boxed_1724_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
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
lean_object* v___x_1746_; lean_object* v_env_1747_; lean_object* v___x_1748_; lean_object* v_toCold_1749_; lean_object* v_mctx_1750_; lean_object* v_lctx_1751_; lean_object* v_options_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1746_ = lean_st_ref_get(v___y_1744_);
v_env_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc_ref(v_env_1747_);
lean_dec(v___x_1746_);
v___x_1748_ = lean_st_ref_get(v___y_1742_);
v_toCold_1749_ = lean_ctor_get(v___y_1743_, 0);
v_mctx_1750_ = lean_ctor_get(v___x_1748_, 0);
lean_inc_ref(v_mctx_1750_);
lean_dec(v___x_1748_);
v_lctx_1751_ = lean_ctor_get(v___y_1741_, 2);
v_options_1752_ = lean_ctor_get(v_toCold_1749_, 2);
lean_inc_ref(v_options_1752_);
lean_inc_ref(v_lctx_1751_);
v___x_1753_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1753_, 0, v_env_1747_);
lean_ctor_set(v___x_1753_, 1, v_mctx_1750_);
lean_ctor_set(v___x_1753_, 2, v_lctx_1751_);
lean_ctor_set(v___x_1753_, 3, v_options_1752_);
v___x_1754_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v_msgData_1740_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(lean_object* v_msgData_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(lean_object* v_msg_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_ref_1769_; lean_object* v___x_1770_; lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1779_; 
v_ref_1769_ = lean_ctor_get(v___y_1766_, 2);
v___x_1770_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_);
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1773_ = v___x_1770_;
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1770_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1779_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
lean_inc(v_ref_1769_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_ref_1769_);
lean_ctor_set(v___x_1775_, 1, v_a_1771_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set_tag(v___x_1773_, 1);
lean_ctor_set(v___x_1773_, 0, v___x_1775_);
v___x_1777_ = v___x_1773_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(lean_object* v_msg_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(lean_object* v_ref_1787_, lean_object* v_msg_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v_toCold_1794_; lean_object* v_currRecDepth_1795_; lean_object* v_ref_1796_; uint8_t v_diag_1797_; uint8_t v_suppressElabErrors_1798_; lean_object* v_ref_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v_toCold_1794_ = lean_ctor_get(v___y_1791_, 0);
v_currRecDepth_1795_ = lean_ctor_get(v___y_1791_, 1);
v_ref_1796_ = lean_ctor_get(v___y_1791_, 2);
v_diag_1797_ = lean_ctor_get_uint8(v___y_1791_, sizeof(void*)*3);
v_suppressElabErrors_1798_ = lean_ctor_get_uint8(v___y_1791_, sizeof(void*)*3 + 1);
v_ref_1799_ = l_Lean_replaceRef(v_ref_1787_, v_ref_1796_);
lean_inc(v_currRecDepth_1795_);
lean_inc_ref(v_toCold_1794_);
v___x_1800_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1800_, 0, v_toCold_1794_);
lean_ctor_set(v___x_1800_, 1, v_currRecDepth_1795_);
lean_ctor_set(v___x_1800_, 2, v_ref_1799_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*3, v_diag_1797_);
lean_ctor_set_uint8(v___x_1800_, sizeof(void*)*3 + 1, v_suppressElabErrors_1798_);
v___x_1801_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_1788_, v___y_1789_, v___y_1790_, v___x_1800_, v___y_1792_);
lean_dec_ref_known(v___x_1800_, 3);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(lean_object* v_ref_1802_, lean_object* v_msg_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1802_, v_msg_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v_ref_1802_);
return v_res_1809_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1814_ = lean_unsigned_to_nat(0u);
v___x_1815_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1814_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
lean_ctor_set(v___x_1815_, 2, v___x_1814_);
lean_ctor_set(v___x_1815_, 3, v___x_1814_);
lean_ctor_set(v___x_1815_, 4, v___x_1813_);
lean_ctor_set(v___x_1815_, 5, v___x_1813_);
lean_ctor_set(v___x_1815_, 6, v___x_1813_);
lean_ctor_set(v___x_1815_, 7, v___x_1813_);
lean_ctor_set(v___x_1815_, 8, v___x_1813_);
lean_ctor_set(v___x_1815_, 9, v___x_1813_);
lean_ctor_set(v___x_1815_, 10, v___x_1813_);
return v___x_1815_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_unsigned_to_nat(32u);
v___x_1817_ = lean_mk_empty_array_with_capacity(v___x_1816_);
v___x_1818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
return v___x_1818_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1819_ = ((size_t)5ULL);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = lean_unsigned_to_nat(32u);
v___x_1822_ = lean_mk_empty_array_with_capacity(v___x_1821_);
v___x_1823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
v___x_1824_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v___x_1822_);
lean_ctor_set(v___x_1824_, 2, v___x_1820_);
lean_ctor_set(v___x_1824_, 3, v___x_1820_);
lean_ctor_set_usize(v___x_1824_, 4, v___x_1819_);
return v___x_1824_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1825_ = lean_box(1);
v___x_1826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
v___x_1827_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
v___x_1828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1826_);
lean_ctor_set(v___x_1828_, 2, v___x_1825_);
return v___x_1828_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1830_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6));
v___x_1831_ = l_Lean_stringToMessageData(v___x_1830_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1833_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8));
v___x_1834_ = l_Lean_stringToMessageData(v___x_1833_);
return v___x_1834_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18));
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(lean_object* v_msg_1850_, lean_object* v_declHint_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v_env_1855_; uint8_t v___x_1856_; 
v___x_1854_ = lean_st_ref_get(v___y_1852_);
v_env_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc_ref(v_env_1855_);
lean_dec(v___x_1854_);
v___x_1856_ = l_Lean_Name_isAnonymous(v_declHint_1851_);
if (v___x_1856_ == 0)
{
uint8_t v_isExporting_1857_; 
v_isExporting_1857_ = lean_ctor_get_uint8(v_env_1855_, sizeof(void*)*8);
if (v_isExporting_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_dec_ref(v_env_1855_);
lean_dec(v_declHint_1851_);
v___x_1858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_msg_1850_);
return v___x_1858_;
}
else
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
lean_inc_ref(v_env_1855_);
v___x_1859_ = l_Lean_Environment_setExporting(v_env_1855_, v___x_1856_);
lean_inc(v_declHint_1851_);
lean_inc_ref(v___x_1859_);
v___x_1860_ = l_Lean_Environment_contains(v___x_1859_, v_declHint_1851_, v_isExporting_1857_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v___x_1859_);
lean_dec_ref(v_env_1855_);
lean_dec(v_declHint_1851_);
v___x_1861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1861_, 0, v_msg_1850_);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v_c_1867_; lean_object* v___x_1868_; 
v___x_1862_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
v___x_1863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5);
v___x_1864_ = l_Lean_Options_empty;
v___x_1865_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1859_);
lean_ctor_set(v___x_1865_, 1, v___x_1862_);
lean_ctor_set(v___x_1865_, 2, v___x_1863_);
lean_ctor_set(v___x_1865_, 3, v___x_1864_);
lean_inc(v_declHint_1851_);
v___x_1866_ = l_Lean_MessageData_ofConstName(v_declHint_1851_, v___x_1856_);
v_c_1867_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1867_, 0, v___x_1865_);
lean_ctor_set(v_c_1867_, 1, v___x_1866_);
v___x_1868_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1855_, v_declHint_1851_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
lean_dec_ref(v_env_1855_);
lean_dec(v_declHint_1851_);
v___x_1869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v_c_1867_);
v___x_1871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_MessageData_note(v___x_1872_);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v_msg_1850_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
return v___x_1875_;
}
else
{
lean_object* v_val_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1911_; 
v_val_1876_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1878_ = v___x_1868_;
v_isShared_1879_ = v_isSharedCheck_1911_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_val_1876_);
lean_dec(v___x_1868_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1911_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v_mod_1883_; uint8_t v___x_1884_; 
v___x_1880_ = lean_box(0);
v___x_1881_ = l_Lean_Environment_header(v_env_1855_);
lean_dec_ref(v_env_1855_);
v___x_1882_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1881_);
v_mod_1883_ = lean_array_get(v___x_1880_, v___x_1882_, v_val_1876_);
lean_dec(v_val_1876_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = l_Lean_isPrivateName(v_declHint_1851_);
lean_dec(v_declHint_1851_);
if (v___x_1884_ == 0)
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1885_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1885_);
lean_ctor_set(v___x_1886_, 1, v_c_1867_);
v___x_1887_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = l_Lean_MessageData_ofName(v_mod_1883_);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = l_Lean_MessageData_note(v___x_1892_);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v_msg_1850_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set_tag(v___x_1878_, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1894_);
v___x_1896_ = v___x_1878_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1894_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1898_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1898_);
lean_ctor_set(v___x_1899_, 1, v_c_1867_);
v___x_1900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = l_Lean_MessageData_ofName(v_mod_1883_);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = l_Lean_MessageData_note(v___x_1905_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_msg_1850_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set_tag(v___x_1878_, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1907_);
v___x_1909_ = v___x_1878_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1912_; 
lean_dec_ref(v_env_1855_);
lean_dec(v_declHint_1851_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_msg_1850_);
return v___x_1912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(lean_object* v_msg_1913_, lean_object* v_declHint_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1913_, v_declHint_1914_, v___y_1915_);
lean_dec(v___y_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(lean_object* v_msg_1918_, lean_object* v_declHint_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1935_; 
v___x_1925_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_1918_, v_declHint_1919_, v___y_1923_);
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1928_ = v___x_1925_;
v_isShared_1929_ = v_isSharedCheck_1935_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_dec(v___x_1925_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1935_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1930_ = l_Lean_unknownIdentifierMessageTag;
v___x_1931_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1930_);
lean_ctor_set(v___x_1931_, 1, v_a_1926_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1931_);
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(lean_object* v_msg_1936_, lean_object* v_declHint_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1936_, v_declHint_1937_, v___y_1938_, v___y_1939_, v___y_1940_, v___y_1941_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(lean_object* v_ref_1944_, lean_object* v_msg_1945_, lean_object* v_declHint_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
lean_object* v___x_1952_; lean_object* v_a_1953_; lean_object* v___x_1954_; 
v___x_1952_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_1945_, v_declHint_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
v___x_1954_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_1944_, v_a_1953_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(lean_object* v_ref_1955_, lean_object* v_msg_1956_, lean_object* v_declHint_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1955_, v_msg_1956_, v_declHint_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v_ref_1955_);
return v_res_1963_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0));
v___x_1966_ = l_Lean_stringToMessageData(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2));
v___x_1969_ = l_Lean_stringToMessageData(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(lean_object* v_ref_1970_, lean_object* v_constName_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1977_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
v___x_1978_ = 0;
lean_inc(v_constName_1971_);
v___x_1979_ = l_Lean_MessageData_ofConstName(v_constName_1971_, v___x_1978_);
v___x_1980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1977_);
lean_ctor_set(v___x_1980_, 1, v___x_1979_);
v___x_1981_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_1982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1980_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_1970_, v___x_1982_, v_constName_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(lean_object* v_ref_1984_, lean_object* v_constName_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1984_, v_constName_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v_ref_1984_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_){
_start:
{
lean_object* v_ref_1998_; lean_object* v___x_1999_; 
v_ref_1998_ = lean_ctor_get(v___y_1995_, 2);
v___x_1999_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_1998_, v_constName_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_);
lean_dec(v___y_2004_);
lean_dec_ref(v___y_2003_);
lean_dec(v___y_2002_);
lean_dec_ref(v___y_2001_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v___x_2013_; lean_object* v_env_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; 
v___x_2013_ = lean_st_ref_get(v___y_2011_);
v_env_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc_ref(v_env_2014_);
lean_dec(v___x_2013_);
v___x_2015_ = 0;
lean_inc(v_constName_2007_);
v___x_2016_ = l_Lean_Environment_findConstVal_x3f(v_env_2014_, v_constName_2007_, v___x_2015_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
return v___x_2017_;
}
else
{
lean_object* v_val_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_constName_2007_);
v_val_2018_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2016_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_val_2018_);
lean_dec(v___x_2016_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 0);
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_val_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
lean_dec(v___y_2030_);
lean_dec_ref(v___y_2029_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_declName_2033_, uint8_t v_s_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v___x_2038_; lean_object* v_env_2039_; lean_object* v_nextMacroScope_2040_; lean_object* v_ngen_2041_; lean_object* v_auxDeclNGen_2042_; lean_object* v_traceState_2043_; lean_object* v_messages_2044_; lean_object* v_infoState_2045_; lean_object* v_snapshotTasks_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2075_; 
v___x_2038_ = lean_st_ref_take(v___y_2036_);
v_env_2039_ = lean_ctor_get(v___x_2038_, 0);
v_nextMacroScope_2040_ = lean_ctor_get(v___x_2038_, 1);
v_ngen_2041_ = lean_ctor_get(v___x_2038_, 2);
v_auxDeclNGen_2042_ = lean_ctor_get(v___x_2038_, 3);
v_traceState_2043_ = lean_ctor_get(v___x_2038_, 4);
v_messages_2044_ = lean_ctor_get(v___x_2038_, 6);
v_infoState_2045_ = lean_ctor_get(v___x_2038_, 7);
v_snapshotTasks_2046_ = lean_ctor_get(v___x_2038_, 8);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v___x_2038_, 5);
lean_dec(v_unused_2076_);
v___x_2048_ = v___x_2038_;
v_isShared_2049_ = v_isSharedCheck_2075_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_snapshotTasks_2046_);
lean_inc(v_infoState_2045_);
lean_inc(v_messages_2044_);
lean_inc(v_traceState_2043_);
lean_inc(v_auxDeclNGen_2042_);
lean_inc(v_ngen_2041_);
lean_inc(v_nextMacroScope_2040_);
lean_inc(v_env_2039_);
lean_dec(v___x_2038_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2075_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
uint8_t v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2050_ = 0;
v___x_2051_ = lean_box(0);
v___x_2052_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2039_, v_declName_2033_, v_s_2034_, v___x_2050_, v___x_2051_);
v___x_2053_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 5, v___x_2053_);
lean_ctor_set(v___x_2048_, 0, v___x_2052_);
v___x_2055_ = v___x_2048_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2052_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_nextMacroScope_2040_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_ngen_2041_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_auxDeclNGen_2042_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_traceState_2043_);
lean_ctor_set(v_reuseFailAlloc_2074_, 5, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2074_, 6, v_messages_2044_);
lean_ctor_set(v_reuseFailAlloc_2074_, 7, v_infoState_2045_);
lean_ctor_set(v_reuseFailAlloc_2074_, 8, v_snapshotTasks_2046_);
v___x_2055_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v_mctx_2058_; lean_object* v_zetaDeltaFVarIds_2059_; lean_object* v_postponed_2060_; lean_object* v_diag_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2072_; 
v___x_2056_ = lean_st_ref_put(v___y_2036_, v___x_2055_);
v___x_2057_ = lean_st_ref_take(v___y_2035_);
v_mctx_2058_ = lean_ctor_get(v___x_2057_, 0);
v_zetaDeltaFVarIds_2059_ = lean_ctor_get(v___x_2057_, 2);
v_postponed_2060_ = lean_ctor_get(v___x_2057_, 3);
v_diag_2061_ = lean_ctor_get(v___x_2057_, 4);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2072_ == 0)
{
lean_object* v_unused_2073_; 
v_unused_2073_ = lean_ctor_get(v___x_2057_, 1);
lean_dec(v_unused_2073_);
v___x_2063_ = v___x_2057_;
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_diag_2061_);
lean_inc(v_postponed_2060_);
lean_inc(v_zetaDeltaFVarIds_2059_);
lean_inc(v_mctx_2058_);
lean_dec(v___x_2057_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2065_; lean_object* v___x_2067_; 
v___x_2065_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 1, v___x_2065_);
v___x_2067_ = v___x_2063_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_mctx_2058_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_zetaDeltaFVarIds_2059_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_postponed_2060_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_diag_2061_);
v___x_2067_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2068_ = lean_st_ref_put(v___y_2035_, v___x_2067_);
v___x_2069_ = lean_box(0);
v___x_2070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_declName_2077_, lean_object* v_s_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
uint8_t v_s_boxed_2082_; lean_object* v_res_2083_; 
v_s_boxed_2082_ = lean_unbox(v_s_2078_);
v_res_2083_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2077_, v_s_boxed_2082_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec(v___y_2079_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_declName_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
uint8_t v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = 0;
v___x_2091_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2084_, v___x_2090_, v___y_2086_, v___y_2088_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_declName_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2098_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0));
v___x_2101_ = l_Lean_stringToMessageData(v___x_2100_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2103_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2));
v___x_2104_ = l_Lean_stringToMessageData(v___x_2103_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4));
v___x_2107_ = l_Lean_stringToMessageData(v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(lean_object* v_attrName_2108_, lean_object* v_declName_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2115_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2116_ = l_Lean_MessageData_ofName(v_attrName_2108_);
v___x_2117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = 0;
v___x_2121_ = l_Lean_MessageData_ofConstName(v_declName_2109_, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2119_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2122_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2124_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(lean_object* v_attrName_2126_, lean_object* v_declName_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2126_, v_declName_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2133_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0));
v___x_2136_ = l_Lean_stringToMessageData(v___x_2135_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(lean_object* v_attrName_2140_, lean_object* v_declName_2141_, lean_object* v_asyncPrefix_x3f_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___y_2149_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2142_) == 0)
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Lean_MessageData_nil;
v___y_2149_ = v___x_2162_;
goto v___jp_2148_;
}
else
{
lean_object* v_val_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v_val_2163_ = lean_ctor_get(v_asyncPrefix_x3f_2142_, 0);
lean_inc(v_val_2163_);
lean_dec_ref_known(v_asyncPrefix_x3f_2142_, 1);
v___x_2164_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
v___x_2165_ = l_Lean_MessageData_ofName(v_val_2163_);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___y_2149_ = v___x_2168_;
goto v___jp_2148_;
}
v___jp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2150_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
v___x_2151_ = l_Lean_MessageData_ofName(v_attrName_2140_);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
v___x_2154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2152_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = 0;
v___x_2156_ = l_Lean_MessageData_ofConstName(v_declName_2141_, v___x_2155_);
v___x_2157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2157_, 0, v___x_2154_);
lean_ctor_set(v___x_2157_, 1, v___x_2156_);
v___x_2158_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v___y_2149_);
v___x_2161_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_2160_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
return v___x_2161_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v_attrName_2169_, lean_object* v_declName_2170_, lean_object* v_asyncPrefix_x3f_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2169_, v_declName_2170_, v_asyncPrefix_x3f_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_attr_2178_, lean_object* v_decl_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v___x_2228_; lean_object* v_env_2229_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___x_2244_; 
v___x_2228_ = lean_st_ref_get(v___y_2183_);
v_env_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_ref(v_env_2229_);
lean_dec(v___x_2228_);
v___x_2244_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2229_, v_decl_2179_);
if (lean_obj_tag(v___x_2244_) == 0)
{
v___y_2231_ = v___y_2180_;
v___y_2232_ = v___y_2181_;
v___y_2233_ = v___y_2182_;
v___y_2234_ = v___y_2183_;
goto v___jp_2230_;
}
else
{
lean_object* v_attr_2245_; lean_object* v_toAttributeImplCore_2246_; lean_object* v_name_2247_; lean_object* v___x_2248_; 
lean_dec_ref_known(v___x_2244_, 1);
lean_dec_ref(v_env_2229_);
v_attr_2245_ = lean_ctor_get(v_attr_2178_, 0);
lean_inc_ref(v_attr_2245_);
lean_dec_ref(v_attr_2178_);
v_toAttributeImplCore_2246_ = lean_ctor_get(v_attr_2245_, 0);
lean_inc_ref(v_toAttributeImplCore_2246_);
lean_dec_ref(v_attr_2245_);
v_name_2247_ = lean_ctor_get(v_toAttributeImplCore_2246_, 1);
lean_inc(v_name_2247_);
lean_dec_ref(v_toAttributeImplCore_2246_);
v___x_2248_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_2247_, v_decl_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2248_;
}
v___jp_2185_:
{
lean_object* v___x_2188_; lean_object* v_ext_2189_; lean_object* v_toEnvExtension_2190_; lean_object* v_env_2191_; lean_object* v_nextMacroScope_2192_; lean_object* v_ngen_2193_; lean_object* v_auxDeclNGen_2194_; lean_object* v_traceState_2195_; lean_object* v_messages_2196_; lean_object* v_infoState_2197_; lean_object* v_snapshotTasks_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2226_; 
v___x_2188_ = lean_st_ref_take(v___y_2187_);
v_ext_2189_ = lean_ctor_get(v_attr_2178_, 1);
lean_inc_ref(v_ext_2189_);
lean_dec_ref(v_attr_2178_);
v_toEnvExtension_2190_ = lean_ctor_get(v_ext_2189_, 0);
v_env_2191_ = lean_ctor_get(v___x_2188_, 0);
v_nextMacroScope_2192_ = lean_ctor_get(v___x_2188_, 1);
v_ngen_2193_ = lean_ctor_get(v___x_2188_, 2);
v_auxDeclNGen_2194_ = lean_ctor_get(v___x_2188_, 3);
v_traceState_2195_ = lean_ctor_get(v___x_2188_, 4);
v_messages_2196_ = lean_ctor_get(v___x_2188_, 6);
v_infoState_2197_ = lean_ctor_get(v___x_2188_, 7);
v_snapshotTasks_2198_ = lean_ctor_get(v___x_2188_, 8);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; 
v_unused_2227_ = lean_ctor_get(v___x_2188_, 5);
lean_dec(v_unused_2227_);
v___x_2200_ = v___x_2188_;
v_isShared_2201_ = v_isSharedCheck_2226_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_snapshotTasks_2198_);
lean_inc(v_infoState_2197_);
lean_inc(v_messages_2196_);
lean_inc(v_traceState_2195_);
lean_inc(v_auxDeclNGen_2194_);
lean_inc(v_ngen_2193_);
lean_inc(v_nextMacroScope_2192_);
lean_inc(v_env_2191_);
lean_dec(v___x_2188_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2226_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v_asyncMode_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v_asyncMode_2202_ = lean_ctor_get(v_toEnvExtension_2190_, 2);
lean_inc(v_asyncMode_2202_);
lean_inc(v_decl_2179_);
v___x_2203_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2189_, v_env_2191_, v_decl_2179_, v_asyncMode_2202_, v_decl_2179_);
lean_dec(v_asyncMode_2202_);
v___x_2204_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 5, v___x_2204_);
lean_ctor_set(v___x_2200_, 0, v___x_2203_);
v___x_2206_ = v___x_2200_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v_nextMacroScope_2192_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_ngen_2193_);
lean_ctor_set(v_reuseFailAlloc_2225_, 3, v_auxDeclNGen_2194_);
lean_ctor_set(v_reuseFailAlloc_2225_, 4, v_traceState_2195_);
lean_ctor_set(v_reuseFailAlloc_2225_, 5, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2225_, 6, v_messages_2196_);
lean_ctor_set(v_reuseFailAlloc_2225_, 7, v_infoState_2197_);
lean_ctor_set(v_reuseFailAlloc_2225_, 8, v_snapshotTasks_2198_);
v___x_2206_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v_mctx_2209_; lean_object* v_zetaDeltaFVarIds_2210_; lean_object* v_postponed_2211_; lean_object* v_diag_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2223_; 
v___x_2207_ = lean_st_ref_put(v___y_2187_, v___x_2206_);
v___x_2208_ = lean_st_ref_take(v___y_2186_);
v_mctx_2209_ = lean_ctor_get(v___x_2208_, 0);
v_zetaDeltaFVarIds_2210_ = lean_ctor_get(v___x_2208_, 2);
v_postponed_2211_ = lean_ctor_get(v___x_2208_, 3);
v_diag_2212_ = lean_ctor_get(v___x_2208_, 4);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; 
v_unused_2224_ = lean_ctor_get(v___x_2208_, 1);
lean_dec(v_unused_2224_);
v___x_2214_ = v___x_2208_;
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_diag_2212_);
lean_inc(v_postponed_2211_);
lean_inc(v_zetaDeltaFVarIds_2210_);
lean_inc(v_mctx_2209_);
lean_dec(v___x_2208_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2223_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2216_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 1, v___x_2216_);
v___x_2218_ = v___x_2214_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_mctx_2209_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2216_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v_zetaDeltaFVarIds_2210_);
lean_ctor_set(v_reuseFailAlloc_2222_, 3, v_postponed_2211_);
lean_ctor_set(v_reuseFailAlloc_2222_, 4, v_diag_2212_);
v___x_2218_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_st_ref_put(v___y_2186_, v___x_2218_);
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
return v___x_2221_;
}
}
}
}
}
v___jp_2230_:
{
lean_object* v_ext_2235_; lean_object* v_toEnvExtension_2236_; lean_object* v_attr_2237_; lean_object* v_asyncMode_2238_; uint8_t v___x_2239_; 
v_ext_2235_ = lean_ctor_get(v_attr_2178_, 1);
v_toEnvExtension_2236_ = lean_ctor_get(v_ext_2235_, 0);
v_attr_2237_ = lean_ctor_get(v_attr_2178_, 0);
v_asyncMode_2238_ = lean_ctor_get(v_toEnvExtension_2236_, 2);
lean_inc(v_decl_2179_);
lean_inc_ref(v_env_2229_);
v___x_2239_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2229_, v_decl_2179_, v_asyncMode_2238_);
if (v___x_2239_ == 0)
{
lean_object* v_toAttributeImplCore_2240_; lean_object* v_name_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_inc_ref(v_attr_2237_);
lean_dec_ref(v_attr_2178_);
v_toAttributeImplCore_2240_ = lean_ctor_get(v_attr_2237_, 0);
lean_inc_ref(v_toAttributeImplCore_2240_);
lean_dec_ref(v_attr_2237_);
v_name_2241_ = lean_ctor_get(v_toAttributeImplCore_2240_, 1);
lean_inc(v_name_2241_);
lean_dec_ref(v_toAttributeImplCore_2240_);
v___x_2242_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2229_);
v___x_2243_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_2241_, v_decl_2179_, v___x_2242_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
return v___x_2243_;
}
else
{
lean_dec_ref(v_env_2229_);
v___y_2186_ = v___y_2232_;
v___y_2187_ = v___y_2234_;
goto v___jp_2185_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(lean_object* v_attr_2249_, lean_object* v_decl_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v_attr_2249_, v_decl_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; lean_object* v_env_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; 
v___x_2263_ = lean_st_ref_get(v___y_2261_);
v_env_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc_ref(v_env_2264_);
lean_dec(v___x_2263_);
v___x_2265_ = 0;
lean_inc(v_constName_2257_);
v___x_2266_ = l_Lean_Environment_find_x3f(v_env_2264_, v_constName_2257_, v___x_2265_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
return v___x_2267_;
}
else
{
lean_object* v_val_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec(v_constName_2257_);
v_val_2268_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2266_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_val_2268_);
lean_dec(v___x_2266_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
lean_ctor_set_tag(v___x_2270_, 0);
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_val_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_res_2282_; 
v_res_2282_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2282_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2286_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2287_ = lean_unsigned_to_nat(58u);
v___x_2288_ = lean_unsigned_to_nat(33u);
v___x_2289_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2290_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2291_ = l_mkPanicMessageWithDecl(v___x_2290_, v___x_2289_, v___x_2288_, v___x_2287_, v___x_2286_);
return v___x_2291_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2293_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2294_ = lean_unsigned_to_nat(60u);
v___x_2295_ = lean_unsigned_to_nat(30u);
v___x_2296_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2297_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2298_ = l_mkPanicMessageWithDecl(v___x_2297_, v___x_2296_, v___x_2295_, v___x_2294_, v___x_2293_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2299_, lean_object* v_indName_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_, lean_object* v_a_2303_, lean_object* v_a_2304_){
_start:
{
lean_object* v___x_2306_; 
lean_inc(v_indName_2300_);
v___x_2306_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2300_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref_known(v___x_2306_, 1);
if (lean_obj_tag(v_a_2307_) == 5)
{
lean_object* v_val_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2494_; 
v_val_2308_ = lean_ctor_get(v_a_2307_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_a_2307_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2310_ = v_a_2307_;
v_isShared_2311_ = v_isSharedCheck_2494_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_val_2308_);
lean_dec(v_a_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2494_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_inc(v_indName_2300_);
v___x_2312_ = l_Lean_mkCasesOnName(v_indName_2300_);
lean_inc(v___x_2312_);
v___x_2313_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2312_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v_name_2315_; lean_object* v_levelParams_2316_; lean_object* v_type_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v_name_2315_ = lean_ctor_get(v_a_2314_, 0);
lean_inc(v_name_2315_);
v_levelParams_2316_ = lean_ctor_get(v_a_2314_, 1);
lean_inc_n(v_levelParams_2316_, 2);
v_type_2317_ = lean_ctor_get(v_a_2314_, 2);
lean_inc_ref(v_type_2317_);
lean_dec(v_a_2314_);
v___x_2318_ = lean_box(0);
v___x_2319_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2316_, v___x_2318_);
if (lean_obj_tag(v___x_2319_) == 1)
{
lean_object* v_head_2320_; lean_object* v_tail_2321_; lean_object* v_numParams_2322_; lean_object* v_numIndices_2323_; lean_object* v_ctors_2324_; lean_object* v___f_2325_; lean_object* v___x_2327_; 
v_head_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_head_2320_);
v_tail_2321_ = lean_ctor_get(v___x_2319_, 1);
lean_inc(v_tail_2321_);
v_numParams_2322_ = lean_ctor_get(v_val_2308_, 1);
lean_inc_n(v_numParams_2322_, 2);
v_numIndices_2323_ = lean_ctor_get(v_val_2308_, 2);
lean_inc(v_numIndices_2323_);
v_ctors_2324_ = lean_ctor_get(v_val_2308_, 4);
lean_inc(v_ctors_2324_);
v___f_2325_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2325_, 0, v_numIndices_2323_);
lean_closure_set(v___f_2325_, 1, v_head_2320_);
lean_closure_set(v___f_2325_, 2, v_ctors_2324_);
lean_closure_set(v___f_2325_, 3, v_tail_2321_);
lean_closure_set(v___f_2325_, 4, v_numParams_2322_);
lean_closure_set(v___f_2325_, 5, v_indName_2300_);
lean_closure_set(v___f_2325_, 6, v_val_2308_);
lean_closure_set(v___f_2325_, 7, v___x_2319_);
lean_closure_set(v___f_2325_, 8, v___x_2312_);
lean_closure_set(v___f_2325_, 9, v_name_2315_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set_tag(v___x_2310_, 1);
lean_ctor_set(v___x_2310_, 0, v_numParams_2322_);
v___x_2327_ = v___x_2310_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_numParams_2322_);
v___x_2327_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
uint8_t v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = 0;
v___x_2329_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2317_, v___x_2327_, v___f_2325_, v___x_2328_, v___x_2328_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2331_; lean_object* v___f_2332_; uint8_t v___y_2334_; uint8_t v___x_2473_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
lean_inc(v_a_2330_);
lean_dec_ref_known(v___x_2329_, 1);
v___x_2331_ = lean_box(v___x_2328_);
lean_inc(v_declName_2299_);
v___f_2332_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2332_, 0, v_a_2330_);
lean_closure_set(v___f_2332_, 1, v_declName_2299_);
lean_closure_set(v___f_2332_, 2, v_levelParams_2316_);
lean_closure_set(v___f_2332_, 3, v___x_2331_);
v___x_2473_ = l_Lean_isPrivateName(v_declName_2299_);
if (v___x_2473_ == 0)
{
uint8_t v___x_2474_; 
v___x_2474_ = 1;
v___y_2334_ = v___x_2474_;
goto v___jp_2333_;
}
else
{
v___y_2334_ = v___x_2328_;
goto v___jp_2333_;
}
v___jp_2333_:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2332_, v___y_2334_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v___x_2336_; lean_object* v_env_2337_; lean_object* v_nextMacroScope_2338_; lean_object* v_ngen_2339_; lean_object* v_auxDeclNGen_2340_; lean_object* v_traceState_2341_; lean_object* v_messages_2342_; lean_object* v_infoState_2343_; lean_object* v_snapshotTasks_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2471_; 
lean_dec_ref_known(v___x_2335_, 1);
v___x_2336_ = lean_st_ref_take(v_a_2304_);
v_env_2337_ = lean_ctor_get(v___x_2336_, 0);
v_nextMacroScope_2338_ = lean_ctor_get(v___x_2336_, 1);
v_ngen_2339_ = lean_ctor_get(v___x_2336_, 2);
v_auxDeclNGen_2340_ = lean_ctor_get(v___x_2336_, 3);
v_traceState_2341_ = lean_ctor_get(v___x_2336_, 4);
v_messages_2342_ = lean_ctor_get(v___x_2336_, 6);
v_infoState_2343_ = lean_ctor_get(v___x_2336_, 7);
v_snapshotTasks_2344_ = lean_ctor_get(v___x_2336_, 8);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2471_ == 0)
{
lean_object* v_unused_2472_; 
v_unused_2472_ = lean_ctor_get(v___x_2336_, 5);
lean_dec(v_unused_2472_);
v___x_2346_ = v___x_2336_;
v_isShared_2347_ = v_isSharedCheck_2471_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_snapshotTasks_2344_);
lean_inc(v_infoState_2343_);
lean_inc(v_messages_2342_);
lean_inc(v_traceState_2341_);
lean_inc(v_auxDeclNGen_2340_);
lean_inc(v_ngen_2339_);
lean_inc(v_nextMacroScope_2338_);
lean_inc(v_env_2337_);
lean_dec(v___x_2336_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2471_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
lean_inc(v_declName_2299_);
v___x_2348_ = l_Lean_Meta_markMatcherLike(v_env_2337_, v_declName_2299_);
v___x_2349_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2347_ == 0)
{
lean_ctor_set(v___x_2346_, 5, v___x_2349_);
lean_ctor_set(v___x_2346_, 0, v___x_2348_);
v___x_2351_ = v___x_2346_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_nextMacroScope_2338_);
lean_ctor_set(v_reuseFailAlloc_2470_, 2, v_ngen_2339_);
lean_ctor_set(v_reuseFailAlloc_2470_, 3, v_auxDeclNGen_2340_);
lean_ctor_set(v_reuseFailAlloc_2470_, 4, v_traceState_2341_);
lean_ctor_set(v_reuseFailAlloc_2470_, 5, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2470_, 6, v_messages_2342_);
lean_ctor_set(v_reuseFailAlloc_2470_, 7, v_infoState_2343_);
lean_ctor_set(v_reuseFailAlloc_2470_, 8, v_snapshotTasks_2344_);
v___x_2351_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v_mctx_2354_; lean_object* v_zetaDeltaFVarIds_2355_; lean_object* v_postponed_2356_; lean_object* v_diag_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2468_; 
v___x_2352_ = lean_st_ref_put(v_a_2304_, v___x_2351_);
v___x_2353_ = lean_st_ref_take(v_a_2302_);
v_mctx_2354_ = lean_ctor_get(v___x_2353_, 0);
v_zetaDeltaFVarIds_2355_ = lean_ctor_get(v___x_2353_, 2);
v_postponed_2356_ = lean_ctor_get(v___x_2353_, 3);
v_diag_2357_ = lean_ctor_get(v___x_2353_, 4);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2468_ == 0)
{
lean_object* v_unused_2469_; 
v_unused_2469_ = lean_ctor_get(v___x_2353_, 1);
lean_dec(v_unused_2469_);
v___x_2359_ = v___x_2353_;
v_isShared_2360_ = v_isSharedCheck_2468_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_diag_2357_);
lean_inc(v_postponed_2356_);
lean_inc(v_zetaDeltaFVarIds_2355_);
lean_inc(v_mctx_2354_);
lean_dec(v___x_2353_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2468_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2361_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 1, v___x_2361_);
v___x_2363_ = v___x_2359_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_mctx_2354_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2467_, 2, v_zetaDeltaFVarIds_2355_);
lean_ctor_set(v_reuseFailAlloc_2467_, 3, v_postponed_2356_);
lean_ctor_set(v_reuseFailAlloc_2467_, 4, v_diag_2357_);
v___x_2363_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v_env_2366_; lean_object* v_nextMacroScope_2367_; lean_object* v_ngen_2368_; lean_object* v_auxDeclNGen_2369_; lean_object* v_traceState_2370_; lean_object* v_messages_2371_; lean_object* v_infoState_2372_; lean_object* v_snapshotTasks_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2465_; 
v___x_2364_ = lean_st_ref_put(v_a_2302_, v___x_2363_);
v___x_2365_ = lean_st_ref_take(v_a_2304_);
v_env_2366_ = lean_ctor_get(v___x_2365_, 0);
v_nextMacroScope_2367_ = lean_ctor_get(v___x_2365_, 1);
v_ngen_2368_ = lean_ctor_get(v___x_2365_, 2);
v_auxDeclNGen_2369_ = lean_ctor_get(v___x_2365_, 3);
v_traceState_2370_ = lean_ctor_get(v___x_2365_, 4);
v_messages_2371_ = lean_ctor_get(v___x_2365_, 6);
v_infoState_2372_ = lean_ctor_get(v___x_2365_, 7);
v_snapshotTasks_2373_ = lean_ctor_get(v___x_2365_, 8);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2465_ == 0)
{
lean_object* v_unused_2466_; 
v_unused_2466_ = lean_ctor_get(v___x_2365_, 5);
lean_dec(v_unused_2466_);
v___x_2375_ = v___x_2365_;
v_isShared_2376_ = v_isSharedCheck_2465_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_snapshotTasks_2373_);
lean_inc(v_infoState_2372_);
lean_inc(v_messages_2371_);
lean_inc(v_traceState_2370_);
lean_inc(v_auxDeclNGen_2369_);
lean_inc(v_ngen_2368_);
lean_inc(v_nextMacroScope_2367_);
lean_inc(v_env_2366_);
lean_dec(v___x_2365_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2465_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2377_; lean_object* v___x_2379_; 
lean_inc(v_declName_2299_);
v___x_2377_ = l_Lean_markAuxRecursor(v_env_2366_, v_declName_2299_);
if (v_isShared_2376_ == 0)
{
lean_ctor_set(v___x_2375_, 5, v___x_2349_);
lean_ctor_set(v___x_2375_, 0, v___x_2377_);
v___x_2379_ = v___x_2375_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2377_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_nextMacroScope_2367_);
lean_ctor_set(v_reuseFailAlloc_2464_, 2, v_ngen_2368_);
lean_ctor_set(v_reuseFailAlloc_2464_, 3, v_auxDeclNGen_2369_);
lean_ctor_set(v_reuseFailAlloc_2464_, 4, v_traceState_2370_);
lean_ctor_set(v_reuseFailAlloc_2464_, 5, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2464_, 6, v_messages_2371_);
lean_ctor_set(v_reuseFailAlloc_2464_, 7, v_infoState_2372_);
lean_ctor_set(v_reuseFailAlloc_2464_, 8, v_snapshotTasks_2373_);
v___x_2379_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v_mctx_2382_; lean_object* v_zetaDeltaFVarIds_2383_; lean_object* v_postponed_2384_; lean_object* v_diag_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2462_; 
v___x_2380_ = lean_st_ref_put(v_a_2304_, v___x_2379_);
v___x_2381_ = lean_st_ref_take(v_a_2302_);
v_mctx_2382_ = lean_ctor_get(v___x_2381_, 0);
v_zetaDeltaFVarIds_2383_ = lean_ctor_get(v___x_2381_, 2);
v_postponed_2384_ = lean_ctor_get(v___x_2381_, 3);
v_diag_2385_ = lean_ctor_get(v___x_2381_, 4);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2381_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; 
v_unused_2463_ = lean_ctor_get(v___x_2381_, 1);
lean_dec(v_unused_2463_);
v___x_2387_ = v___x_2381_;
v_isShared_2388_ = v_isSharedCheck_2462_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_diag_2385_);
lean_inc(v_postponed_2384_);
lean_inc(v_zetaDeltaFVarIds_2383_);
lean_inc(v_mctx_2382_);
lean_dec(v___x_2381_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2462_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 1, v___x_2361_);
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_mctx_2382_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_zetaDeltaFVarIds_2383_);
lean_ctor_set(v_reuseFailAlloc_2461_, 3, v_postponed_2384_);
lean_ctor_set(v_reuseFailAlloc_2461_, 4, v_diag_2385_);
v___x_2390_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v_env_2393_; lean_object* v_nextMacroScope_2394_; lean_object* v_ngen_2395_; lean_object* v_auxDeclNGen_2396_; lean_object* v_traceState_2397_; lean_object* v_messages_2398_; lean_object* v_infoState_2399_; lean_object* v_snapshotTasks_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2459_; 
v___x_2391_ = lean_st_ref_put(v_a_2302_, v___x_2390_);
v___x_2392_ = lean_st_ref_take(v_a_2304_);
v_env_2393_ = lean_ctor_get(v___x_2392_, 0);
v_nextMacroScope_2394_ = lean_ctor_get(v___x_2392_, 1);
v_ngen_2395_ = lean_ctor_get(v___x_2392_, 2);
v_auxDeclNGen_2396_ = lean_ctor_get(v___x_2392_, 3);
v_traceState_2397_ = lean_ctor_get(v___x_2392_, 4);
v_messages_2398_ = lean_ctor_get(v___x_2392_, 6);
v_infoState_2399_ = lean_ctor_get(v___x_2392_, 7);
v_snapshotTasks_2400_ = lean_ctor_get(v___x_2392_, 8);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2459_ == 0)
{
lean_object* v_unused_2460_; 
v_unused_2460_ = lean_ctor_get(v___x_2392_, 5);
lean_dec(v_unused_2460_);
v___x_2402_ = v___x_2392_;
v_isShared_2403_ = v_isSharedCheck_2459_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_snapshotTasks_2400_);
lean_inc(v_infoState_2399_);
lean_inc(v_messages_2398_);
lean_inc(v_traceState_2397_);
lean_inc(v_auxDeclNGen_2396_);
lean_inc(v_ngen_2395_);
lean_inc(v_nextMacroScope_2394_);
lean_inc(v_env_2393_);
lean_dec(v___x_2392_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2459_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
lean_inc(v_declName_2299_);
v___x_2404_ = l_Lean_Meta_addToCompletionBlackList(v_env_2393_, v_declName_2299_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 5, v___x_2349_);
lean_ctor_set(v___x_2402_, 0, v___x_2404_);
v___x_2406_ = v___x_2402_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_nextMacroScope_2394_);
lean_ctor_set(v_reuseFailAlloc_2458_, 2, v_ngen_2395_);
lean_ctor_set(v_reuseFailAlloc_2458_, 3, v_auxDeclNGen_2396_);
lean_ctor_set(v_reuseFailAlloc_2458_, 4, v_traceState_2397_);
lean_ctor_set(v_reuseFailAlloc_2458_, 5, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2458_, 6, v_messages_2398_);
lean_ctor_set(v_reuseFailAlloc_2458_, 7, v_infoState_2399_);
lean_ctor_set(v_reuseFailAlloc_2458_, 8, v_snapshotTasks_2400_);
v___x_2406_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v_mctx_2409_; lean_object* v_zetaDeltaFVarIds_2410_; lean_object* v_postponed_2411_; lean_object* v_diag_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2456_; 
v___x_2407_ = lean_st_ref_put(v_a_2304_, v___x_2406_);
v___x_2408_ = lean_st_ref_take(v_a_2302_);
v_mctx_2409_ = lean_ctor_get(v___x_2408_, 0);
v_zetaDeltaFVarIds_2410_ = lean_ctor_get(v___x_2408_, 2);
v_postponed_2411_ = lean_ctor_get(v___x_2408_, 3);
v_diag_2412_ = lean_ctor_get(v___x_2408_, 4);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; 
v_unused_2457_ = lean_ctor_get(v___x_2408_, 1);
lean_dec(v_unused_2457_);
v___x_2414_ = v___x_2408_;
v_isShared_2415_ = v_isSharedCheck_2456_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_diag_2412_);
lean_inc(v_postponed_2411_);
lean_inc(v_zetaDeltaFVarIds_2410_);
lean_inc(v_mctx_2409_);
lean_dec(v___x_2408_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2456_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
lean_ctor_set(v___x_2414_, 1, v___x_2361_);
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_mctx_2409_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_zetaDeltaFVarIds_2410_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_postponed_2411_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v_diag_2412_);
v___x_2417_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v_env_2420_; lean_object* v_nextMacroScope_2421_; lean_object* v_ngen_2422_; lean_object* v_auxDeclNGen_2423_; lean_object* v_traceState_2424_; lean_object* v_messages_2425_; lean_object* v_infoState_2426_; lean_object* v_snapshotTasks_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2453_; 
v___x_2418_ = lean_st_ref_put(v_a_2302_, v___x_2417_);
v___x_2419_ = lean_st_ref_take(v_a_2304_);
v_env_2420_ = lean_ctor_get(v___x_2419_, 0);
v_nextMacroScope_2421_ = lean_ctor_get(v___x_2419_, 1);
v_ngen_2422_ = lean_ctor_get(v___x_2419_, 2);
v_auxDeclNGen_2423_ = lean_ctor_get(v___x_2419_, 3);
v_traceState_2424_ = lean_ctor_get(v___x_2419_, 4);
v_messages_2425_ = lean_ctor_get(v___x_2419_, 6);
v_infoState_2426_ = lean_ctor_get(v___x_2419_, 7);
v_snapshotTasks_2427_ = lean_ctor_get(v___x_2419_, 8);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v___x_2419_, 5);
lean_dec(v_unused_2454_);
v___x_2429_ = v___x_2419_;
v_isShared_2430_ = v_isSharedCheck_2453_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_snapshotTasks_2427_);
lean_inc(v_infoState_2426_);
lean_inc(v_messages_2425_);
lean_inc(v_traceState_2424_);
lean_inc(v_auxDeclNGen_2423_);
lean_inc(v_ngen_2422_);
lean_inc(v_nextMacroScope_2421_);
lean_inc(v_env_2420_);
lean_dec(v___x_2419_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2453_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___x_2433_; 
lean_inc(v_declName_2299_);
v___x_2431_ = l_Lean_addProtected(v_env_2420_, v_declName_2299_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 5, v___x_2349_);
lean_ctor_set(v___x_2429_, 0, v___x_2431_);
v___x_2433_ = v___x_2429_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2431_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_nextMacroScope_2421_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_ngen_2422_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_auxDeclNGen_2423_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v_traceState_2424_);
lean_ctor_set(v_reuseFailAlloc_2452_, 5, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2452_, 6, v_messages_2425_);
lean_ctor_set(v_reuseFailAlloc_2452_, 7, v_infoState_2426_);
lean_ctor_set(v_reuseFailAlloc_2452_, 8, v_snapshotTasks_2427_);
v___x_2433_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v_mctx_2436_; lean_object* v_zetaDeltaFVarIds_2437_; lean_object* v_postponed_2438_; lean_object* v_diag_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2450_; 
v___x_2434_ = lean_st_ref_put(v_a_2304_, v___x_2433_);
v___x_2435_ = lean_st_ref_take(v_a_2302_);
v_mctx_2436_ = lean_ctor_get(v___x_2435_, 0);
v_zetaDeltaFVarIds_2437_ = lean_ctor_get(v___x_2435_, 2);
v_postponed_2438_ = lean_ctor_get(v___x_2435_, 3);
v_diag_2439_ = lean_ctor_get(v___x_2435_, 4);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; 
v_unused_2451_ = lean_ctor_get(v___x_2435_, 1);
lean_dec(v_unused_2451_);
v___x_2441_ = v___x_2435_;
v_isShared_2442_ = v_isSharedCheck_2450_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_diag_2439_);
lean_inc(v_postponed_2438_);
lean_inc(v_zetaDeltaFVarIds_2437_);
lean_inc(v_mctx_2436_);
lean_dec(v___x_2435_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2450_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 1, v___x_2361_);
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_mctx_2436_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v___x_2361_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_zetaDeltaFVarIds_2437_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v_postponed_2438_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v_diag_2439_);
v___x_2444_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = lean_st_ref_put(v_a_2302_, v___x_2444_);
v___x_2446_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2299_);
v___x_2447_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_2446_, v_declName_2299_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v___x_2448_; 
lean_dec_ref_known(v___x_2447_, 1);
v___x_2448_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_declName_2299_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
return v___x_2448_;
}
else
{
lean_dec(v_declName_2299_);
return v___x_2447_;
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
lean_dec(v_declName_2299_);
return v___x_2335_;
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v_levelParams_2316_);
lean_dec(v_declName_2299_);
v_a_2475_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2329_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2329_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
else
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec(v___x_2319_);
lean_dec_ref(v_type_2317_);
lean_dec(v_levelParams_2316_);
lean_dec(v_name_2315_);
lean_dec(v___x_2312_);
lean_del_object(v___x_2310_);
lean_dec_ref(v_val_2308_);
lean_dec(v_indName_2300_);
lean_dec(v_declName_2299_);
v___x_2484_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2485_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2484_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
return v___x_2485_;
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec(v___x_2312_);
lean_del_object(v___x_2310_);
lean_dec_ref(v_val_2308_);
lean_dec(v_indName_2300_);
lean_dec(v_declName_2299_);
v_a_2486_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2313_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2313_);
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
lean_dec(v_a_2307_);
lean_dec(v_indName_2300_);
lean_dec(v_declName_2299_);
v___x_2495_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2496_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_2495_, v_a_2301_, v_a_2302_, v_a_2303_, v_a_2304_);
return v___x_2496_;
}
}
else
{
lean_object* v_a_2497_; lean_object* v___x_2499_; uint8_t v_isShared_2500_; uint8_t v_isSharedCheck_2504_; 
lean_dec(v_indName_2300_);
lean_dec(v_declName_2299_);
v_a_2497_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2499_ = v___x_2306_;
v_isShared_2500_ = v_isSharedCheck_2504_;
goto v_resetjp_2498_;
}
else
{
lean_inc(v_a_2497_);
lean_dec(v___x_2306_);
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
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2505_, lean_object* v_indName_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2505_, v_indName_2506_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
lean_dec(v_a_2508_);
lean_dec_ref(v_a_2507_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2513_, lean_object* v_name_2514_, lean_object* v_type_2515_, lean_object* v_k_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v___x_2522_; 
v___x_2522_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2514_, v_type_2515_, v_k_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
return v___x_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2523_, lean_object* v_name_2524_, lean_object* v_type_2525_, lean_object* v_k_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2523_, v_name_2524_, v_type_2525_, v_k_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2533_, lean_object* v_params_2534_, lean_object* v_alts_2535_, lean_object* v___x_2536_, lean_object* v_ism2_2537_, lean_object* v_motive_2538_, lean_object* v_val_2539_, lean_object* v_indName_2540_, lean_object* v___x_2541_, lean_object* v___x_2542_, lean_object* v___x_2543_, lean_object* v_as_2544_, size_t v_sz_2545_, size_t v_i_2546_, lean_object* v_bs_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___x_2553_; 
v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2533_, v_params_2534_, v_alts_2535_, v___x_2536_, v_ism2_2537_, v_motive_2538_, v_val_2539_, v_indName_2540_, v___x_2541_, v___x_2542_, v___x_2543_, v_sz_2545_, v_i_2546_, v_bs_2547_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2554_ = _args[0];
lean_object* v_params_2555_ = _args[1];
lean_object* v_alts_2556_ = _args[2];
lean_object* v___x_2557_ = _args[3];
lean_object* v_ism2_2558_ = _args[4];
lean_object* v_motive_2559_ = _args[5];
lean_object* v_val_2560_ = _args[6];
lean_object* v_indName_2561_ = _args[7];
lean_object* v___x_2562_ = _args[8];
lean_object* v___x_2563_ = _args[9];
lean_object* v___x_2564_ = _args[10];
lean_object* v_as_2565_ = _args[11];
lean_object* v_sz_2566_ = _args[12];
lean_object* v_i_2567_ = _args[13];
lean_object* v_bs_2568_ = _args[14];
lean_object* v___y_2569_ = _args[15];
lean_object* v___y_2570_ = _args[16];
lean_object* v___y_2571_ = _args[17];
lean_object* v___y_2572_ = _args[18];
lean_object* v___y_2573_ = _args[19];
_start:
{
size_t v_sz_boxed_2574_; size_t v_i_boxed_2575_; lean_object* v_res_2576_; 
v_sz_boxed_2574_ = lean_unbox_usize(v_sz_2566_);
lean_dec(v_sz_2566_);
v_i_boxed_2575_ = lean_unbox_usize(v_i_2567_);
lean_dec(v_i_2567_);
v_res_2576_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2554_, v_params_2555_, v_alts_2556_, v___x_2557_, v_ism2_2558_, v_motive_2559_, v_val_2560_, v_indName_2561_, v___x_2562_, v___x_2563_, v___x_2564_, v_as_2565_, v_sz_boxed_2574_, v_i_boxed_2575_, v_bs_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec_ref(v_as_2565_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2577_, lean_object* v_params_2578_, lean_object* v___x_2579_, lean_object* v_motive_2580_, lean_object* v_as_2581_, size_t v_sz_2582_, size_t v_i_2583_, lean_object* v_bs_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2577_, v_params_2578_, v___x_2579_, v_motive_2580_, v_sz_2582_, v_i_2583_, v_bs_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2591_, lean_object* v_params_2592_, lean_object* v___x_2593_, lean_object* v_motive_2594_, lean_object* v_as_2595_, lean_object* v_sz_2596_, lean_object* v_i_2597_, lean_object* v_bs_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
size_t v_sz_boxed_2604_; size_t v_i_boxed_2605_; lean_object* v_res_2606_; 
v_sz_boxed_2604_ = lean_unbox_usize(v_sz_2596_);
lean_dec(v_sz_2596_);
v_i_boxed_2605_ = lean_unbox_usize(v_i_2597_);
lean_dec(v_i_2597_);
v_res_2606_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2591_, v_params_2592_, v___x_2593_, v_motive_2594_, v_as_2595_, v_sz_boxed_2604_, v_i_boxed_2605_, v_bs_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec_ref(v_as_2595_);
lean_dec_ref(v_params_2592_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_declName_2607_, uint8_t v_s_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_2607_, v_s_2608_, v___y_2610_, v___y_2612_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_declName_2615_, lean_object* v_s_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_){
_start:
{
uint8_t v_s_boxed_2622_; lean_object* v_res_2623_; 
v_s_boxed_2622_ = lean_unbox(v_s_2616_);
v_res_2623_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_2615_, v_s_boxed_2622_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
lean_dec_ref(v___y_2619_);
lean_dec(v___y_2618_);
lean_dec_ref(v___y_2617_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2624_, lean_object* v_constName_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2632_, lean_object* v_constName_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v_res_2639_; 
v_res_2639_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2632_, v_constName_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b1_2640_, lean_object* v_attrName_2641_, lean_object* v_declName_2642_, lean_object* v_asyncPrefix_x3f_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v___x_2649_; 
v___x_2649_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_2641_, v_declName_2642_, v_asyncPrefix_x3f_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(lean_object* v_00_u03b1_2650_, lean_object* v_attrName_2651_, lean_object* v_declName_2652_, lean_object* v_asyncPrefix_x3f_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_2650_, v_attrName_2651_, v_declName_2652_, v_asyncPrefix_x3f_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(lean_object* v_00_u03b1_2660_, lean_object* v_attrName_2661_, lean_object* v_declName_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_2661_, v_declName_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(lean_object* v_00_u03b1_2669_, lean_object* v_attrName_2670_, lean_object* v_declName_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_2669_, v_attrName_2670_, v_declName_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(lean_object* v_00_u03b1_2678_, lean_object* v_ref_2679_, lean_object* v_constName_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_2679_, v_constName_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(lean_object* v_00_u03b1_2687_, lean_object* v_ref_2688_, lean_object* v_constName_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_2687_, v_ref_2688_, v_constName_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v_ref_2688_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(lean_object* v_00_u03b1_2696_, lean_object* v_msg_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(lean_object* v_00_u03b1_2704_, lean_object* v_msg_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_2704_, v_msg_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(lean_object* v_00_u03b1_2712_, lean_object* v_ref_2713_, lean_object* v_msg_2714_, lean_object* v_declHint_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_2713_, v_msg_2714_, v_declHint_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(lean_object* v_00_u03b1_2722_, lean_object* v_ref_2723_, lean_object* v_msg_2724_, lean_object* v_declHint_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_2722_, v_ref_2723_, v_msg_2724_, v_declHint_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v_ref_2723_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(lean_object* v_msg_2732_, lean_object* v_declHint_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_2732_, v_declHint_2733_, v___y_2737_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(lean_object* v_msg_2740_, lean_object* v_declHint_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_2740_, v_declHint_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(lean_object* v_00_u03b1_2748_, lean_object* v_ref_2749_, lean_object* v_msg_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_2749_, v_msg_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(lean_object* v_00_u03b1_2757_, lean_object* v_ref_2758_, lean_object* v_msg_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_2757_, v_ref_2758_, v_msg_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_ref_2758_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2766_, lean_object* v___y_2767_){
_start:
{
uint8_t v___x_2769_; 
v___x_2769_ = l_Lean_Expr_hasMVar(v_e_2766_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
v___x_2770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2770_, 0, v_e_2766_);
return v___x_2770_;
}
else
{
lean_object* v___x_2771_; lean_object* v_mctx_2772_; lean_object* v___x_2773_; lean_object* v_fst_2774_; lean_object* v_snd_2775_; lean_object* v___x_2776_; lean_object* v_cache_2777_; lean_object* v_zetaDeltaFVarIds_2778_; lean_object* v_postponed_2779_; lean_object* v_diag_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2789_; 
v___x_2771_ = lean_st_ref_get(v___y_2767_);
v_mctx_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc_ref(v_mctx_2772_);
lean_dec(v___x_2771_);
v___x_2773_ = l_Lean_instantiateMVarsCore(v_mctx_2772_, v_e_2766_);
v_fst_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_fst_2774_);
v_snd_2775_ = lean_ctor_get(v___x_2773_, 1);
lean_inc(v_snd_2775_);
lean_dec_ref(v___x_2773_);
v___x_2776_ = lean_st_ref_take(v___y_2767_);
v_cache_2777_ = lean_ctor_get(v___x_2776_, 1);
v_zetaDeltaFVarIds_2778_ = lean_ctor_get(v___x_2776_, 2);
v_postponed_2779_ = lean_ctor_get(v___x_2776_, 3);
v_diag_2780_ = lean_ctor_get(v___x_2776_, 4);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v___x_2776_, 0);
lean_dec(v_unused_2790_);
v___x_2782_ = v___x_2776_;
v_isShared_2783_ = v_isSharedCheck_2789_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_diag_2780_);
lean_inc(v_postponed_2779_);
lean_inc(v_zetaDeltaFVarIds_2778_);
lean_inc(v_cache_2777_);
lean_dec(v___x_2776_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2789_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v_snd_2775_);
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_snd_2775_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_cache_2777_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_zetaDeltaFVarIds_2778_);
lean_ctor_set(v_reuseFailAlloc_2788_, 3, v_postponed_2779_);
lean_ctor_set(v_reuseFailAlloc_2788_, 4, v_diag_2780_);
v___x_2785_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_st_ref_put(v___y_2767_, v___x_2785_);
v___x_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2787_, 0, v_fst_2774_);
return v___x_2787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2791_, v___y_2792_);
lean_dec(v___y_2792_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2795_, v___y_2797_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2809_, lean_object* v_info_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_){
_start:
{
lean_object* v___x_2814_; lean_object* v_env_2815_; lean_object* v_nextMacroScope_2816_; lean_object* v_ngen_2817_; lean_object* v_auxDeclNGen_2818_; lean_object* v_traceState_2819_; lean_object* v_messages_2820_; lean_object* v_infoState_2821_; lean_object* v_snapshotTasks_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2849_; 
v___x_2814_ = lean_st_ref_take(v___y_2812_);
v_env_2815_ = lean_ctor_get(v___x_2814_, 0);
v_nextMacroScope_2816_ = lean_ctor_get(v___x_2814_, 1);
v_ngen_2817_ = lean_ctor_get(v___x_2814_, 2);
v_auxDeclNGen_2818_ = lean_ctor_get(v___x_2814_, 3);
v_traceState_2819_ = lean_ctor_get(v___x_2814_, 4);
v_messages_2820_ = lean_ctor_get(v___x_2814_, 6);
v_infoState_2821_ = lean_ctor_get(v___x_2814_, 7);
v_snapshotTasks_2822_ = lean_ctor_get(v___x_2814_, 8);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v___x_2814_, 5);
lean_dec(v_unused_2850_);
v___x_2824_ = v___x_2814_;
v_isShared_2825_ = v_isSharedCheck_2849_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_snapshotTasks_2822_);
lean_inc(v_infoState_2821_);
lean_inc(v_messages_2820_);
lean_inc(v_traceState_2819_);
lean_inc(v_auxDeclNGen_2818_);
lean_inc(v_ngen_2817_);
lean_inc(v_nextMacroScope_2816_);
lean_inc(v_env_2815_);
lean_dec(v___x_2814_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2849_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
v___x_2826_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_2815_, v_matcherName_2809_, v_info_2810_);
v___x_2827_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
if (v_isShared_2825_ == 0)
{
lean_ctor_set(v___x_2824_, 5, v___x_2827_);
lean_ctor_set(v___x_2824_, 0, v___x_2826_);
v___x_2829_ = v___x_2824_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_nextMacroScope_2816_);
lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_ngen_2817_);
lean_ctor_set(v_reuseFailAlloc_2848_, 3, v_auxDeclNGen_2818_);
lean_ctor_set(v_reuseFailAlloc_2848_, 4, v_traceState_2819_);
lean_ctor_set(v_reuseFailAlloc_2848_, 5, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2848_, 6, v_messages_2820_);
lean_ctor_set(v_reuseFailAlloc_2848_, 7, v_infoState_2821_);
lean_ctor_set(v_reuseFailAlloc_2848_, 8, v_snapshotTasks_2822_);
v___x_2829_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v_mctx_2832_; lean_object* v_zetaDeltaFVarIds_2833_; lean_object* v_postponed_2834_; lean_object* v_diag_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2846_; 
v___x_2830_ = lean_st_ref_put(v___y_2812_, v___x_2829_);
v___x_2831_ = lean_st_ref_take(v___y_2811_);
v_mctx_2832_ = lean_ctor_get(v___x_2831_, 0);
v_zetaDeltaFVarIds_2833_ = lean_ctor_get(v___x_2831_, 2);
v_postponed_2834_ = lean_ctor_get(v___x_2831_, 3);
v_diag_2835_ = lean_ctor_get(v___x_2831_, 4);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v___x_2831_, 1);
lean_dec(v_unused_2847_);
v___x_2837_ = v___x_2831_;
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_diag_2835_);
lean_inc(v_postponed_2834_);
lean_inc(v_zetaDeltaFVarIds_2833_);
lean_inc(v_mctx_2832_);
lean_dec(v___x_2831_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2839_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v___x_2839_);
v___x_2841_ = v___x_2837_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_mctx_2832_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_zetaDeltaFVarIds_2833_);
lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_postponed_2834_);
lean_ctor_set(v_reuseFailAlloc_2845_, 4, v_diag_2835_);
v___x_2841_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = lean_st_ref_put(v___y_2811_, v___x_2841_);
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_2851_, lean_object* v_info_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2851_, v_info_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec(v___y_2853_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_2857_, lean_object* v_info_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_2857_, v_info_2858_, v___y_2860_, v___y_2862_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_2865_, lean_object* v_info_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_2865_, v_info_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_);
lean_dec(v___y_2870_);
lean_dec_ref(v___y_2869_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2873_, lean_object* v___x_2874_, lean_object* v_newEqs1_2875_, uint8_t v___x_2876_, uint8_t v___x_2877_, uint8_t v___x_2878_, lean_object* v_ism1_x27_2879_, lean_object* v_ism2_x27_2880_, lean_object* v_newRefls1_2881_, lean_object* v_newEqs2_2882_, lean_object* v_newRefls2_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2889_ = l_Lean_mkAppN(v_motive_2873_, v___x_2874_);
v___x_2890_ = l_Array_append___redArg(v_newEqs1_2875_, v_newEqs2_2882_);
v___x_2891_ = l_Lean_Meta_mkForallFVars(v___x_2890_, v___x_2889_, v___x_2876_, v___x_2877_, v___x_2877_, v___x_2878_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec_ref(v___x_2890_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
v___x_2893_ = l_Array_append___redArg(v_ism1_x27_2879_, v_ism2_x27_2880_);
v___x_2894_ = l_Lean_Meta_mkLambdaFVars(v___x_2893_, v_a_2892_, v___x_2876_, v___x_2877_, v___x_2876_, v___x_2877_, v___x_2878_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
lean_dec_ref(v___x_2893_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2904_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2897_ = v___x_2894_;
v_isShared_2898_ = v_isSharedCheck_2904_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2894_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2904_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2899_ = l_Array_append___redArg(v_newRefls1_2881_, v_newRefls2_2883_);
v___x_2900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2900_, 0, v_a_2895_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 0, v___x_2900_);
v___x_2902_ = v___x_2897_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec_ref(v_newRefls1_2881_);
v_a_2905_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2894_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2894_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v_newRefls1_2881_);
lean_dec_ref(v_ism1_x27_2879_);
v_a_2913_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2891_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2891_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2921_, lean_object* v___x_2922_, lean_object* v_newEqs1_2923_, lean_object* v___x_2924_, lean_object* v___x_2925_, lean_object* v___x_2926_, lean_object* v_ism1_x27_2927_, lean_object* v_ism2_x27_2928_, lean_object* v_newRefls1_2929_, lean_object* v_newEqs2_2930_, lean_object* v_newRefls2_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
uint8_t v___x_14914__boxed_2937_; uint8_t v___x_14915__boxed_2938_; uint8_t v___x_14916__boxed_2939_; lean_object* v_res_2940_; 
v___x_14914__boxed_2937_ = lean_unbox(v___x_2924_);
v___x_14915__boxed_2938_ = lean_unbox(v___x_2925_);
v___x_14916__boxed_2939_ = lean_unbox(v___x_2926_);
v_res_2940_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2921_, v___x_2922_, v_newEqs1_2923_, v___x_14914__boxed_2937_, v___x_14915__boxed_2938_, v___x_14916__boxed_2939_, v_ism1_x27_2927_, v_ism2_x27_2928_, v_newRefls1_2929_, v_newEqs2_2930_, v_newRefls2_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec_ref(v_newRefls2_2931_);
lean_dec_ref(v_newEqs2_2930_);
lean_dec_ref(v_ism2_x27_2928_);
lean_dec_ref(v___x_2922_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2941_, lean_object* v___x_2942_, uint8_t v___x_2943_, uint8_t v___x_2944_, uint8_t v___x_2945_, lean_object* v_ism1_x27_2946_, lean_object* v_ism2_x27_2947_, lean_object* v_is_2948_, lean_object* v___x_2949_, lean_object* v_newEqs1_2950_, lean_object* v_newRefls1_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___f_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2957_ = lean_box(v___x_2943_);
v___x_2958_ = lean_box(v___x_2944_);
v___x_2959_ = lean_box(v___x_2945_);
lean_inc_ref(v_ism2_x27_2947_);
v___f_2960_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2960_, 0, v_motive_2941_);
lean_closure_set(v___f_2960_, 1, v___x_2942_);
lean_closure_set(v___f_2960_, 2, v_newEqs1_2950_);
lean_closure_set(v___f_2960_, 3, v___x_2957_);
lean_closure_set(v___f_2960_, 4, v___x_2958_);
lean_closure_set(v___f_2960_, 5, v___x_2959_);
lean_closure_set(v___f_2960_, 6, v_ism1_x27_2946_);
lean_closure_set(v___f_2960_, 7, v_ism2_x27_2947_);
lean_closure_set(v___f_2960_, 8, v_newRefls1_2951_);
v___x_2961_ = lean_array_push(v_is_2948_, v___x_2949_);
v___x_2962_ = l_Lean_Meta_withNewEqs___redArg(v___x_2961_, v_ism2_x27_2947_, v___f_2960_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2963_, lean_object* v___x_2964_, lean_object* v___x_2965_, lean_object* v___x_2966_, lean_object* v___x_2967_, lean_object* v_ism1_x27_2968_, lean_object* v_ism2_x27_2969_, lean_object* v_is_2970_, lean_object* v___x_2971_, lean_object* v_newEqs1_2972_, lean_object* v_newRefls1_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
uint8_t v___x_15005__boxed_2979_; uint8_t v___x_15006__boxed_2980_; uint8_t v___x_15007__boxed_2981_; lean_object* v_res_2982_; 
v___x_15005__boxed_2979_ = lean_unbox(v___x_2965_);
v___x_15006__boxed_2980_ = lean_unbox(v___x_2966_);
v___x_15007__boxed_2981_ = lean_unbox(v___x_2967_);
v_res_2982_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2963_, v___x_2964_, v___x_15005__boxed_2979_, v___x_15006__boxed_2980_, v___x_15007__boxed_2981_, v_ism1_x27_2968_, v_ism2_x27_2969_, v_is_2970_, v___x_2971_, v_newEqs1_2972_, v_newRefls1_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
return v_res_2982_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_2983_, uint8_t v___x_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Lean_addDecl(v___x_2983_, v___x_2984_, v___y_2987_, v___y_2988_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_2991_, lean_object* v___x_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
uint8_t v___x_15047__boxed_2998_; lean_object* v_res_2999_; 
v___x_15047__boxed_2998_ = lean_unbox(v___x_2992_);
v_res_2999_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_2991_, v___x_15047__boxed_2998_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
return v_res_2999_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3002_ = l_Lean_stringToMessageData(v___x_3001_);
return v___x_3002_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3005_ = l_Lean_stringToMessageData(v___x_3004_);
return v___x_3005_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3011_ = lean_box(0);
v___x_3012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3013_ = l_Lean_mkConst(v___x_3012_, v___x_3011_);
return v___x_3013_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3016_ = l_Lean_stringToMessageData(v___x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3017_, lean_object* v_a_3018_, lean_object* v___x_3019_, lean_object* v_zs1_3020_, lean_object* v_snd_3021_, uint8_t v___x_3022_, uint8_t v___x_3023_, uint8_t v___x_3024_, lean_object* v_alts_3025_, lean_object* v_zs2_3026_, lean_object* v___ctorRet2_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = lean_array_get_borrowed(v___x_3017_, v_a_3018_, v___x_3019_);
lean_inc_ref(v_zs1_3020_);
v___x_3034_ = l_Array_append___redArg(v_zs1_3020_, v_zs2_3026_);
lean_inc(v___x_3033_);
v___x_3035_ = l_Lean_Meta_instantiateForall(v___x_3033_, v___x_3034_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
v___x_3037_ = lean_box(0);
v___x_3038_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3036_, v___x_3037_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3038_) == 0)
{
lean_object* v_a_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; 
v_a_3039_ = lean_ctor_get(v___x_3038_, 0);
lean_inc(v_a_3039_);
lean_dec_ref_known(v___x_3038_, 1);
v___x_3040_ = l_Lean_Expr_mvarId_x21(v_a_3039_);
v___x_3041_ = lean_array_get_size(v_snd_3021_);
v___x_3042_ = lean_box(0);
v___x_3043_ = lean_box(0);
lean_inc_ref(v___y_3030_);
v___x_3044_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3041_, v___x_3040_, v___x_3042_, v___x_3043_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_a_3045_);
lean_dec_ref_known(v___x_3044_, 1);
if (lean_obj_tag(v_a_3045_) == 1)
{
lean_object* v_val_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3093_; 
v_val_3046_ = lean_ctor_get(v_a_3045_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_a_3045_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3048_ = v_a_3045_;
v_isShared_3049_ = v_isSharedCheck_3093_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_val_3046_);
lean_dec(v_a_3045_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3093_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v_fst_3050_; lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3091_; 
v_fst_3050_ = lean_ctor_get(v_val_3046_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_val_3046_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v_val_3046_, 1);
lean_dec(v_unused_3092_);
v___x_3052_ = v_val_3046_;
v_isShared_3053_ = v_isSharedCheck_3091_;
goto v_resetjp_3051_;
}
else
{
lean_inc(v_fst_3050_);
lean_dec(v_val_3046_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3091_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___y_3055_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v___x_3083_ = lean_array_get_borrowed(v___x_3017_, v_alts_3025_, v___x_3019_);
v___x_3084_ = lean_array_get_size(v_zs1_3020_);
lean_dec_ref(v_zs1_3020_);
v___x_3085_ = lean_unsigned_to_nat(0u);
v___x_3086_ = lean_nat_dec_eq(v___x_3084_, v___x_3085_);
if (v___x_3086_ == 0)
{
lean_inc(v___x_3083_);
v___y_3055_ = v___x_3083_;
goto v___jp_3054_;
}
else
{
lean_object* v___x_3087_; uint8_t v___x_3088_; 
v___x_3087_ = lean_array_get_size(v_zs2_3026_);
v___x_3088_ = lean_nat_dec_eq(v___x_3087_, v___x_3085_);
if (v___x_3088_ == 0)
{
lean_inc(v___x_3083_);
v___y_3055_ = v___x_3083_;
goto v___jp_3054_;
}
else
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3083_);
v___x_3090_ = l_Lean_Expr_app___override(v___x_3083_, v___x_3089_);
v___y_3055_ = v___x_3090_;
goto v___jp_3054_;
}
}
v___jp_3054_:
{
uint8_t v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = 0;
v___x_3057_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3057_, 0, v___x_3056_);
lean_ctor_set_uint8(v___x_3057_, 1, v___x_3022_);
lean_ctor_set_uint8(v___x_3057_, 2, v___x_3023_);
lean_ctor_set_uint8(v___x_3057_, 3, v___x_3022_);
lean_inc_ref(v___y_3055_);
lean_inc(v_fst_3050_);
v___x_3058_ = l_Lean_MVarId_apply(v_fst_3050_, v___y_3055_, v___x_3057_, v___x_3043_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
if (lean_obj_tag(v_a_3059_) == 0)
{
lean_object* v___x_3060_; 
lean_dec_ref(v___y_3055_);
lean_del_object(v___x_3052_);
lean_dec(v_fst_3050_);
lean_del_object(v___x_3048_);
v___x_3060_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3039_, v___y_3029_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; lean_object* v___x_3062_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3062_ = l_Lean_Meta_mkLambdaFVars(v___x_3034_, v_a_3061_, v___x_3023_, v___x_3022_, v___x_3023_, v___x_3022_, v___x_3024_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
lean_dec_ref(v___x_3034_);
return v___x_3062_;
}
else
{
lean_dec_ref(v___x_3034_);
return v___x_3060_;
}
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3066_; 
lean_dec(v_a_3059_);
lean_dec(v_a_3039_);
lean_dec_ref(v___x_3034_);
v___x_3063_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3064_ = l_Lean_MessageData_ofExpr(v___y_3055_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set_tag(v___x_3052_, 7);
lean_ctor_set(v___x_3052_, 1, v___x_3064_);
lean_ctor_set(v___x_3052_, 0, v___x_3063_);
v___x_3066_ = v___x_3052_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3063_);
lean_ctor_set(v_reuseFailAlloc_3074_, 1, v___x_3064_);
v___x_3066_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3066_);
lean_ctor_set(v___x_3068_, 1, v___x_3067_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v_fst_3050_);
v___x_3070_ = v___x_3048_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_fst_3050_);
v___x_3070_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3068_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3071_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
return v___x_3072_;
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref(v___y_3055_);
lean_del_object(v___x_3052_);
lean_dec(v_fst_3050_);
lean_del_object(v___x_3048_);
lean_dec(v_a_3039_);
lean_dec_ref(v___x_3034_);
v_a_3075_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_3058_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3058_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec(v_a_3045_);
lean_dec(v_a_3039_);
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_zs1_3020_);
v___x_3094_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3095_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_3094_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
return v___x_3095_;
}
}
else
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_a_3039_);
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_zs1_3020_);
v_a_3096_ = lean_ctor_get(v___x_3044_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3044_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3044_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_zs1_3020_);
return v___x_3038_;
}
}
else
{
lean_dec_ref(v___x_3034_);
lean_dec_ref(v_zs1_3020_);
return v___x_3035_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3104_, lean_object* v_a_3105_, lean_object* v___x_3106_, lean_object* v_zs1_3107_, lean_object* v_snd_3108_, lean_object* v___x_3109_, lean_object* v___x_3110_, lean_object* v___x_3111_, lean_object* v_alts_3112_, lean_object* v_zs2_3113_, lean_object* v___ctorRet2_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_){
_start:
{
uint8_t v___x_15107__boxed_3120_; uint8_t v___x_15108__boxed_3121_; uint8_t v___x_15109__boxed_3122_; lean_object* v_res_3123_; 
v___x_15107__boxed_3120_ = lean_unbox(v___x_3109_);
v___x_15108__boxed_3121_ = lean_unbox(v___x_3110_);
v___x_15109__boxed_3122_ = lean_unbox(v___x_3111_);
v_res_3123_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3104_, v_a_3105_, v___x_3106_, v_zs1_3107_, v_snd_3108_, v___x_15107__boxed_3120_, v___x_15108__boxed_3121_, v___x_15109__boxed_3122_, v_alts_3112_, v_zs2_3113_, v___ctorRet2_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec_ref(v___ctorRet2_3114_);
lean_dec_ref(v_zs2_3113_);
lean_dec_ref(v_alts_3112_);
lean_dec_ref(v_snd_3108_);
lean_dec(v___x_3106_);
lean_dec_ref(v_a_3105_);
lean_dec_ref(v___x_3104_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3124_, lean_object* v_a_3125_, lean_object* v___x_3126_, lean_object* v_snd_3127_, uint8_t v___x_3128_, uint8_t v___x_3129_, uint8_t v___x_3130_, lean_object* v_alts_3131_, lean_object* v_a_3132_, lean_object* v_zs1_3133_, lean_object* v___ctorRet1_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; 
v___x_3140_ = lean_box(v___x_3128_);
v___x_3141_ = lean_box(v___x_3129_);
v___x_3142_ = lean_box(v___x_3130_);
v___f_3143_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3143_, 0, v___x_3124_);
lean_closure_set(v___f_3143_, 1, v_a_3125_);
lean_closure_set(v___f_3143_, 2, v___x_3126_);
lean_closure_set(v___f_3143_, 3, v_zs1_3133_);
lean_closure_set(v___f_3143_, 4, v_snd_3127_);
lean_closure_set(v___f_3143_, 5, v___x_3140_);
lean_closure_set(v___f_3143_, 6, v___x_3141_);
lean_closure_set(v___f_3143_, 7, v___x_3142_);
lean_closure_set(v___f_3143_, 8, v_alts_3131_);
v___x_3144_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3132_, v___f_3143_, v___x_3129_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
return v___x_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3145_, lean_object* v_a_3146_, lean_object* v___x_3147_, lean_object* v_snd_3148_, lean_object* v___x_3149_, lean_object* v___x_3150_, lean_object* v___x_3151_, lean_object* v_alts_3152_, lean_object* v_a_3153_, lean_object* v_zs1_3154_, lean_object* v___ctorRet1_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
uint8_t v___x_15306__boxed_3161_; uint8_t v___x_15307__boxed_3162_; uint8_t v___x_15308__boxed_3163_; lean_object* v_res_3164_; 
v___x_15306__boxed_3161_ = lean_unbox(v___x_3149_);
v___x_15307__boxed_3162_ = lean_unbox(v___x_3150_);
v___x_15308__boxed_3163_ = lean_unbox(v___x_3151_);
v_res_3164_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3145_, v_a_3146_, v___x_3147_, v_snd_3148_, v___x_15306__boxed_3161_, v___x_15307__boxed_3162_, v___x_15308__boxed_3163_, v_alts_3152_, v_a_3153_, v_zs1_3154_, v___ctorRet1_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec_ref(v___ctorRet1_3155_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3165_, lean_object* v_params_3166_, lean_object* v_a_3167_, lean_object* v_snd_3168_, lean_object* v_alts_3169_, size_t v_sz_3170_, size_t v_i_3171_, lean_object* v_bs_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
uint8_t v___x_3178_; 
v___x_3178_ = lean_usize_dec_lt(v_i_3171_, v_sz_3170_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; 
lean_dec_ref(v_alts_3169_);
lean_dec_ref(v_snd_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_tail_3165_);
v___x_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3179_, 0, v_bs_3172_);
return v___x_3179_;
}
else
{
lean_object* v_v_3180_; lean_object* v___x_3181_; lean_object* v_bs_x27_3182_; lean_object* v___y_3184_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v_v_3180_ = lean_array_uget(v_bs_3172_, v_i_3171_);
v___x_3181_ = lean_unsigned_to_nat(0u);
v_bs_x27_3182_ = lean_array_uset(v_bs_3172_, v_i_3171_, v___x_3181_);
lean_inc(v_tail_3165_);
v___x_3198_ = l_Lean_mkConst(v_v_3180_, v_tail_3165_);
v___x_3199_ = l_Lean_mkAppN(v___x_3198_, v_params_3166_);
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
lean_inc(v___y_3174_);
lean_inc_ref(v___y_3173_);
v___x_3200_ = lean_infer_type(v___x_3199_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3202_; uint8_t v___x_3203_; uint8_t v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___f_3209_; lean_object* v___x_3210_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc_n(v_a_3201_, 2);
lean_dec_ref_known(v___x_3200_, 1);
v___x_3202_ = l_Lean_instInhabitedExpr;
v___x_3203_ = 0;
v___x_3204_ = 1;
v___x_3205_ = lean_usize_to_nat(v_i_3171_);
v___x_3206_ = lean_box(v___x_3178_);
v___x_3207_ = lean_box(v___x_3203_);
v___x_3208_ = lean_box(v___x_3204_);
lean_inc_ref(v_alts_3169_);
lean_inc_ref(v_snd_3168_);
lean_inc_ref(v_a_3167_);
v___f_3209_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3209_, 0, v___x_3202_);
lean_closure_set(v___f_3209_, 1, v_a_3167_);
lean_closure_set(v___f_3209_, 2, v___x_3205_);
lean_closure_set(v___f_3209_, 3, v_snd_3168_);
lean_closure_set(v___f_3209_, 4, v___x_3206_);
lean_closure_set(v___f_3209_, 5, v___x_3207_);
lean_closure_set(v___f_3209_, 6, v___x_3208_);
lean_closure_set(v___f_3209_, 7, v_alts_3169_);
lean_closure_set(v___f_3209_, 8, v_a_3201_);
v___x_3210_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3201_, v___f_3209_, v___x_3203_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
v___y_3184_ = v___x_3210_;
goto v___jp_3183_;
}
else
{
v___y_3184_ = v___x_3200_;
goto v___jp_3183_;
}
v___jp_3183_:
{
if (lean_obj_tag(v___y_3184_) == 0)
{
lean_object* v_a_3185_; size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; 
v_a_3185_ = lean_ctor_get(v___y_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref_known(v___y_3184_, 1);
v___x_3186_ = ((size_t)1ULL);
v___x_3187_ = lean_usize_add(v_i_3171_, v___x_3186_);
v___x_3188_ = lean_array_uset(v_bs_x27_3182_, v_i_3171_, v_a_3185_);
v_i_3171_ = v___x_3187_;
v_bs_3172_ = v___x_3188_;
goto _start;
}
else
{
lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec_ref(v_bs_x27_3182_);
lean_dec_ref(v_alts_3169_);
lean_dec_ref(v_snd_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_tail_3165_);
v_a_3190_ = lean_ctor_get(v___y_3184_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___y_3184_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___y_3184_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_dec(v___y_3184_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3211_, lean_object* v_params_3212_, lean_object* v_a_3213_, lean_object* v_snd_3214_, lean_object* v_alts_3215_, lean_object* v_sz_3216_, lean_object* v_i_3217_, lean_object* v_bs_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_){
_start:
{
size_t v_sz_boxed_3224_; size_t v_i_boxed_3225_; lean_object* v_res_3226_; 
v_sz_boxed_3224_ = lean_unbox_usize(v_sz_3216_);
lean_dec(v_sz_3216_);
v_i_boxed_3225_ = lean_unbox_usize(v_i_3217_);
lean_dec(v_i_3217_);
v_res_3226_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3211_, v_params_3212_, v_a_3213_, v_snd_3214_, v_alts_3215_, v_sz_boxed_3224_, v_i_boxed_3225_, v_bs_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec_ref(v_params_3212_);
return v_res_3226_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3227_ = lean_box(0);
v___x_3228_ = lean_unsigned_to_nat(16u);
v___x_3229_ = lean_mk_array(v___x_3228_, v___x_3227_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3230_, lean_object* v___x_3231_, uint8_t v___x_3232_, uint8_t v___x_3233_, uint8_t v___x_3234_, lean_object* v_ism1_x27_3235_, lean_object* v_is_3236_, lean_object* v___x_3237_, lean_object* v___x_3238_, lean_object* v___x_3239_, lean_object* v___x_3240_, lean_object* v_params_3241_, lean_object* v___x_3242_, lean_object* v___x_3243_, lean_object* v_heq_3244_, lean_object* v_val_3245_, lean_object* v_tail_3246_, lean_object* v_alts_3247_, size_t v_sz_3248_, size_t v___x_3249_, lean_object* v___x_3250_, lean_object* v___x_3251_, lean_object* v_declName_3252_, lean_object* v_levelParams_3253_, lean_object* v_numIndices_3254_, lean_object* v___x_3255_, lean_object* v___x_3256_, lean_object* v_numParams_3257_, lean_object* v_snd_3258_, lean_object* v_ism2_x27_3259_, lean_object* v_x_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___f_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3266_ = lean_box(v___x_3232_);
v___x_3267_ = lean_box(v___x_3233_);
v___x_3268_ = lean_box(v___x_3234_);
lean_inc_ref(v___x_3237_);
lean_inc_ref_n(v_is_3236_, 2);
lean_inc_ref(v_ism1_x27_3235_);
lean_inc_ref(v_motive_3230_);
v___f_3269_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3269_, 0, v_motive_3230_);
lean_closure_set(v___f_3269_, 1, v___x_3231_);
lean_closure_set(v___f_3269_, 2, v___x_3266_);
lean_closure_set(v___f_3269_, 3, v___x_3267_);
lean_closure_set(v___f_3269_, 4, v___x_3268_);
lean_closure_set(v___f_3269_, 5, v_ism1_x27_3235_);
lean_closure_set(v___f_3269_, 6, v_ism2_x27_3259_);
lean_closure_set(v___f_3269_, 7, v_is_3236_);
lean_closure_set(v___f_3269_, 8, v___x_3237_);
lean_inc_ref(v___x_3238_);
v___x_3270_ = lean_array_push(v_is_3236_, v___x_3238_);
v___x_3271_ = l_Lean_Meta_withNewEqs___redArg(v___x_3270_, v_ism1_x27_3235_, v___f_3269_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v_a_3272_; lean_object* v_fst_3273_; lean_object* v_snd_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3375_; 
v_a_3272_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_a_3272_);
lean_dec_ref_known(v___x_3271_, 1);
v_fst_3273_ = lean_ctor_get(v_a_3272_, 0);
v_snd_3274_ = lean_ctor_get(v_a_3272_, 1);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_a_3272_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3276_ = v_a_3272_;
v_isShared_3277_ = v_isSharedCheck_3375_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_snd_3274_);
lean_inc(v_fst_3273_);
lean_dec(v_a_3272_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3375_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3278_ = l_Lean_mkConst(v___x_3239_, v___x_3240_);
v___x_3279_ = l_Lean_mkAppN(v___x_3278_, v_params_3241_);
v___x_3280_ = l_Lean_Expr_app___override(v___x_3279_, v_fst_3273_);
lean_inc_ref(v_is_3236_);
v___x_3281_ = l_Array_append___redArg(v_is_3236_, v___x_3242_);
v___x_3282_ = l_Array_append___redArg(v___x_3281_, v_is_3236_);
v___x_3283_ = l_Array_append___redArg(v___x_3282_, v___x_3243_);
v___x_3284_ = l_Lean_mkAppN(v___x_3280_, v___x_3283_);
lean_dec_ref(v___x_3283_);
lean_inc_ref(v_heq_3244_);
v___x_3285_ = l_Lean_Expr_app___override(v___x_3284_, v_heq_3244_);
v___x_3286_ = l_Lean_InductiveVal_numCtors(v_val_3245_);
lean_inc_ref(v___x_3285_);
v___x_3287_ = l_Lean_Meta_inferArgumentTypesN(v___x_3286_, v___x_3285_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3289_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc(v_a_3288_);
lean_dec_ref_known(v___x_3287_, 1);
lean_inc_ref(v_alts_3247_);
lean_inc(v_snd_3274_);
v___x_3289_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3246_, v_params_3241_, v_a_3288_, v_snd_3274_, v_alts_3247_, v_sz_3248_, v___x_3249_, v___x_3250_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
lean_inc(v_a_3290_);
lean_dec_ref_known(v___x_3289_, 1);
v___x_3291_ = l_Lean_mkAppN(v___x_3285_, v_a_3290_);
lean_dec(v_a_3290_);
v___x_3292_ = l_Lean_mkAppN(v___x_3291_, v_snd_3274_);
lean_dec(v_snd_3274_);
lean_inc_ref(v___x_3251_);
v___x_3293_ = lean_array_push(v___x_3251_, v_motive_3230_);
v___x_3294_ = l_Array_append___redArg(v_params_3241_, v___x_3293_);
lean_dec_ref(v___x_3293_);
v___x_3295_ = l_Array_append___redArg(v___x_3294_, v_is_3236_);
lean_dec_ref(v_is_3236_);
v___x_3296_ = lean_unsigned_to_nat(2u);
v___x_3297_ = lean_mk_empty_array_with_capacity(v___x_3296_);
v___x_3298_ = lean_array_push(v___x_3297_, v___x_3238_);
v___x_3299_ = lean_array_push(v___x_3298_, v___x_3237_);
v___x_3300_ = l_Array_append___redArg(v___x_3295_, v___x_3299_);
lean_dec_ref(v___x_3299_);
v___x_3301_ = lean_array_push(v___x_3251_, v_heq_3244_);
v___x_3302_ = l_Array_append___redArg(v___x_3300_, v___x_3301_);
lean_dec_ref(v___x_3301_);
v___x_3303_ = l_Array_append___redArg(v___x_3302_, v_alts_3247_);
lean_dec_ref(v_alts_3247_);
v___x_3304_ = l_Lean_Meta_mkLambdaFVars(v___x_3303_, v___x_3292_, v___x_3232_, v___x_3233_, v___x_3232_, v___x_3233_, v___x_3234_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
lean_dec_ref(v___x_3303_);
if (lean_obj_tag(v___x_3304_) == 0)
{
lean_object* v_a_3305_; lean_object* v___x_3306_; 
v_a_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc_n(v_a_3305_, 2);
lean_dec_ref_known(v___x_3304_, 1);
lean_inc(v___y_3264_);
lean_inc_ref(v___y_3263_);
lean_inc(v___y_3262_);
lean_inc_ref(v___y_3261_);
v___x_3306_ = lean_infer_type(v_a_3305_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_object* v_a_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3342_; 
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
lean_inc(v_a_3307_);
lean_dec_ref_known(v___x_3306_, 1);
v___x_3308_ = lean_box(1);
lean_inc(v_declName_3252_);
v___x_3309_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3252_, v_levelParams_3253_, v_a_3307_, v_a_3305_, v___x_3308_, v___y_3264_);
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3342_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3342_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
lean_object* v___x_3315_; 
if (v_isShared_3313_ == 0)
{
lean_ctor_set_tag(v___x_3312_, 1);
v___x_3315_ = v___x_3312_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3310_);
v___x_3315_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3316_; lean_object* v___f_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3316_ = lean_box(v___x_3232_);
lean_inc_ref(v___x_3315_);
v___f_3317_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3317_, 0, v___x_3315_);
lean_closure_set(v___f_3317_, 1, v___x_3316_);
v___x_3318_ = lean_nat_add(v_numIndices_3254_, v___x_3255_);
lean_inc(v___x_3256_);
v___x_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3256_);
v___x_3320_ = lean_box(0);
v___x_3321_ = lean_mk_empty_array_with_capacity(v___x_3255_);
v___x_3322_ = lean_array_push(v___x_3321_, v___x_3320_);
v___x_3323_ = lean_array_push(v___x_3322_, v___x_3320_);
v___x_3324_ = lean_array_push(v___x_3323_, v___x_3320_);
v___x_3325_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 1, v___x_3325_);
lean_ctor_set(v___x_3276_, 0, v___x_3256_);
v___x_3327_ = v___x_3276_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3328_; uint8_t v___y_3330_; uint8_t v___x_3339_; 
v___x_3328_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3328_, 0, v_numParams_3257_);
lean_ctor_set(v___x_3328_, 1, v___x_3318_);
lean_ctor_set(v___x_3328_, 2, v_snd_3258_);
lean_ctor_set(v___x_3328_, 3, v___x_3319_);
lean_ctor_set(v___x_3328_, 4, v___x_3324_);
lean_ctor_set(v___x_3328_, 5, v___x_3327_);
v___x_3339_ = l_Lean_isPrivateName(v_declName_3252_);
if (v___x_3339_ == 0)
{
v___y_3330_ = v___x_3233_;
goto v___jp_3329_;
}
else
{
v___y_3330_ = v___x_3232_;
goto v___jp_3329_;
}
v___jp_3329_:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3317_, v___y_3330_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
lean_dec_ref_known(v___x_3331_, 1);
v___x_3332_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3252_);
v___x_3333_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(v___x_3332_, v_declName_3252_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v___x_3334_; uint8_t v___x_3335_; lean_object* v___x_3336_; 
lean_dec_ref_known(v___x_3333_, 1);
lean_inc_n(v_declName_3252_, 2);
v___x_3334_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3252_, v___x_3328_, v___y_3262_, v___y_3264_);
lean_dec_ref(v___x_3334_);
v___x_3335_ = 0;
v___x_3336_ = l_Lean_Meta_setInlineAttribute(v_declName_3252_, v___x_3335_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v___x_3337_; 
lean_dec_ref_known(v___x_3336_, 1);
v___x_3337_ = l_Lean_enableRealizationsForConst(v_declName_3252_, v___y_3263_, v___y_3264_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v___x_3338_; 
lean_dec_ref_known(v___x_3337_, 1);
v___x_3338_ = l_Lean_compileDecl(v___x_3315_, v___x_3233_, v___y_3263_, v___y_3264_);
return v___x_3338_;
}
else
{
lean_dec_ref(v___x_3315_);
return v___x_3337_;
}
}
else
{
lean_dec_ref(v___x_3315_);
lean_dec(v_declName_3252_);
return v___x_3336_;
}
}
else
{
lean_dec_ref_known(v___x_3328_, 6);
lean_dec_ref(v___x_3315_);
lean_dec(v_declName_3252_);
return v___x_3333_;
}
}
else
{
lean_dec_ref_known(v___x_3328_, 6);
lean_dec_ref(v___x_3315_);
lean_dec(v_declName_3252_);
return v___x_3331_;
}
}
}
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec(v_a_3305_);
lean_del_object(v___x_3276_);
lean_dec_ref(v_snd_3258_);
lean_dec(v_numParams_3257_);
lean_dec(v___x_3256_);
lean_dec(v_levelParams_3253_);
lean_dec(v_declName_3252_);
v_a_3343_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3306_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3306_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_del_object(v___x_3276_);
lean_dec_ref(v_snd_3258_);
lean_dec(v_numParams_3257_);
lean_dec(v___x_3256_);
lean_dec(v_levelParams_3253_);
lean_dec(v_declName_3252_);
v_a_3351_ = lean_ctor_get(v___x_3304_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3304_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3304_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3304_);
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
lean_dec_ref(v___x_3285_);
lean_del_object(v___x_3276_);
lean_dec(v_snd_3274_);
lean_dec_ref(v_snd_3258_);
lean_dec(v_numParams_3257_);
lean_dec(v___x_3256_);
lean_dec(v_levelParams_3253_);
lean_dec(v_declName_3252_);
lean_dec_ref(v___x_3251_);
lean_dec_ref(v_alts_3247_);
lean_dec_ref(v_heq_3244_);
lean_dec_ref(v_params_3241_);
lean_dec_ref(v___x_3238_);
lean_dec_ref(v___x_3237_);
lean_dec_ref(v_is_3236_);
lean_dec_ref(v_motive_3230_);
v_a_3359_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3289_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3289_);
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
lean_dec_ref(v___x_3285_);
lean_del_object(v___x_3276_);
lean_dec(v_snd_3274_);
lean_dec_ref(v_snd_3258_);
lean_dec(v_numParams_3257_);
lean_dec(v___x_3256_);
lean_dec(v_levelParams_3253_);
lean_dec(v_declName_3252_);
lean_dec_ref(v___x_3251_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v_alts_3247_);
lean_dec(v_tail_3246_);
lean_dec_ref(v_heq_3244_);
lean_dec_ref(v_params_3241_);
lean_dec_ref(v___x_3238_);
lean_dec_ref(v___x_3237_);
lean_dec_ref(v_is_3236_);
lean_dec_ref(v_motive_3230_);
v_a_3367_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3369_ = v___x_3287_;
v_isShared_3370_ = v_isSharedCheck_3374_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_a_3367_);
lean_dec(v___x_3287_);
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
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec_ref(v_snd_3258_);
lean_dec(v_numParams_3257_);
lean_dec(v___x_3256_);
lean_dec(v_levelParams_3253_);
lean_dec(v_declName_3252_);
lean_dec_ref(v___x_3251_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v_alts_3247_);
lean_dec(v_tail_3246_);
lean_dec_ref(v_heq_3244_);
lean_dec_ref(v_params_3241_);
lean_dec(v___x_3240_);
lean_dec(v___x_3239_);
lean_dec_ref(v___x_3238_);
lean_dec_ref(v___x_3237_);
lean_dec_ref(v_is_3236_);
lean_dec_ref(v_motive_3230_);
v_a_3376_ = lean_ctor_get(v___x_3271_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3271_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3271_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3271_);
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
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3384_ = _args[0];
lean_object* v___x_3385_ = _args[1];
lean_object* v___x_3386_ = _args[2];
lean_object* v___x_3387_ = _args[3];
lean_object* v___x_3388_ = _args[4];
lean_object* v_ism1_x27_3389_ = _args[5];
lean_object* v_is_3390_ = _args[6];
lean_object* v___x_3391_ = _args[7];
lean_object* v___x_3392_ = _args[8];
lean_object* v___x_3393_ = _args[9];
lean_object* v___x_3394_ = _args[10];
lean_object* v_params_3395_ = _args[11];
lean_object* v___x_3396_ = _args[12];
lean_object* v___x_3397_ = _args[13];
lean_object* v_heq_3398_ = _args[14];
lean_object* v_val_3399_ = _args[15];
lean_object* v_tail_3400_ = _args[16];
lean_object* v_alts_3401_ = _args[17];
lean_object* v_sz_3402_ = _args[18];
lean_object* v___x_3403_ = _args[19];
lean_object* v___x_3404_ = _args[20];
lean_object* v___x_3405_ = _args[21];
lean_object* v_declName_3406_ = _args[22];
lean_object* v_levelParams_3407_ = _args[23];
lean_object* v_numIndices_3408_ = _args[24];
lean_object* v___x_3409_ = _args[25];
lean_object* v___x_3410_ = _args[26];
lean_object* v_numParams_3411_ = _args[27];
lean_object* v_snd_3412_ = _args[28];
lean_object* v_ism2_x27_3413_ = _args[29];
lean_object* v_x_3414_ = _args[30];
lean_object* v___y_3415_ = _args[31];
lean_object* v___y_3416_ = _args[32];
lean_object* v___y_3417_ = _args[33];
lean_object* v___y_3418_ = _args[34];
lean_object* v___y_3419_ = _args[35];
_start:
{
uint8_t v___x_15445__boxed_3420_; uint8_t v___x_15446__boxed_3421_; uint8_t v___x_15447__boxed_3422_; size_t v_sz_boxed_3423_; size_t v___x_15456__boxed_3424_; lean_object* v_res_3425_; 
v___x_15445__boxed_3420_ = lean_unbox(v___x_3386_);
v___x_15446__boxed_3421_ = lean_unbox(v___x_3387_);
v___x_15447__boxed_3422_ = lean_unbox(v___x_3388_);
v_sz_boxed_3423_ = lean_unbox_usize(v_sz_3402_);
lean_dec(v_sz_3402_);
v___x_15456__boxed_3424_ = lean_unbox_usize(v___x_3403_);
lean_dec(v___x_3403_);
v_res_3425_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3384_, v___x_3385_, v___x_15445__boxed_3420_, v___x_15446__boxed_3421_, v___x_15447__boxed_3422_, v_ism1_x27_3389_, v_is_3390_, v___x_3391_, v___x_3392_, v___x_3393_, v___x_3394_, v_params_3395_, v___x_3396_, v___x_3397_, v_heq_3398_, v_val_3399_, v_tail_3400_, v_alts_3401_, v_sz_boxed_3423_, v___x_15456__boxed_3424_, v___x_3404_, v___x_3405_, v_declName_3406_, v_levelParams_3407_, v_numIndices_3408_, v___x_3409_, v___x_3410_, v_numParams_3411_, v_snd_3412_, v_ism2_x27_3413_, v_x_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec_ref(v_x_3414_);
lean_dec(v___x_3409_);
lean_dec(v_numIndices_3408_);
lean_dec_ref(v_val_3399_);
lean_dec_ref(v___x_3397_);
lean_dec_ref(v___x_3396_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3426_, lean_object* v___x_3427_, uint8_t v___x_3428_, uint8_t v___x_3429_, uint8_t v___x_3430_, lean_object* v_is_3431_, lean_object* v___x_3432_, lean_object* v___x_3433_, lean_object* v___x_3434_, lean_object* v___x_3435_, lean_object* v_params_3436_, lean_object* v___x_3437_, lean_object* v___x_3438_, lean_object* v_heq_3439_, lean_object* v_val_3440_, lean_object* v_tail_3441_, lean_object* v_alts_3442_, size_t v_sz_3443_, size_t v___x_3444_, lean_object* v___x_3445_, lean_object* v___x_3446_, lean_object* v_declName_3447_, lean_object* v_levelParams_3448_, lean_object* v_numIndices_3449_, lean_object* v___x_3450_, lean_object* v___x_3451_, lean_object* v_numParams_3452_, lean_object* v_snd_3453_, lean_object* v___x_3454_, lean_object* v___x_3455_, lean_object* v_ism1_x27_3456_, lean_object* v_x_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___f_3468_; lean_object* v___x_3469_; 
v___x_3463_ = lean_box(v___x_3428_);
v___x_3464_ = lean_box(v___x_3429_);
v___x_3465_ = lean_box(v___x_3430_);
v___x_3466_ = lean_box_usize(v_sz_3443_);
v___x_3467_ = lean_box_usize(v___x_3444_);
v___f_3468_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3468_, 0, v_motive_3426_);
lean_closure_set(v___f_3468_, 1, v___x_3427_);
lean_closure_set(v___f_3468_, 2, v___x_3463_);
lean_closure_set(v___f_3468_, 3, v___x_3464_);
lean_closure_set(v___f_3468_, 4, v___x_3465_);
lean_closure_set(v___f_3468_, 5, v_ism1_x27_3456_);
lean_closure_set(v___f_3468_, 6, v_is_3431_);
lean_closure_set(v___f_3468_, 7, v___x_3432_);
lean_closure_set(v___f_3468_, 8, v___x_3433_);
lean_closure_set(v___f_3468_, 9, v___x_3434_);
lean_closure_set(v___f_3468_, 10, v___x_3435_);
lean_closure_set(v___f_3468_, 11, v_params_3436_);
lean_closure_set(v___f_3468_, 12, v___x_3437_);
lean_closure_set(v___f_3468_, 13, v___x_3438_);
lean_closure_set(v___f_3468_, 14, v_heq_3439_);
lean_closure_set(v___f_3468_, 15, v_val_3440_);
lean_closure_set(v___f_3468_, 16, v_tail_3441_);
lean_closure_set(v___f_3468_, 17, v_alts_3442_);
lean_closure_set(v___f_3468_, 18, v___x_3466_);
lean_closure_set(v___f_3468_, 19, v___x_3467_);
lean_closure_set(v___f_3468_, 20, v___x_3445_);
lean_closure_set(v___f_3468_, 21, v___x_3446_);
lean_closure_set(v___f_3468_, 22, v_declName_3447_);
lean_closure_set(v___f_3468_, 23, v_levelParams_3448_);
lean_closure_set(v___f_3468_, 24, v_numIndices_3449_);
lean_closure_set(v___f_3468_, 25, v___x_3450_);
lean_closure_set(v___f_3468_, 26, v___x_3451_);
lean_closure_set(v___f_3468_, 27, v_numParams_3452_);
lean_closure_set(v___f_3468_, 28, v_snd_3453_);
v___x_3469_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3454_, v___x_3455_, v___f_3468_, v___x_3428_, v___x_3428_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3470_ = _args[0];
lean_object* v___x_3471_ = _args[1];
lean_object* v___x_3472_ = _args[2];
lean_object* v___x_3473_ = _args[3];
lean_object* v___x_3474_ = _args[4];
lean_object* v_is_3475_ = _args[5];
lean_object* v___x_3476_ = _args[6];
lean_object* v___x_3477_ = _args[7];
lean_object* v___x_3478_ = _args[8];
lean_object* v___x_3479_ = _args[9];
lean_object* v_params_3480_ = _args[10];
lean_object* v___x_3481_ = _args[11];
lean_object* v___x_3482_ = _args[12];
lean_object* v_heq_3483_ = _args[13];
lean_object* v_val_3484_ = _args[14];
lean_object* v_tail_3485_ = _args[15];
lean_object* v_alts_3486_ = _args[16];
lean_object* v_sz_3487_ = _args[17];
lean_object* v___x_3488_ = _args[18];
lean_object* v___x_3489_ = _args[19];
lean_object* v___x_3490_ = _args[20];
lean_object* v_declName_3491_ = _args[21];
lean_object* v_levelParams_3492_ = _args[22];
lean_object* v_numIndices_3493_ = _args[23];
lean_object* v___x_3494_ = _args[24];
lean_object* v___x_3495_ = _args[25];
lean_object* v_numParams_3496_ = _args[26];
lean_object* v_snd_3497_ = _args[27];
lean_object* v___x_3498_ = _args[28];
lean_object* v___x_3499_ = _args[29];
lean_object* v_ism1_x27_3500_ = _args[30];
lean_object* v_x_3501_ = _args[31];
lean_object* v___y_3502_ = _args[32];
lean_object* v___y_3503_ = _args[33];
lean_object* v___y_3504_ = _args[34];
lean_object* v___y_3505_ = _args[35];
lean_object* v___y_3506_ = _args[36];
_start:
{
uint8_t v___x_15767__boxed_3507_; uint8_t v___x_15768__boxed_3508_; uint8_t v___x_15769__boxed_3509_; size_t v_sz_boxed_3510_; size_t v___x_15778__boxed_3511_; lean_object* v_res_3512_; 
v___x_15767__boxed_3507_ = lean_unbox(v___x_3472_);
v___x_15768__boxed_3508_ = lean_unbox(v___x_3473_);
v___x_15769__boxed_3509_ = lean_unbox(v___x_3474_);
v_sz_boxed_3510_ = lean_unbox_usize(v_sz_3487_);
lean_dec(v_sz_3487_);
v___x_15778__boxed_3511_ = lean_unbox_usize(v___x_3488_);
lean_dec(v___x_3488_);
v_res_3512_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3470_, v___x_3471_, v___x_15767__boxed_3507_, v___x_15768__boxed_3508_, v___x_15769__boxed_3509_, v_is_3475_, v___x_3476_, v___x_3477_, v___x_3478_, v___x_3479_, v_params_3480_, v___x_3481_, v___x_3482_, v_heq_3483_, v_val_3484_, v_tail_3485_, v_alts_3486_, v_sz_boxed_3510_, v___x_15778__boxed_3511_, v___x_3489_, v___x_3490_, v_declName_3491_, v_levelParams_3492_, v_numIndices_3493_, v___x_3494_, v___x_3495_, v_numParams_3496_, v_snd_3497_, v___x_3498_, v___x_3499_, v_ism1_x27_3500_, v_x_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec_ref(v_x_3501_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3513_, lean_object* v___x_3514_, lean_object* v_motive_3515_, lean_object* v___x_3516_, uint8_t v___x_3517_, uint8_t v___x_3518_, uint8_t v___x_3519_, lean_object* v_is_3520_, lean_object* v___x_3521_, lean_object* v___x_3522_, lean_object* v___x_3523_, lean_object* v___x_3524_, lean_object* v_params_3525_, lean_object* v___x_3526_, lean_object* v___x_3527_, lean_object* v_heq_3528_, lean_object* v_val_3529_, lean_object* v_tail_3530_, size_t v_sz_3531_, size_t v___x_3532_, lean_object* v___x_3533_, lean_object* v___x_3534_, lean_object* v_declName_3535_, lean_object* v_levelParams_3536_, lean_object* v___x_3537_, lean_object* v___x_3538_, lean_object* v_numParams_3539_, lean_object* v_snd_3540_, lean_object* v___x_3541_, lean_object* v_alts_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___f_3555_; lean_object* v___x_3556_; 
v___x_3548_ = lean_nat_add(v_numIndices_3513_, v___x_3514_);
v___x_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
v___x_3550_ = lean_box(v___x_3517_);
v___x_3551_ = lean_box(v___x_3518_);
v___x_3552_ = lean_box(v___x_3519_);
v___x_3553_ = lean_box_usize(v_sz_3531_);
v___x_3554_ = lean_box_usize(v___x_3532_);
lean_inc_ref(v___x_3549_);
lean_inc_ref(v___x_3541_);
v___f_3555_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3555_, 0, v_motive_3515_);
lean_closure_set(v___f_3555_, 1, v___x_3516_);
lean_closure_set(v___f_3555_, 2, v___x_3550_);
lean_closure_set(v___f_3555_, 3, v___x_3551_);
lean_closure_set(v___f_3555_, 4, v___x_3552_);
lean_closure_set(v___f_3555_, 5, v_is_3520_);
lean_closure_set(v___f_3555_, 6, v___x_3521_);
lean_closure_set(v___f_3555_, 7, v___x_3522_);
lean_closure_set(v___f_3555_, 8, v___x_3523_);
lean_closure_set(v___f_3555_, 9, v___x_3524_);
lean_closure_set(v___f_3555_, 10, v_params_3525_);
lean_closure_set(v___f_3555_, 11, v___x_3526_);
lean_closure_set(v___f_3555_, 12, v___x_3527_);
lean_closure_set(v___f_3555_, 13, v_heq_3528_);
lean_closure_set(v___f_3555_, 14, v_val_3529_);
lean_closure_set(v___f_3555_, 15, v_tail_3530_);
lean_closure_set(v___f_3555_, 16, v_alts_3542_);
lean_closure_set(v___f_3555_, 17, v___x_3553_);
lean_closure_set(v___f_3555_, 18, v___x_3554_);
lean_closure_set(v___f_3555_, 19, v___x_3533_);
lean_closure_set(v___f_3555_, 20, v___x_3534_);
lean_closure_set(v___f_3555_, 21, v_declName_3535_);
lean_closure_set(v___f_3555_, 22, v_levelParams_3536_);
lean_closure_set(v___f_3555_, 23, v_numIndices_3513_);
lean_closure_set(v___f_3555_, 24, v___x_3537_);
lean_closure_set(v___f_3555_, 25, v___x_3538_);
lean_closure_set(v___f_3555_, 26, v_numParams_3539_);
lean_closure_set(v___f_3555_, 27, v_snd_3540_);
lean_closure_set(v___f_3555_, 28, v___x_3541_);
lean_closure_set(v___f_3555_, 29, v___x_3549_);
v___x_3556_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3541_, v___x_3549_, v___f_3555_, v___x_3517_, v___x_3517_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3557_ = _args[0];
lean_object* v___x_3558_ = _args[1];
lean_object* v_motive_3559_ = _args[2];
lean_object* v___x_3560_ = _args[3];
lean_object* v___x_3561_ = _args[4];
lean_object* v___x_3562_ = _args[5];
lean_object* v___x_3563_ = _args[6];
lean_object* v_is_3564_ = _args[7];
lean_object* v___x_3565_ = _args[8];
lean_object* v___x_3566_ = _args[9];
lean_object* v___x_3567_ = _args[10];
lean_object* v___x_3568_ = _args[11];
lean_object* v_params_3569_ = _args[12];
lean_object* v___x_3570_ = _args[13];
lean_object* v___x_3571_ = _args[14];
lean_object* v_heq_3572_ = _args[15];
lean_object* v_val_3573_ = _args[16];
lean_object* v_tail_3574_ = _args[17];
lean_object* v_sz_3575_ = _args[18];
lean_object* v___x_3576_ = _args[19];
lean_object* v___x_3577_ = _args[20];
lean_object* v___x_3578_ = _args[21];
lean_object* v_declName_3579_ = _args[22];
lean_object* v_levelParams_3580_ = _args[23];
lean_object* v___x_3581_ = _args[24];
lean_object* v___x_3582_ = _args[25];
lean_object* v_numParams_3583_ = _args[26];
lean_object* v_snd_3584_ = _args[27];
lean_object* v___x_3585_ = _args[28];
lean_object* v_alts_3586_ = _args[29];
lean_object* v___y_3587_ = _args[30];
lean_object* v___y_3588_ = _args[31];
lean_object* v___y_3589_ = _args[32];
lean_object* v___y_3590_ = _args[33];
lean_object* v___y_3591_ = _args[34];
_start:
{
uint8_t v___x_15860__boxed_3592_; uint8_t v___x_15861__boxed_3593_; uint8_t v___x_15862__boxed_3594_; size_t v_sz_boxed_3595_; size_t v___x_15871__boxed_3596_; lean_object* v_res_3597_; 
v___x_15860__boxed_3592_ = lean_unbox(v___x_3561_);
v___x_15861__boxed_3593_ = lean_unbox(v___x_3562_);
v___x_15862__boxed_3594_ = lean_unbox(v___x_3563_);
v_sz_boxed_3595_ = lean_unbox_usize(v_sz_3575_);
lean_dec(v_sz_3575_);
v___x_15871__boxed_3596_ = lean_unbox_usize(v___x_3576_);
lean_dec(v___x_3576_);
v_res_3597_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3557_, v___x_3558_, v_motive_3559_, v___x_3560_, v___x_15860__boxed_3592_, v___x_15861__boxed_3593_, v___x_15862__boxed_3594_, v_is_3564_, v___x_3565_, v___x_3566_, v___x_3567_, v___x_3568_, v_params_3569_, v___x_3570_, v___x_3571_, v_heq_3572_, v_val_3573_, v_tail_3574_, v_sz_boxed_3595_, v___x_15871__boxed_3596_, v___x_3577_, v___x_3578_, v_declName_3579_, v_levelParams_3580_, v___x_3581_, v___x_3582_, v_numParams_3583_, v_snd_3584_, v___x_3585_, v_alts_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___x_3558_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3598_, lean_object* v_declInfos_3599_, lean_object* v_k_3600_, lean_object* v_kind_3601_, lean_object* v_x_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_){
_start:
{
uint8_t v_kind_boxed_3608_; lean_object* v_res_3609_; 
v_kind_boxed_3608_ = lean_unbox(v_kind_3601_);
v_res_3609_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3598_, v_declInfos_3599_, v_k_3600_, v_kind_boxed_3608_, v_x_3602_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
lean_dec(v___y_3606_);
lean_dec_ref(v___y_3605_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3610_, lean_object* v_k_3611_, uint8_t v_kind_3612_, lean_object* v_acc_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; lean_object* v_toApplicative_3620_; lean_object* v_toFunctor_3621_; lean_object* v_toSeq_3622_; lean_object* v_toSeqLeft_3623_; lean_object* v_toSeqRight_3624_; lean_object* v___f_3625_; lean_object* v___f_3626_; lean_object* v___f_3627_; lean_object* v___f_3628_; lean_object* v___x_3629_; lean_object* v___f_3630_; lean_object* v___f_3631_; lean_object* v___f_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v_toApplicative_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3694_; 
v___x_3619_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
v_toApplicative_3620_ = lean_ctor_get(v___x_3619_, 0);
v_toFunctor_3621_ = lean_ctor_get(v_toApplicative_3620_, 0);
v_toSeq_3622_ = lean_ctor_get(v_toApplicative_3620_, 2);
v_toSeqLeft_3623_ = lean_ctor_get(v_toApplicative_3620_, 3);
v_toSeqRight_3624_ = lean_ctor_get(v_toApplicative_3620_, 4);
v___f_3625_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2));
v___f_3626_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3));
lean_inc_ref_n(v_toFunctor_3621_, 2);
v___f_3627_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3627_, 0, v_toFunctor_3621_);
v___f_3628_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3628_, 0, v_toFunctor_3621_);
v___x_3629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___f_3627_);
lean_ctor_set(v___x_3629_, 1, v___f_3628_);
lean_inc(v_toSeqRight_3624_);
v___f_3630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3630_, 0, v_toSeqRight_3624_);
lean_inc(v_toSeqLeft_3623_);
v___f_3631_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3631_, 0, v_toSeqLeft_3623_);
lean_inc(v_toSeq_3622_);
v___f_3632_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3632_, 0, v_toSeq_3622_);
v___x_3633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3629_);
lean_ctor_set(v___x_3633_, 1, v___f_3625_);
lean_ctor_set(v___x_3633_, 2, v___f_3632_);
lean_ctor_set(v___x_3633_, 3, v___f_3631_);
lean_ctor_set(v___x_3633_, 4, v___f_3630_);
v___x_3634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
lean_ctor_set(v___x_3634_, 1, v___f_3626_);
v___x_3635_ = l_StateRefT_x27_instMonad___redArg(v___x_3634_);
v_toApplicative_3636_ = lean_ctor_get(v___x_3635_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3635_);
if (v_isSharedCheck_3694_ == 0)
{
lean_object* v_unused_3695_; 
v_unused_3695_ = lean_ctor_get(v___x_3635_, 1);
lean_dec(v_unused_3695_);
v___x_3638_ = v___x_3635_;
v_isShared_3639_ = v_isSharedCheck_3694_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_toApplicative_3636_);
lean_dec(v___x_3635_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3694_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v_toFunctor_3640_; lean_object* v_toSeq_3641_; lean_object* v_toSeqLeft_3642_; lean_object* v_toSeqRight_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3692_; 
v_toFunctor_3640_ = lean_ctor_get(v_toApplicative_3636_, 0);
v_toSeq_3641_ = lean_ctor_get(v_toApplicative_3636_, 2);
v_toSeqLeft_3642_ = lean_ctor_get(v_toApplicative_3636_, 3);
v_toSeqRight_3643_ = lean_ctor_get(v_toApplicative_3636_, 4);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_toApplicative_3636_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; 
v_unused_3693_ = lean_ctor_get(v_toApplicative_3636_, 1);
lean_dec(v_unused_3693_);
v___x_3645_ = v_toApplicative_3636_;
v_isShared_3646_ = v_isSharedCheck_3692_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_toSeqRight_3643_);
lean_inc(v_toSeqLeft_3642_);
lean_inc(v_toSeq_3641_);
lean_inc(v_toFunctor_3640_);
lean_dec(v_toApplicative_3636_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3692_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___f_3647_; lean_object* v___f_3648_; lean_object* v___f_3649_; lean_object* v___f_3650_; lean_object* v___x_3651_; lean_object* v___f_3652_; lean_object* v___f_3653_; lean_object* v___f_3654_; lean_object* v___x_3656_; 
v___f_3647_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4));
v___f_3648_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5));
lean_inc_ref(v_toFunctor_3640_);
v___f_3649_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3649_, 0, v_toFunctor_3640_);
v___f_3650_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3650_, 0, v_toFunctor_3640_);
v___x_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___f_3649_);
lean_ctor_set(v___x_3651_, 1, v___f_3650_);
v___f_3652_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3652_, 0, v_toSeqRight_3643_);
v___f_3653_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3653_, 0, v_toSeqLeft_3642_);
v___f_3654_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3654_, 0, v_toSeq_3641_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 4, v___f_3652_);
lean_ctor_set(v___x_3645_, 3, v___f_3653_);
lean_ctor_set(v___x_3645_, 2, v___f_3654_);
lean_ctor_set(v___x_3645_, 1, v___f_3647_);
lean_ctor_set(v___x_3645_, 0, v___x_3651_);
v___x_3656_ = v___x_3645_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3651_);
lean_ctor_set(v_reuseFailAlloc_3691_, 1, v___f_3647_);
lean_ctor_set(v_reuseFailAlloc_3691_, 2, v___f_3654_);
lean_ctor_set(v_reuseFailAlloc_3691_, 3, v___f_3653_);
lean_ctor_set(v_reuseFailAlloc_3691_, 4, v___f_3652_);
v___x_3656_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 1, v___f_3648_);
lean_ctor_set(v___x_3638_, 0, v___x_3656_);
v___x_3658_ = v___x_3638_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3690_, 1, v___f_3648_);
v___x_3658_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v___x_3659_ = lean_array_get_size(v_acc_3613_);
v___x_3660_ = lean_array_get_size(v_declInfos_3610_);
v___x_3661_ = lean_nat_dec_lt(v___x_3659_, v___x_3660_);
if (v___x_3661_ == 0)
{
lean_object* v___x_3662_; 
lean_dec_ref(v___x_3658_);
lean_dec_ref(v_declInfos_3610_);
lean_inc(v___y_3617_);
lean_inc_ref(v___y_3616_);
lean_inc(v___y_3615_);
lean_inc_ref(v___y_3614_);
v___x_3662_ = lean_apply_6(v_k_3611_, v_acc_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, lean_box(0));
return v___x_3662_;
}
else
{
lean_object* v___x_3663_; uint8_t v___x_3664_; lean_object* v___x_3665_; lean_object* v___f_3666_; lean_object* v___f_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v_snd_3672_; lean_object* v_fst_3673_; lean_object* v_fst_3674_; lean_object* v_snd_3675_; lean_object* v___x_3676_; 
v___x_3663_ = lean_box(0);
v___x_3664_ = 0;
v___x_3665_ = l_Lean_instInhabitedExpr;
v___f_3666_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3666_, 0, v___x_3658_);
lean_closure_set(v___f_3666_, 1, v___x_3665_);
v___f_3667_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3667_, 0, v___f_3666_);
v___x_3668_ = lean_box(v___x_3664_);
v___x_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
lean_ctor_set(v___x_3669_, 1, v___f_3667_);
v___x_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3663_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = lean_array_get(v___x_3670_, v_declInfos_3610_, v___x_3659_);
lean_dec_ref_known(v___x_3670_, 2);
v_snd_3672_ = lean_ctor_get(v___x_3671_, 1);
lean_inc(v_snd_3672_);
v_fst_3673_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_fst_3673_);
lean_dec(v___x_3671_);
v_fst_3674_ = lean_ctor_get(v_snd_3672_, 0);
lean_inc(v_fst_3674_);
v_snd_3675_ = lean_ctor_get(v_snd_3672_, 1);
lean_inc(v_snd_3675_);
lean_dec(v_snd_3672_);
lean_inc(v___y_3617_);
lean_inc_ref(v___y_3616_);
lean_inc(v___y_3615_);
lean_inc_ref(v___y_3614_);
lean_inc_ref(v_acc_3613_);
v___x_3676_ = lean_apply_6(v_snd_3675_, v_acc_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_, lean_box(0));
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3678_; lean_object* v___f_3679_; uint8_t v___x_3680_; lean_object* v___x_3681_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref_known(v___x_3676_, 1);
v___x_3678_ = lean_box(v_kind_3612_);
v___f_3679_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3679_, 0, v_acc_3613_);
lean_closure_set(v___f_3679_, 1, v_declInfos_3610_);
lean_closure_set(v___f_3679_, 2, v_k_3611_);
lean_closure_set(v___f_3679_, 3, v___x_3678_);
v___x_3680_ = lean_unbox(v_fst_3674_);
lean_dec(v_fst_3674_);
v___x_3681_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3673_, v___x_3680_, v_a_3677_, v___f_3679_, v_kind_3612_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
return v___x_3681_;
}
else
{
lean_object* v_a_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3689_; 
lean_dec(v_fst_3674_);
lean_dec(v_fst_3673_);
lean_dec_ref(v_acc_3613_);
lean_dec_ref(v_k_3611_);
lean_dec_ref(v_declInfos_3610_);
v_a_3682_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3689_ == 0)
{
v___x_3684_ = v___x_3676_;
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_a_3682_);
lean_dec(v___x_3676_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3689_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3687_; 
if (v_isShared_3685_ == 0)
{
v___x_3687_ = v___x_3684_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_a_3682_);
v___x_3687_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3686_;
}
v_reusejp_3686_:
{
return v___x_3687_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3696_, lean_object* v_declInfos_3697_, lean_object* v_k_3698_, uint8_t v_kind_3699_, lean_object* v_x_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = lean_array_push(v_acc_3696_, v_x_3700_);
v___x_3707_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3697_, v_k_3698_, v_kind_3699_, v___x_3706_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3708_, lean_object* v_k_3709_, lean_object* v_kind_3710_, lean_object* v_acc_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
uint8_t v_kind_boxed_3717_; lean_object* v_res_3718_; 
v_kind_boxed_3717_ = lean_unbox(v_kind_3710_);
v_res_3718_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3708_, v_k_3709_, v_kind_boxed_3717_, v_acc_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3719_, lean_object* v_k_3720_, uint8_t v_kind_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0));
v___x_3728_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3719_, v_k_3720_, v_kind_3721_, v___x_3727_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3729_, lean_object* v_k_3730_, lean_object* v_kind_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
uint8_t v_kind_boxed_3737_; lean_object* v_res_3738_; 
v_kind_boxed_3737_ = lean_unbox(v_kind_3731_);
v_res_3738_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3729_, v_k_3730_, v_kind_boxed_3737_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_);
lean_dec(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec(v___y_3733_);
lean_dec_ref(v___y_3732_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3739_, lean_object* v_k_3740_, uint8_t v_kind_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
size_t v_sz_3747_; size_t v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v_sz_3747_ = lean_array_size(v_declInfos_3739_);
v___x_3748_ = ((size_t)0ULL);
v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_3747_, v___x_3748_, v_declInfos_3739_);
v___x_3750_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3749_, v_k_3740_, v_kind_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3751_, lean_object* v_k_3752_, lean_object* v_kind_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
uint8_t v_kind_boxed_3759_; lean_object* v_res_3760_; 
v_kind_boxed_3759_ = lean_unbox(v_kind_3753_);
v_res_3760_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3751_, v_k_3752_, v_kind_boxed_3759_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3761_, lean_object* v_k_3762_, uint8_t v_kind_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_){
_start:
{
size_t v_sz_3769_; size_t v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_sz_3769_ = lean_array_size(v_declInfos_3761_);
v___x_3770_ = ((size_t)0ULL);
v___x_3771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3769_, v___x_3770_, v_declInfos_3761_);
v___x_3772_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3771_, v_k_3762_, v_kind_3763_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3773_, lean_object* v_k_3774_, lean_object* v_kind_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
uint8_t v_kind_boxed_3781_; lean_object* v_res_3782_; 
v_kind_boxed_3781_ = lean_unbox(v_kind_3775_);
v_res_3782_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3773_, v_k_3774_, v_kind_boxed_3781_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
return v_res_3782_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3785_ = lean_box(0);
v___x_3786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3787_ = l_Lean_mkConst(v___x_3786_, v___x_3785_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3788_, lean_object* v___x_3789_, lean_object* v_motive_3790_, uint8_t v___x_3791_, uint8_t v___x_3792_, uint8_t v___x_3793_, lean_object* v___x_3794_, lean_object* v_v_3795_, lean_object* v___x_3796_, lean_object* v_zs12_3797_, lean_object* v_is_3798_, lean_object* v_fields1_3799_, lean_object* v_fields2_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_){
_start:
{
lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v_e_3816_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
lean_inc(v___x_3788_);
v___x_3826_ = l_Lean_mkNatLit(v___x_3788_);
v___x_3827_ = l_Lean_Meta_mkEqRefl(v___x_3826_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref_known(v___x_3827_, 1);
lean_inc_ref(v___x_3789_);
v___x_3829_ = l_Lean_mkAppN(v___x_3789_, v_fields1_3799_);
v___x_3830_ = l_Lean_mkAppN(v___x_3789_, v_fields2_3800_);
v___x_3831_ = lean_unsigned_to_nat(3u);
v___x_3832_ = lean_mk_empty_array_with_capacity(v___x_3831_);
v___x_3833_ = lean_array_push(v___x_3832_, v___x_3829_);
v___x_3834_ = lean_array_push(v___x_3833_, v___x_3830_);
v___x_3835_ = lean_array_push(v___x_3834_, v_a_3828_);
v___x_3836_ = l_Array_append___redArg(v_is_3798_, v___x_3835_);
lean_dec_ref(v___x_3835_);
v___x_3837_ = l_Lean_mkAppN(v_motive_3790_, v___x_3836_);
lean_dec_ref(v___x_3836_);
v___x_3838_ = l_Lean_Meta_mkForallFVars(v_zs12_3797_, v___x_3837_, v___x_3791_, v___x_3792_, v___x_3792_, v___x_3793_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v___x_3840_; uint8_t v___x_3841_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v___x_3838_, 1);
v___x_3840_ = lean_array_get_size(v_zs12_3797_);
v___x_3841_ = lean_nat_dec_eq(v___x_3840_, v___x_3794_);
if (v___x_3841_ == 0)
{
v_e_3816_ = v_a_3839_;
goto v___jp_3815_;
}
else
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3843_ = l_Lean_mkArrow(v___x_3842_, v_a_3839_, v___y_3803_, v___y_3804_);
if (lean_obj_tag(v___x_3843_) == 0)
{
lean_object* v_a_3844_; 
v_a_3844_ = lean_ctor_get(v___x_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref_known(v___x_3843_, 1);
v_e_3816_ = v_a_3844_;
goto v___jp_3815_;
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
lean_dec(v_v_3795_);
lean_dec(v___x_3794_);
lean_dec(v___x_3788_);
v_a_3845_ = lean_ctor_get(v___x_3843_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___x_3843_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___x_3843_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec(v_v_3795_);
lean_dec(v___x_3794_);
lean_dec(v___x_3788_);
v_a_3853_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3838_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3838_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
else
{
lean_object* v_a_3861_; lean_object* v___x_3863_; uint8_t v_isShared_3864_; uint8_t v_isSharedCheck_3868_; 
lean_dec_ref(v_is_3798_);
lean_dec(v_v_3795_);
lean_dec(v___x_3794_);
lean_dec_ref(v_motive_3790_);
lean_dec_ref(v___x_3789_);
lean_dec(v___x_3788_);
v_a_3861_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3868_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3868_ == 0)
{
v___x_3863_ = v___x_3827_;
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
else
{
lean_inc(v_a_3861_);
lean_dec(v___x_3827_);
v___x_3863_ = lean_box(0);
v_isShared_3864_ = v_isSharedCheck_3868_;
goto v_resetjp_3862_;
}
v_resetjp_3862_:
{
lean_object* v___x_3866_; 
if (v_isShared_3864_ == 0)
{
v___x_3866_ = v___x_3863_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3867_; 
v_reuseFailAlloc_3867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3867_, 0, v_a_3861_);
v___x_3866_ = v_reuseFailAlloc_3867_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
return v___x_3866_;
}
}
}
v___jp_3806_:
{
lean_object* v___x_3809_; uint8_t v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; 
v___x_3809_ = lean_array_get_size(v_zs12_3797_);
v___x_3810_ = lean_nat_dec_eq(v___x_3809_, v___x_3794_);
v___x_3811_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3794_);
lean_ctor_set_uint8(v___x_3811_, sizeof(void*)*2, v___x_3810_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___y_3808_);
lean_ctor_set(v___x_3812_, 1, v___y_3807_);
v___x_3813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
lean_ctor_set(v___x_3813_, 1, v___x_3811_);
v___x_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3813_);
return v___x_3814_;
}
v___jp_3815_:
{
if (lean_obj_tag(v_v_3795_) == 1)
{
lean_object* v_str_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_dec(v___x_3788_);
v_str_3817_ = lean_ctor_get(v_v_3795_, 1);
lean_inc_ref(v_str_3817_);
lean_dec_ref_known(v_v_3795_, 2);
v___x_3818_ = lean_box(0);
v___x_3819_ = l_Lean_Name_str___override(v___x_3818_, v_str_3817_);
v___y_3807_ = v_e_3816_;
v___y_3808_ = v___x_3819_;
goto v___jp_3806_;
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_dec(v_v_3795_);
v___x_3820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3821_ = lean_nat_add(v___x_3788_, v___x_3796_);
lean_dec(v___x_3788_);
v___x_3822_ = l_Nat_reprFast(v___x_3821_);
v___x_3823_ = lean_string_append(v___x_3820_, v___x_3822_);
lean_dec_ref(v___x_3822_);
v___x_3824_ = lean_box(0);
v___x_3825_ = l_Lean_Name_str___override(v___x_3824_, v___x_3823_);
v___y_3807_ = v_e_3816_;
v___y_3808_ = v___x_3825_;
goto v___jp_3806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3869_ = _args[0];
lean_object* v___x_3870_ = _args[1];
lean_object* v_motive_3871_ = _args[2];
lean_object* v___x_3872_ = _args[3];
lean_object* v___x_3873_ = _args[4];
lean_object* v___x_3874_ = _args[5];
lean_object* v___x_3875_ = _args[6];
lean_object* v_v_3876_ = _args[7];
lean_object* v___x_3877_ = _args[8];
lean_object* v_zs12_3878_ = _args[9];
lean_object* v_is_3879_ = _args[10];
lean_object* v_fields1_3880_ = _args[11];
lean_object* v_fields2_3881_ = _args[12];
lean_object* v___y_3882_ = _args[13];
lean_object* v___y_3883_ = _args[14];
lean_object* v___y_3884_ = _args[15];
lean_object* v___y_3885_ = _args[16];
lean_object* v___y_3886_ = _args[17];
_start:
{
uint8_t v___x_16205__boxed_3887_; uint8_t v___x_16206__boxed_3888_; uint8_t v___x_16207__boxed_3889_; lean_object* v_res_3890_; 
v___x_16205__boxed_3887_ = lean_unbox(v___x_3872_);
v___x_16206__boxed_3888_ = lean_unbox(v___x_3873_);
v___x_16207__boxed_3889_ = lean_unbox(v___x_3874_);
v_res_3890_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3869_, v___x_3870_, v_motive_3871_, v___x_16205__boxed_3887_, v___x_16206__boxed_3888_, v___x_16207__boxed_3889_, v___x_3875_, v_v_3876_, v___x_3877_, v_zs12_3878_, v_is_3879_, v_fields1_3880_, v_fields2_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec_ref(v_fields2_3881_);
lean_dec_ref(v_fields1_3880_);
lean_dec_ref(v_zs12_3878_);
lean_dec(v___x_3877_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3891_, lean_object* v_params_3892_, lean_object* v_motive_3893_, size_t v_sz_3894_, size_t v_i_3895_, lean_object* v_bs_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
uint8_t v___x_3902_; 
v___x_3902_ = lean_usize_dec_lt(v_i_3895_, v_sz_3894_);
if (v___x_3902_ == 0)
{
lean_object* v___x_3903_; 
lean_dec_ref(v_motive_3893_);
lean_dec(v_tail_3891_);
v___x_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3903_, 0, v_bs_3896_);
return v___x_3903_;
}
else
{
lean_object* v___x_3904_; lean_object* v___x_3905_; uint8_t v___x_3906_; uint8_t v___x_3907_; lean_object* v_v_3908_; lean_object* v_bs_x27_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___f_3916_; lean_object* v___x_3917_; 
v___x_3904_ = lean_unsigned_to_nat(0u);
v___x_3905_ = lean_unsigned_to_nat(1u);
v___x_3906_ = 0;
v___x_3907_ = 1;
v_v_3908_ = lean_array_uget(v_bs_3896_, v_i_3895_);
v_bs_x27_3909_ = lean_array_uset(v_bs_3896_, v_i_3895_, v___x_3904_);
v___x_3910_ = lean_usize_to_nat(v_i_3895_);
lean_inc(v_tail_3891_);
lean_inc(v_v_3908_);
v___x_3911_ = l_Lean_mkConst(v_v_3908_, v_tail_3891_);
v___x_3912_ = l_Lean_mkAppN(v___x_3911_, v_params_3892_);
v___x_3913_ = lean_box(v___x_3906_);
v___x_3914_ = lean_box(v___x_3902_);
v___x_3915_ = lean_box(v___x_3907_);
lean_inc_ref(v_motive_3893_);
lean_inc_ref(v___x_3912_);
v___f_3916_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3916_, 0, v___x_3910_);
lean_closure_set(v___f_3916_, 1, v___x_3912_);
lean_closure_set(v___f_3916_, 2, v_motive_3893_);
lean_closure_set(v___f_3916_, 3, v___x_3913_);
lean_closure_set(v___f_3916_, 4, v___x_3914_);
lean_closure_set(v___f_3916_, 5, v___x_3915_);
lean_closure_set(v___f_3916_, 6, v___x_3904_);
lean_closure_set(v___f_3916_, 7, v_v_3908_);
lean_closure_set(v___f_3916_, 8, v___x_3905_);
v___x_3917_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3912_, v___f_3916_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; size_t v___x_3919_; size_t v___x_3920_; lean_object* v___x_3921_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3917_, 1);
v___x_3919_ = ((size_t)1ULL);
v___x_3920_ = lean_usize_add(v_i_3895_, v___x_3919_);
v___x_3921_ = lean_array_uset(v_bs_x27_3909_, v_i_3895_, v_a_3918_);
v_i_3895_ = v___x_3920_;
v_bs_3896_ = v___x_3921_;
goto _start;
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec_ref(v_bs_x27_3909_);
lean_dec_ref(v_motive_3893_);
lean_dec(v_tail_3891_);
v_a_3923_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3917_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3917_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3931_, lean_object* v_params_3932_, lean_object* v_motive_3933_, lean_object* v_sz_3934_, lean_object* v_i_3935_, lean_object* v_bs_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
size_t v_sz_boxed_3942_; size_t v_i_boxed_3943_; lean_object* v_res_3944_; 
v_sz_boxed_3942_ = lean_unbox_usize(v_sz_3934_);
lean_dec(v_sz_3934_);
v_i_boxed_3943_ = lean_unbox_usize(v_i_3935_);
lean_dec(v_i_3935_);
v_res_3944_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3931_, v_params_3932_, v_motive_3933_, v_sz_boxed_3942_, v_i_boxed_3943_, v_bs_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec_ref(v_params_3932_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_3947_, lean_object* v_tail_3948_, lean_object* v_params_3949_, lean_object* v_numIndices_3950_, lean_object* v___x_3951_, lean_object* v___x_3952_, uint8_t v___x_3953_, uint8_t v___x_3954_, uint8_t v___x_3955_, lean_object* v_is_3956_, lean_object* v___x_3957_, lean_object* v___x_3958_, lean_object* v___x_3959_, lean_object* v___x_3960_, lean_object* v___x_3961_, lean_object* v___x_3962_, lean_object* v_heq_3963_, lean_object* v_val_3964_, lean_object* v___x_3965_, lean_object* v_declName_3966_, lean_object* v_levelParams_3967_, lean_object* v___x_3968_, lean_object* v___x_3969_, lean_object* v_numParams_3970_, lean_object* v___x_3971_, lean_object* v_motive_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v___x_3978_; size_t v_sz_3979_; size_t v___x_3980_; lean_object* v___x_3981_; 
v___x_3978_ = lean_array_mk(v_ctors_3947_);
v_sz_3979_ = lean_array_size(v___x_3978_);
v___x_3980_ = ((size_t)0ULL);
lean_inc_ref(v___x_3978_);
lean_inc_ref(v_motive_3972_);
lean_inc(v_tail_3948_);
v___x_3981_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3948_, v_params_3949_, v_motive_3972_, v_sz_3979_, v___x_3980_, v___x_3978_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; lean_object* v___x_3983_; lean_object* v_fst_3984_; lean_object* v_snd_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___f_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3983_ = l_Array_unzip___redArg(v_a_3982_);
lean_dec(v_a_3982_);
v_fst_3984_ = lean_ctor_get(v___x_3983_, 0);
lean_inc(v_fst_3984_);
v_snd_3985_ = lean_ctor_get(v___x_3983_, 1);
lean_inc(v_snd_3985_);
lean_dec_ref(v___x_3983_);
v___x_3986_ = lean_box(v___x_3953_);
v___x_3987_ = lean_box(v___x_3954_);
v___x_3988_ = lean_box(v___x_3955_);
v___x_3989_ = lean_box_usize(v_sz_3979_);
v___x_3990_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_3991_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_3991_, 0, v_numIndices_3950_);
lean_closure_set(v___f_3991_, 1, v___x_3951_);
lean_closure_set(v___f_3991_, 2, v_motive_3972_);
lean_closure_set(v___f_3991_, 3, v___x_3952_);
lean_closure_set(v___f_3991_, 4, v___x_3986_);
lean_closure_set(v___f_3991_, 5, v___x_3987_);
lean_closure_set(v___f_3991_, 6, v___x_3988_);
lean_closure_set(v___f_3991_, 7, v_is_3956_);
lean_closure_set(v___f_3991_, 8, v___x_3957_);
lean_closure_set(v___f_3991_, 9, v___x_3958_);
lean_closure_set(v___f_3991_, 10, v___x_3959_);
lean_closure_set(v___f_3991_, 11, v___x_3960_);
lean_closure_set(v___f_3991_, 12, v_params_3949_);
lean_closure_set(v___f_3991_, 13, v___x_3961_);
lean_closure_set(v___f_3991_, 14, v___x_3962_);
lean_closure_set(v___f_3991_, 15, v_heq_3963_);
lean_closure_set(v___f_3991_, 16, v_val_3964_);
lean_closure_set(v___f_3991_, 17, v_tail_3948_);
lean_closure_set(v___f_3991_, 18, v___x_3989_);
lean_closure_set(v___f_3991_, 19, v___x_3990_);
lean_closure_set(v___f_3991_, 20, v___x_3978_);
lean_closure_set(v___f_3991_, 21, v___x_3965_);
lean_closure_set(v___f_3991_, 22, v_declName_3966_);
lean_closure_set(v___f_3991_, 23, v_levelParams_3967_);
lean_closure_set(v___f_3991_, 24, v___x_3968_);
lean_closure_set(v___f_3991_, 25, v___x_3969_);
lean_closure_set(v___f_3991_, 26, v_numParams_3970_);
lean_closure_set(v___f_3991_, 27, v_snd_3985_);
lean_closure_set(v___f_3991_, 28, v___x_3971_);
v___x_3992_ = 0;
v___x_3993_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_3984_, v___f_3991_, v___x_3992_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
return v___x_3993_;
}
else
{
lean_object* v_a_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4001_; 
lean_dec_ref(v___x_3978_);
lean_dec_ref(v_motive_3972_);
lean_dec_ref(v___x_3971_);
lean_dec(v_numParams_3970_);
lean_dec(v___x_3969_);
lean_dec(v___x_3968_);
lean_dec(v_levelParams_3967_);
lean_dec(v_declName_3966_);
lean_dec_ref(v___x_3965_);
lean_dec_ref(v_val_3964_);
lean_dec_ref(v_heq_3963_);
lean_dec_ref(v___x_3962_);
lean_dec_ref(v___x_3961_);
lean_dec(v___x_3960_);
lean_dec(v___x_3959_);
lean_dec_ref(v___x_3958_);
lean_dec_ref(v___x_3957_);
lean_dec_ref(v_is_3956_);
lean_dec_ref(v___x_3952_);
lean_dec(v___x_3951_);
lean_dec(v_numIndices_3950_);
lean_dec_ref(v_params_3949_);
lean_dec(v_tail_3948_);
v_a_3994_ = lean_ctor_get(v___x_3981_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3981_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3996_ = v___x_3981_;
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_a_3994_);
lean_dec(v___x_3981_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4001_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v___x_3999_; 
if (v_isShared_3997_ == 0)
{
v___x_3999_ = v___x_3996_;
goto v_reusejp_3998_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3994_);
v___x_3999_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3998_;
}
v_reusejp_3998_:
{
return v___x_3999_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4002_ = _args[0];
lean_object* v_tail_4003_ = _args[1];
lean_object* v_params_4004_ = _args[2];
lean_object* v_numIndices_4005_ = _args[3];
lean_object* v___x_4006_ = _args[4];
lean_object* v___x_4007_ = _args[5];
lean_object* v___x_4008_ = _args[6];
lean_object* v___x_4009_ = _args[7];
lean_object* v___x_4010_ = _args[8];
lean_object* v_is_4011_ = _args[9];
lean_object* v___x_4012_ = _args[10];
lean_object* v___x_4013_ = _args[11];
lean_object* v___x_4014_ = _args[12];
lean_object* v___x_4015_ = _args[13];
lean_object* v___x_4016_ = _args[14];
lean_object* v___x_4017_ = _args[15];
lean_object* v_heq_4018_ = _args[16];
lean_object* v_val_4019_ = _args[17];
lean_object* v___x_4020_ = _args[18];
lean_object* v_declName_4021_ = _args[19];
lean_object* v_levelParams_4022_ = _args[20];
lean_object* v___x_4023_ = _args[21];
lean_object* v___x_4024_ = _args[22];
lean_object* v_numParams_4025_ = _args[23];
lean_object* v___x_4026_ = _args[24];
lean_object* v_motive_4027_ = _args[25];
lean_object* v___y_4028_ = _args[26];
lean_object* v___y_4029_ = _args[27];
lean_object* v___y_4030_ = _args[28];
lean_object* v___y_4031_ = _args[29];
lean_object* v___y_4032_ = _args[30];
_start:
{
uint8_t v___x_16444__boxed_4033_; uint8_t v___x_16445__boxed_4034_; uint8_t v___x_16446__boxed_4035_; lean_object* v_res_4036_; 
v___x_16444__boxed_4033_ = lean_unbox(v___x_4008_);
v___x_16445__boxed_4034_ = lean_unbox(v___x_4009_);
v___x_16446__boxed_4035_ = lean_unbox(v___x_4010_);
v_res_4036_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4002_, v_tail_4003_, v_params_4004_, v_numIndices_4005_, v___x_4006_, v___x_4007_, v___x_16444__boxed_4033_, v___x_16445__boxed_4034_, v___x_16446__boxed_4035_, v_is_4011_, v___x_4012_, v___x_4013_, v___x_4014_, v___x_4015_, v___x_4016_, v___x_4017_, v_heq_4018_, v_val_4019_, v___x_4020_, v_declName_4021_, v_levelParams_4022_, v___x_4023_, v___x_4024_, v_numParams_4025_, v___x_4026_, v_motive_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4037_, lean_object* v___x_4038_, lean_object* v_is_4039_, lean_object* v_head_4040_, lean_object* v_ctors_4041_, lean_object* v_tail_4042_, lean_object* v_params_4043_, lean_object* v_numIndices_4044_, lean_object* v___x_4045_, lean_object* v___x_4046_, lean_object* v___x_4047_, lean_object* v___x_4048_, lean_object* v___x_4049_, lean_object* v_val_4050_, lean_object* v___x_4051_, lean_object* v_declName_4052_, lean_object* v_levelParams_4053_, lean_object* v___x_4054_, lean_object* v_numParams_4055_, lean_object* v___x_4056_, lean_object* v_heq_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; uint8_t v___x_4070_; uint8_t v___x_4071_; uint8_t v___x_4072_; lean_object* v___x_4073_; 
v___x_4063_ = lean_unsigned_to_nat(3u);
v___x_4064_ = lean_mk_empty_array_with_capacity(v___x_4063_);
lean_inc_ref(v___x_4037_);
v___x_4065_ = lean_array_push(v___x_4064_, v___x_4037_);
lean_inc_ref(v___x_4038_);
v___x_4066_ = lean_array_push(v___x_4065_, v___x_4038_);
lean_inc_ref(v_heq_4057_);
v___x_4067_ = lean_array_push(v___x_4066_, v_heq_4057_);
lean_inc_ref(v_is_4039_);
v___x_4068_ = l_Array_append___redArg(v_is_4039_, v___x_4067_);
lean_dec_ref(v___x_4067_);
v___x_4069_ = l_Lean_mkSort(v_head_4040_);
v___x_4070_ = 0;
v___x_4071_ = 1;
v___x_4072_ = 1;
v___x_4073_ = l_Lean_Meta_mkForallFVars(v___x_4068_, v___x_4069_, v___x_4070_, v___x_4071_, v___x_4071_, v___x_4072_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4073_) == 0)
{
lean_object* v_a_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___f_4078_; lean_object* v___x_4079_; uint8_t v___x_4080_; lean_object* v___x_4081_; 
v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4073_, 1);
v___x_4075_ = lean_box(v___x_4070_);
v___x_4076_ = lean_box(v___x_4071_);
v___x_4077_ = lean_box(v___x_4072_);
v___f_4078_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4078_, 0, v_ctors_4041_);
lean_closure_set(v___f_4078_, 1, v_tail_4042_);
lean_closure_set(v___f_4078_, 2, v_params_4043_);
lean_closure_set(v___f_4078_, 3, v_numIndices_4044_);
lean_closure_set(v___f_4078_, 4, v___x_4045_);
lean_closure_set(v___f_4078_, 5, v___x_4068_);
lean_closure_set(v___f_4078_, 6, v___x_4075_);
lean_closure_set(v___f_4078_, 7, v___x_4076_);
lean_closure_set(v___f_4078_, 8, v___x_4077_);
lean_closure_set(v___f_4078_, 9, v_is_4039_);
lean_closure_set(v___f_4078_, 10, v___x_4038_);
lean_closure_set(v___f_4078_, 11, v___x_4037_);
lean_closure_set(v___f_4078_, 12, v___x_4046_);
lean_closure_set(v___f_4078_, 13, v___x_4047_);
lean_closure_set(v___f_4078_, 14, v___x_4048_);
lean_closure_set(v___f_4078_, 15, v___x_4049_);
lean_closure_set(v___f_4078_, 16, v_heq_4057_);
lean_closure_set(v___f_4078_, 17, v_val_4050_);
lean_closure_set(v___f_4078_, 18, v___x_4051_);
lean_closure_set(v___f_4078_, 19, v_declName_4052_);
lean_closure_set(v___f_4078_, 20, v_levelParams_4053_);
lean_closure_set(v___f_4078_, 21, v___x_4063_);
lean_closure_set(v___f_4078_, 22, v___x_4054_);
lean_closure_set(v___f_4078_, 23, v_numParams_4055_);
lean_closure_set(v___f_4078_, 24, v___x_4056_);
v___x_4079_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4080_ = 0;
v___x_4081_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4079_, v___x_4072_, v_a_4074_, v___f_4078_, v___x_4080_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
return v___x_4081_;
}
else
{
lean_object* v_a_4082_; lean_object* v___x_4084_; uint8_t v_isShared_4085_; uint8_t v_isSharedCheck_4089_; 
lean_dec_ref(v___x_4068_);
lean_dec_ref(v_heq_4057_);
lean_dec_ref(v___x_4056_);
lean_dec(v_numParams_4055_);
lean_dec(v___x_4054_);
lean_dec(v_levelParams_4053_);
lean_dec(v_declName_4052_);
lean_dec_ref(v___x_4051_);
lean_dec_ref(v_val_4050_);
lean_dec_ref(v___x_4049_);
lean_dec_ref(v___x_4048_);
lean_dec(v___x_4047_);
lean_dec(v___x_4046_);
lean_dec(v___x_4045_);
lean_dec(v_numIndices_4044_);
lean_dec_ref(v_params_4043_);
lean_dec(v_tail_4042_);
lean_dec(v_ctors_4041_);
lean_dec_ref(v_is_4039_);
lean_dec_ref(v___x_4038_);
lean_dec_ref(v___x_4037_);
v_a_4082_ = lean_ctor_get(v___x_4073_, 0);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4084_ = v___x_4073_;
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
else
{
lean_inc(v_a_4082_);
lean_dec(v___x_4073_);
v___x_4084_ = lean_box(0);
v_isShared_4085_ = v_isSharedCheck_4089_;
goto v_resetjp_4083_;
}
v_resetjp_4083_:
{
lean_object* v___x_4087_; 
if (v_isShared_4085_ == 0)
{
v___x_4087_ = v___x_4084_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v_a_4082_);
v___x_4087_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
return v___x_4087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4090_ = _args[0];
lean_object* v___x_4091_ = _args[1];
lean_object* v_is_4092_ = _args[2];
lean_object* v_head_4093_ = _args[3];
lean_object* v_ctors_4094_ = _args[4];
lean_object* v_tail_4095_ = _args[5];
lean_object* v_params_4096_ = _args[6];
lean_object* v_numIndices_4097_ = _args[7];
lean_object* v___x_4098_ = _args[8];
lean_object* v___x_4099_ = _args[9];
lean_object* v___x_4100_ = _args[10];
lean_object* v___x_4101_ = _args[11];
lean_object* v___x_4102_ = _args[12];
lean_object* v_val_4103_ = _args[13];
lean_object* v___x_4104_ = _args[14];
lean_object* v_declName_4105_ = _args[15];
lean_object* v_levelParams_4106_ = _args[16];
lean_object* v___x_4107_ = _args[17];
lean_object* v_numParams_4108_ = _args[18];
lean_object* v___x_4109_ = _args[19];
lean_object* v_heq_4110_ = _args[20];
lean_object* v___y_4111_ = _args[21];
lean_object* v___y_4112_ = _args[22];
lean_object* v___y_4113_ = _args[23];
lean_object* v___y_4114_ = _args[24];
lean_object* v___y_4115_ = _args[25];
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4090_, v___x_4091_, v_is_4092_, v_head_4093_, v_ctors_4094_, v_tail_4095_, v_params_4096_, v_numIndices_4097_, v___x_4098_, v___x_4099_, v___x_4100_, v___x_4101_, v___x_4102_, v_val_4103_, v___x_4104_, v_declName_4105_, v_levelParams_4106_, v___x_4107_, v_numParams_4108_, v___x_4109_, v_heq_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4117_, lean_object* v_x1_4118_, lean_object* v_indName_4119_, lean_object* v_tail_4120_, lean_object* v_params_4121_, lean_object* v_is_4122_, lean_object* v___x_4123_, lean_object* v_head_4124_, lean_object* v_ctors_4125_, lean_object* v_numIndices_4126_, lean_object* v___x_4127_, lean_object* v___x_4128_, lean_object* v_val_4129_, lean_object* v_declName_4130_, lean_object* v_levelParams_4131_, lean_object* v_numParams_4132_, lean_object* v___x_4133_, lean_object* v_x2_4134_, lean_object* v_x_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4141_ = lean_unsigned_to_nat(0u);
v___x_4142_ = lean_array_get_borrowed(v___x_4117_, v_x1_4118_, v___x_4141_);
v___x_4143_ = lean_array_get_borrowed(v___x_4117_, v_x2_4134_, v___x_4141_);
v___x_4144_ = l_Lean_mkCtorIdxName(v_indName_4119_);
lean_inc(v_tail_4120_);
v___x_4145_ = l_Lean_mkConst(v___x_4144_, v_tail_4120_);
lean_inc_ref(v_params_4121_);
v___x_4146_ = l_Array_append___redArg(v_params_4121_, v_is_4122_);
v___x_4147_ = lean_mk_empty_array_with_capacity(v___x_4123_);
lean_inc(v___x_4142_);
lean_inc_ref_n(v___x_4147_, 2);
v___x_4148_ = lean_array_push(v___x_4147_, v___x_4142_);
lean_inc_ref(v___x_4146_);
v___x_4149_ = l_Array_append___redArg(v___x_4146_, v___x_4148_);
lean_inc_ref(v___x_4145_);
v___x_4150_ = l_Lean_mkAppN(v___x_4145_, v___x_4149_);
lean_dec_ref(v___x_4149_);
lean_inc(v___x_4143_);
v___x_4151_ = lean_array_push(v___x_4147_, v___x_4143_);
v___x_4152_ = l_Array_append___redArg(v___x_4146_, v___x_4151_);
v___x_4153_ = l_Lean_mkAppN(v___x_4145_, v___x_4152_);
lean_dec_ref(v___x_4152_);
v___x_4154_ = l_Lean_Meta_mkEq(v___x_4150_, v___x_4153_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___f_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_a_4155_);
lean_dec_ref_known(v___x_4154_, 1);
lean_inc(v___x_4143_);
lean_inc(v___x_4142_);
v___f_4156_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4156_, 0, v___x_4142_);
lean_closure_set(v___f_4156_, 1, v___x_4143_);
lean_closure_set(v___f_4156_, 2, v_is_4122_);
lean_closure_set(v___f_4156_, 3, v_head_4124_);
lean_closure_set(v___f_4156_, 4, v_ctors_4125_);
lean_closure_set(v___f_4156_, 5, v_tail_4120_);
lean_closure_set(v___f_4156_, 6, v_params_4121_);
lean_closure_set(v___f_4156_, 7, v_numIndices_4126_);
lean_closure_set(v___f_4156_, 8, v___x_4123_);
lean_closure_set(v___f_4156_, 9, v___x_4127_);
lean_closure_set(v___f_4156_, 10, v___x_4128_);
lean_closure_set(v___f_4156_, 11, v___x_4148_);
lean_closure_set(v___f_4156_, 12, v___x_4151_);
lean_closure_set(v___f_4156_, 13, v_val_4129_);
lean_closure_set(v___f_4156_, 14, v___x_4147_);
lean_closure_set(v___f_4156_, 15, v_declName_4130_);
lean_closure_set(v___f_4156_, 16, v_levelParams_4131_);
lean_closure_set(v___f_4156_, 17, v___x_4141_);
lean_closure_set(v___f_4156_, 18, v_numParams_4132_);
lean_closure_set(v___f_4156_, 19, v___x_4133_);
v___x_4157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4158_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4157_, v_a_4155_, v___f_4156_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
return v___x_4158_;
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_dec_ref(v___x_4151_);
lean_dec_ref(v___x_4148_);
lean_dec_ref(v___x_4147_);
lean_dec_ref(v___x_4133_);
lean_dec(v_numParams_4132_);
lean_dec(v_levelParams_4131_);
lean_dec(v_declName_4130_);
lean_dec_ref(v_val_4129_);
lean_dec(v___x_4128_);
lean_dec(v___x_4127_);
lean_dec(v_numIndices_4126_);
lean_dec(v_ctors_4125_);
lean_dec(v_head_4124_);
lean_dec(v___x_4123_);
lean_dec_ref(v_is_4122_);
lean_dec_ref(v_params_4121_);
lean_dec(v_tail_4120_);
v_a_4159_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4154_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4154_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4167_ = _args[0];
lean_object* v_x1_4168_ = _args[1];
lean_object* v_indName_4169_ = _args[2];
lean_object* v_tail_4170_ = _args[3];
lean_object* v_params_4171_ = _args[4];
lean_object* v_is_4172_ = _args[5];
lean_object* v___x_4173_ = _args[6];
lean_object* v_head_4174_ = _args[7];
lean_object* v_ctors_4175_ = _args[8];
lean_object* v_numIndices_4176_ = _args[9];
lean_object* v___x_4177_ = _args[10];
lean_object* v___x_4178_ = _args[11];
lean_object* v_val_4179_ = _args[12];
lean_object* v_declName_4180_ = _args[13];
lean_object* v_levelParams_4181_ = _args[14];
lean_object* v_numParams_4182_ = _args[15];
lean_object* v___x_4183_ = _args[16];
lean_object* v_x2_4184_ = _args[17];
lean_object* v_x_4185_ = _args[18];
lean_object* v___y_4186_ = _args[19];
lean_object* v___y_4187_ = _args[20];
lean_object* v___y_4188_ = _args[21];
lean_object* v___y_4189_ = _args[22];
lean_object* v___y_4190_ = _args[23];
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4167_, v_x1_4168_, v_indName_4169_, v_tail_4170_, v_params_4171_, v_is_4172_, v___x_4173_, v_head_4174_, v_ctors_4175_, v_numIndices_4176_, v___x_4177_, v___x_4178_, v_val_4179_, v_declName_4180_, v_levelParams_4181_, v_numParams_4182_, v___x_4183_, v_x2_4184_, v_x_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec_ref(v_x_4185_);
lean_dec_ref(v_x2_4184_);
lean_dec_ref(v_x1_4168_);
lean_dec_ref(v___x_4167_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4192_, lean_object* v_indName_4193_, lean_object* v_tail_4194_, lean_object* v_params_4195_, lean_object* v_is_4196_, lean_object* v___x_4197_, lean_object* v_head_4198_, lean_object* v_ctors_4199_, lean_object* v_numIndices_4200_, lean_object* v___x_4201_, lean_object* v___x_4202_, lean_object* v_val_4203_, lean_object* v_declName_4204_, lean_object* v_levelParams_4205_, lean_object* v_numParams_4206_, lean_object* v___x_4207_, lean_object* v_t_4208_, lean_object* v___x_4209_, lean_object* v_x1_4210_, lean_object* v_x_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v___f_4217_; uint8_t v___x_4218_; lean_object* v___x_4219_; 
v___f_4217_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4217_, 0, v___x_4192_);
lean_closure_set(v___f_4217_, 1, v_x1_4210_);
lean_closure_set(v___f_4217_, 2, v_indName_4193_);
lean_closure_set(v___f_4217_, 3, v_tail_4194_);
lean_closure_set(v___f_4217_, 4, v_params_4195_);
lean_closure_set(v___f_4217_, 5, v_is_4196_);
lean_closure_set(v___f_4217_, 6, v___x_4197_);
lean_closure_set(v___f_4217_, 7, v_head_4198_);
lean_closure_set(v___f_4217_, 8, v_ctors_4199_);
lean_closure_set(v___f_4217_, 9, v_numIndices_4200_);
lean_closure_set(v___f_4217_, 10, v___x_4201_);
lean_closure_set(v___f_4217_, 11, v___x_4202_);
lean_closure_set(v___f_4217_, 12, v_val_4203_);
lean_closure_set(v___f_4217_, 13, v_declName_4204_);
lean_closure_set(v___f_4217_, 14, v_levelParams_4205_);
lean_closure_set(v___f_4217_, 15, v_numParams_4206_);
lean_closure_set(v___f_4217_, 16, v___x_4207_);
v___x_4218_ = 0;
v___x_4219_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4208_, v___x_4209_, v___f_4217_, v___x_4218_, v___x_4218_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4220_ = _args[0];
lean_object* v_indName_4221_ = _args[1];
lean_object* v_tail_4222_ = _args[2];
lean_object* v_params_4223_ = _args[3];
lean_object* v_is_4224_ = _args[4];
lean_object* v___x_4225_ = _args[5];
lean_object* v_head_4226_ = _args[6];
lean_object* v_ctors_4227_ = _args[7];
lean_object* v_numIndices_4228_ = _args[8];
lean_object* v___x_4229_ = _args[9];
lean_object* v___x_4230_ = _args[10];
lean_object* v_val_4231_ = _args[11];
lean_object* v_declName_4232_ = _args[12];
lean_object* v_levelParams_4233_ = _args[13];
lean_object* v_numParams_4234_ = _args[14];
lean_object* v___x_4235_ = _args[15];
lean_object* v_t_4236_ = _args[16];
lean_object* v___x_4237_ = _args[17];
lean_object* v_x1_4238_ = _args[18];
lean_object* v_x_4239_ = _args[19];
lean_object* v___y_4240_ = _args[20];
lean_object* v___y_4241_ = _args[21];
lean_object* v___y_4242_ = _args[22];
lean_object* v___y_4243_ = _args[23];
lean_object* v___y_4244_ = _args[24];
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4220_, v_indName_4221_, v_tail_4222_, v_params_4223_, v_is_4224_, v___x_4225_, v_head_4226_, v_ctors_4227_, v_numIndices_4228_, v___x_4229_, v___x_4230_, v_val_4231_, v_declName_4232_, v_levelParams_4233_, v_numParams_4234_, v___x_4235_, v_t_4236_, v___x_4237_, v_x1_4238_, v_x_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec_ref(v_x_4239_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4246_, lean_object* v_indName_4247_, lean_object* v_tail_4248_, lean_object* v_params_4249_, lean_object* v_head_4250_, lean_object* v_ctors_4251_, lean_object* v_numIndices_4252_, lean_object* v___x_4253_, lean_object* v___x_4254_, lean_object* v_val_4255_, lean_object* v_declName_4256_, lean_object* v_levelParams_4257_, lean_object* v_numParams_4258_, lean_object* v___x_4259_, lean_object* v_is_4260_, lean_object* v_t_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___f_4269_; uint8_t v___x_4270_; lean_object* v___x_4271_; 
v___x_4267_ = lean_unsigned_to_nat(1u);
v___x_4268_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4261_);
v___f_4269_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4269_, 0, v___x_4246_);
lean_closure_set(v___f_4269_, 1, v_indName_4247_);
lean_closure_set(v___f_4269_, 2, v_tail_4248_);
lean_closure_set(v___f_4269_, 3, v_params_4249_);
lean_closure_set(v___f_4269_, 4, v_is_4260_);
lean_closure_set(v___f_4269_, 5, v___x_4267_);
lean_closure_set(v___f_4269_, 6, v_head_4250_);
lean_closure_set(v___f_4269_, 7, v_ctors_4251_);
lean_closure_set(v___f_4269_, 8, v_numIndices_4252_);
lean_closure_set(v___f_4269_, 9, v___x_4253_);
lean_closure_set(v___f_4269_, 10, v___x_4254_);
lean_closure_set(v___f_4269_, 11, v_val_4255_);
lean_closure_set(v___f_4269_, 12, v_declName_4256_);
lean_closure_set(v___f_4269_, 13, v_levelParams_4257_);
lean_closure_set(v___f_4269_, 14, v_numParams_4258_);
lean_closure_set(v___f_4269_, 15, v___x_4259_);
lean_closure_set(v___f_4269_, 16, v_t_4261_);
lean_closure_set(v___f_4269_, 17, v___x_4268_);
v___x_4270_ = 0;
v___x_4271_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4261_, v___x_4268_, v___f_4269_, v___x_4270_, v___x_4270_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4272_ = _args[0];
lean_object* v_indName_4273_ = _args[1];
lean_object* v_tail_4274_ = _args[2];
lean_object* v_params_4275_ = _args[3];
lean_object* v_head_4276_ = _args[4];
lean_object* v_ctors_4277_ = _args[5];
lean_object* v_numIndices_4278_ = _args[6];
lean_object* v___x_4279_ = _args[7];
lean_object* v___x_4280_ = _args[8];
lean_object* v_val_4281_ = _args[9];
lean_object* v_declName_4282_ = _args[10];
lean_object* v_levelParams_4283_ = _args[11];
lean_object* v_numParams_4284_ = _args[12];
lean_object* v___x_4285_ = _args[13];
lean_object* v_is_4286_ = _args[14];
lean_object* v_t_4287_ = _args[15];
lean_object* v___y_4288_ = _args[16];
lean_object* v___y_4289_ = _args[17];
lean_object* v___y_4290_ = _args[18];
lean_object* v___y_4291_ = _args[19];
lean_object* v___y_4292_ = _args[20];
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4272_, v_indName_4273_, v_tail_4274_, v_params_4275_, v_head_4276_, v_ctors_4277_, v_numIndices_4278_, v___x_4279_, v___x_4280_, v_val_4281_, v_declName_4282_, v_levelParams_4283_, v_numParams_4284_, v___x_4285_, v_is_4286_, v_t_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4294_, lean_object* v_indName_4295_, lean_object* v_tail_4296_, lean_object* v_head_4297_, lean_object* v_ctors_4298_, lean_object* v_numIndices_4299_, lean_object* v___x_4300_, lean_object* v___x_4301_, lean_object* v_val_4302_, lean_object* v_declName_4303_, lean_object* v_levelParams_4304_, lean_object* v_numParams_4305_, lean_object* v_params_4306_, lean_object* v_t_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; lean_object* v___f_4314_; lean_object* v___x_4315_; uint8_t v___x_4316_; lean_object* v___x_4317_; 
v___x_4313_ = l_Lean_Expr_bindingBody_x21(v_t_4307_);
lean_inc_ref(v___x_4313_);
lean_inc(v_numIndices_4299_);
v___f_4314_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4314_, 0, v___x_4294_);
lean_closure_set(v___f_4314_, 1, v_indName_4295_);
lean_closure_set(v___f_4314_, 2, v_tail_4296_);
lean_closure_set(v___f_4314_, 3, v_params_4306_);
lean_closure_set(v___f_4314_, 4, v_head_4297_);
lean_closure_set(v___f_4314_, 5, v_ctors_4298_);
lean_closure_set(v___f_4314_, 6, v_numIndices_4299_);
lean_closure_set(v___f_4314_, 7, v___x_4300_);
lean_closure_set(v___f_4314_, 8, v___x_4301_);
lean_closure_set(v___f_4314_, 9, v_val_4302_);
lean_closure_set(v___f_4314_, 10, v_declName_4303_);
lean_closure_set(v___f_4314_, 11, v_levelParams_4304_);
lean_closure_set(v___f_4314_, 12, v_numParams_4305_);
lean_closure_set(v___f_4314_, 13, v___x_4313_);
v___x_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4315_, 0, v_numIndices_4299_);
v___x_4316_ = 0;
v___x_4317_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4313_, v___x_4315_, v___f_4314_, v___x_4316_, v___x_4316_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
return v___x_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4318_ = _args[0];
lean_object* v_indName_4319_ = _args[1];
lean_object* v_tail_4320_ = _args[2];
lean_object* v_head_4321_ = _args[3];
lean_object* v_ctors_4322_ = _args[4];
lean_object* v_numIndices_4323_ = _args[5];
lean_object* v___x_4324_ = _args[6];
lean_object* v___x_4325_ = _args[7];
lean_object* v_val_4326_ = _args[8];
lean_object* v_declName_4327_ = _args[9];
lean_object* v_levelParams_4328_ = _args[10];
lean_object* v_numParams_4329_ = _args[11];
lean_object* v_params_4330_ = _args[12];
lean_object* v_t_4331_ = _args[13];
lean_object* v___y_4332_ = _args[14];
lean_object* v___y_4333_ = _args[15];
lean_object* v___y_4334_ = _args[16];
lean_object* v___y_4335_ = _args[17];
lean_object* v___y_4336_ = _args[18];
_start:
{
lean_object* v_res_4337_; 
v_res_4337_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4318_, v_indName_4319_, v_tail_4320_, v_head_4321_, v_ctors_4322_, v_numIndices_4323_, v___x_4324_, v___x_4325_, v_val_4326_, v_declName_4327_, v_levelParams_4328_, v_numParams_4329_, v_params_4330_, v_t_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
lean_dec_ref(v_t_4331_);
return v_res_4337_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4342_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4343_ = lean_unsigned_to_nat(58u);
v___x_4344_ = lean_unsigned_to_nat(142u);
v___x_4345_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4346_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4347_ = l_mkPanicMessageWithDecl(v___x_4346_, v___x_4345_, v___x_4344_, v___x_4343_, v___x_4342_);
return v___x_4347_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4348_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4349_ = lean_unsigned_to_nat(60u);
v___x_4350_ = lean_unsigned_to_nat(136u);
v___x_4351_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4352_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4353_ = l_mkPanicMessageWithDecl(v___x_4352_, v___x_4351_, v___x_4350_, v___x_4349_, v___x_4348_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4354_, lean_object* v_indName_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v___x_4361_; 
lean_inc(v_indName_4355_);
v___x_4361_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4361_, 1);
if (lean_obj_tag(v_a_4362_) == 5)
{
lean_object* v_val_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v_val_4363_ = lean_ctor_get(v_a_4362_, 0);
lean_inc_ref(v_val_4363_);
lean_dec_ref_known(v_a_4362_, 1);
v___x_4364_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4354_);
v___x_4365_ = l_Lean_Name_append(v_declName_4354_, v___x_4364_);
lean_inc(v_indName_4355_);
lean_inc(v___x_4365_);
v___x_4366_ = l_Lean_mkCasesOnSameCtorHet(v___x_4365_, v_indName_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4399_; 
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4399_ == 0)
{
lean_object* v_unused_4400_; 
v_unused_4400_ = lean_ctor_get(v___x_4366_, 0);
lean_dec(v_unused_4400_);
v___x_4368_ = v___x_4366_;
v_isShared_4369_ = v_isSharedCheck_4399_;
goto v_resetjp_4367_;
}
else
{
lean_dec(v___x_4366_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4399_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4370_; lean_object* v___x_4371_; 
lean_inc(v_indName_4355_);
v___x_4370_ = l_Lean_mkCasesOnName(v_indName_4355_);
v___x_4371_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4370_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
if (lean_obj_tag(v___x_4371_) == 0)
{
lean_object* v_a_4372_; lean_object* v_levelParams_4373_; lean_object* v_type_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v_a_4372_ = lean_ctor_get(v___x_4371_, 0);
lean_inc(v_a_4372_);
lean_dec_ref_known(v___x_4371_, 1);
v_levelParams_4373_ = lean_ctor_get(v_a_4372_, 1);
lean_inc_n(v_levelParams_4373_, 2);
v_type_4374_ = lean_ctor_get(v_a_4372_, 2);
lean_inc_ref(v_type_4374_);
lean_dec(v_a_4372_);
v___x_4375_ = lean_box(0);
v___x_4376_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4373_, v___x_4375_);
if (lean_obj_tag(v___x_4376_) == 1)
{
lean_object* v_head_4377_; lean_object* v_tail_4378_; lean_object* v_numParams_4379_; lean_object* v_numIndices_4380_; lean_object* v_ctors_4381_; lean_object* v___x_4382_; lean_object* v___f_4383_; lean_object* v___x_4385_; 
v_head_4377_ = lean_ctor_get(v___x_4376_, 0);
lean_inc(v_head_4377_);
v_tail_4378_ = lean_ctor_get(v___x_4376_, 1);
lean_inc(v_tail_4378_);
v_numParams_4379_ = lean_ctor_get(v_val_4363_, 1);
lean_inc_n(v_numParams_4379_, 2);
v_numIndices_4380_ = lean_ctor_get(v_val_4363_, 2);
lean_inc(v_numIndices_4380_);
v_ctors_4381_ = lean_ctor_get(v_val_4363_, 4);
lean_inc(v_ctors_4381_);
v___x_4382_ = l_Lean_instInhabitedExpr;
v___f_4383_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4383_, 0, v___x_4382_);
lean_closure_set(v___f_4383_, 1, v_indName_4355_);
lean_closure_set(v___f_4383_, 2, v_tail_4378_);
lean_closure_set(v___f_4383_, 3, v_head_4377_);
lean_closure_set(v___f_4383_, 4, v_ctors_4381_);
lean_closure_set(v___f_4383_, 5, v_numIndices_4380_);
lean_closure_set(v___f_4383_, 6, v___x_4365_);
lean_closure_set(v___f_4383_, 7, v___x_4376_);
lean_closure_set(v___f_4383_, 8, v_val_4363_);
lean_closure_set(v___f_4383_, 9, v_declName_4354_);
lean_closure_set(v___f_4383_, 10, v_levelParams_4373_);
lean_closure_set(v___f_4383_, 11, v_numParams_4379_);
if (v_isShared_4369_ == 0)
{
lean_ctor_set_tag(v___x_4368_, 1);
lean_ctor_set(v___x_4368_, 0, v_numParams_4379_);
v___x_4385_ = v___x_4368_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_numParams_4379_);
v___x_4385_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
uint8_t v___x_4386_; lean_object* v___x_4387_; 
v___x_4386_ = 0;
v___x_4387_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4374_, v___x_4385_, v___f_4383_, v___x_4386_, v___x_4386_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
return v___x_4387_;
}
}
else
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
lean_dec(v___x_4376_);
lean_dec_ref(v_type_4374_);
lean_dec(v_levelParams_4373_);
lean_del_object(v___x_4368_);
lean_dec(v___x_4365_);
lean_dec_ref(v_val_4363_);
lean_dec(v_indName_4355_);
lean_dec(v_declName_4354_);
v___x_4389_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4390_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4389_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
return v___x_4390_;
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_del_object(v___x_4368_);
lean_dec(v___x_4365_);
lean_dec_ref(v_val_4363_);
lean_dec(v_indName_4355_);
lean_dec(v_declName_4354_);
v_a_4391_ = lean_ctor_get(v___x_4371_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4371_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4371_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4371_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
}
else
{
lean_dec(v___x_4365_);
lean_dec_ref(v_val_4363_);
lean_dec(v_indName_4355_);
lean_dec(v_declName_4354_);
return v___x_4366_;
}
}
else
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
lean_dec(v_a_4362_);
lean_dec(v_indName_4355_);
lean_dec(v_declName_4354_);
v___x_4401_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4402_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(v___x_4401_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
return v___x_4402_;
}
}
else
{
lean_object* v_a_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_indName_4355_);
lean_dec(v_declName_4354_);
v_a_4403_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4361_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_a_4403_);
lean_dec(v___x_4361_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_a_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4411_, lean_object* v_indName_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_, lean_object* v_a_4415_, lean_object* v_a_4416_, lean_object* v_a_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_Lean_mkCasesOnSameCtor(v_declName_4411_, v_indName_4412_, v_a_4413_, v_a_4414_, v_a_4415_, v_a_4416_);
lean_dec(v_a_4416_);
lean_dec_ref(v_a_4415_);
lean_dec(v_a_4414_);
lean_dec_ref(v_a_4413_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4419_, lean_object* v_params_4420_, lean_object* v_motive_4421_, lean_object* v_as_4422_, size_t v_sz_4423_, size_t v_i_4424_, lean_object* v_bs_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v___x_4431_; 
v___x_4431_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4419_, v_params_4420_, v_motive_4421_, v_sz_4423_, v_i_4424_, v_bs_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4432_, lean_object* v_params_4433_, lean_object* v_motive_4434_, lean_object* v_as_4435_, lean_object* v_sz_4436_, lean_object* v_i_4437_, lean_object* v_bs_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
size_t v_sz_boxed_4444_; size_t v_i_boxed_4445_; lean_object* v_res_4446_; 
v_sz_boxed_4444_ = lean_unbox_usize(v_sz_4436_);
lean_dec(v_sz_4436_);
v_i_boxed_4445_ = lean_unbox_usize(v_i_4437_);
lean_dec(v_i_4437_);
v_res_4446_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4432_, v_params_4433_, v_motive_4434_, v_as_4435_, v_sz_boxed_4444_, v_i_boxed_4445_, v_bs_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
lean_dec(v___y_4442_);
lean_dec_ref(v___y_4441_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec_ref(v_as_4435_);
lean_dec_ref(v_params_4433_);
return v_res_4446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4447_, lean_object* v_params_4448_, lean_object* v_a_4449_, lean_object* v_snd_4450_, lean_object* v_alts_4451_, lean_object* v_as_4452_, size_t v_sz_4453_, size_t v_i_4454_, lean_object* v_bs_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v___x_4461_; 
v___x_4461_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4447_, v_params_4448_, v_a_4449_, v_snd_4450_, v_alts_4451_, v_sz_4453_, v_i_4454_, v_bs_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
return v___x_4461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4462_, lean_object* v_params_4463_, lean_object* v_a_4464_, lean_object* v_snd_4465_, lean_object* v_alts_4466_, lean_object* v_as_4467_, lean_object* v_sz_4468_, lean_object* v_i_4469_, lean_object* v_bs_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
size_t v_sz_boxed_4476_; size_t v_i_boxed_4477_; lean_object* v_res_4478_; 
v_sz_boxed_4476_ = lean_unbox_usize(v_sz_4468_);
lean_dec(v_sz_4468_);
v_i_boxed_4477_ = lean_unbox_usize(v_i_4469_);
lean_dec(v_i_4469_);
v_res_4478_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4462_, v_params_4463_, v_a_4464_, v_snd_4465_, v_alts_4466_, v_as_4467_, v_sz_boxed_4476_, v_i_boxed_4477_, v_bs_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec_ref(v_as_4467_);
lean_dec_ref(v_params_4463_);
return v_res_4478_;
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
