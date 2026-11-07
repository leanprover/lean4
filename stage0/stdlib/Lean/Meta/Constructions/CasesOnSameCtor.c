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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Pi_instInhabited___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Match_Extension_addMatcherInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConstructorElimName(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
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
static const lean_closure_object l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___closed__0 = (const lean_object*)&l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4_value;
static const lean_closure_object l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5 = (const lean_object*)&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0 = (const lean_object*)&l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__4;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Cannot add attribute `["};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` to declaration `"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3;
static const lean_string_object l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "` because it is in an imported module"};
static const lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__4 = (const lean_object*)&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "` because it is not from the present async context"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1;
static const lean_string_object l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " `"};
static const lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__2 = (const lean_object*)&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(lean_object* v_msg_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___f_286_; lean_object* v___x_17131__overap_287_; lean_object* v___x_288_; 
v___f_286_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___closed__0));
v___x_17131__overap_287_ = lean_panic_fn_borrowed(v___f_286_, v_msg_280_);
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
v___x_288_ = lean_apply_5(v___x_17131__overap_287_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, lean_box(0));
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___boxed(lean_object* v_msg_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v_msg_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(lean_object* v_name_296_, lean_object* v_type_297_, lean_object* v_k_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
uint8_t v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; 
v___x_304_ = 0;
v___x_305_ = 0;
v___x_306_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_name_296_, v___x_304_, v_type_297_, v_k_298_, v___x_305_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(lean_object* v_name_307_, lean_object* v_type_308_, lean_object* v_k_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_307_, v_type_308_, v_k_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(lean_object* v___x_316_, lean_object* v_ism2_317_, lean_object* v_motive_318_, uint8_t v___x_319_, uint8_t v___x_320_, uint8_t v___x_321_, lean_object* v_a_322_, lean_object* v___f_323_, lean_object* v_zs1_324_, lean_object* v_val_325_, lean_object* v___x_326_, lean_object* v_indName_327_, lean_object* v_v_328_, lean_object* v___x_329_, lean_object* v_params_330_, lean_object* v___x_331_, lean_object* v_h_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_338_ = l_Array_append___redArg(v___x_316_, v_ism2_317_);
v___x_339_ = l_Lean_mkAppN(v_motive_318_, v___x_338_);
lean_dec_ref(v___x_338_);
v___x_340_ = l_Lean_Meta_mkLambdaFVars(v_ism2_317_, v___x_339_, v___x_319_, v___x_320_, v___x_319_, v___x_320_, v___x_321_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_340_, 1);
v___x_342_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_322_, v___f_323_, v___x_319_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___y_345_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_348_ = l_Lean_InductiveVal_numCtors(v_val_325_);
v___x_349_ = lean_nat_dec_eq(v___x_348_, v___x_326_);
lean_dec(v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v___x_331_);
v___x_350_ = l_Lean_mkConstructorElimName(v_indName_327_, v_v_328_);
v___x_351_ = l_Lean_mkConst(v___x_350_, v___x_329_);
v___x_352_ = lean_mk_empty_array_with_capacity(v___x_326_);
v___x_353_ = lean_array_push(v___x_352_, v_a_341_);
v___x_354_ = l_Array_append___redArg(v_params_330_, v___x_353_);
lean_dec_ref(v___x_353_);
v___x_355_ = l_Array_append___redArg(v___x_354_, v_ism2_317_);
v___x_356_ = lean_unsigned_to_nat(2u);
v___x_357_ = lean_mk_empty_array_with_capacity(v___x_356_);
lean_inc_ref(v_h_332_);
v___x_358_ = lean_array_push(v___x_357_, v_h_332_);
v___x_359_ = lean_array_push(v___x_358_, v_a_343_);
v___x_360_ = l_Array_append___redArg(v___x_355_, v___x_359_);
lean_dec_ref(v___x_359_);
v___x_361_ = l_Lean_mkAppN(v___x_351_, v___x_360_);
lean_dec_ref(v___x_360_);
v___y_345_ = v___x_361_;
goto v___jp_344_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v_v_328_);
lean_dec(v_indName_327_);
v___x_362_ = l_Lean_mkConst(v___x_331_, v___x_329_);
v___x_363_ = lean_mk_empty_array_with_capacity(v___x_326_);
lean_inc_ref(v___x_363_);
v___x_364_ = lean_array_push(v___x_363_, v_a_341_);
v___x_365_ = l_Array_append___redArg(v_params_330_, v___x_364_);
lean_dec_ref(v___x_364_);
v___x_366_ = l_Array_append___redArg(v___x_365_, v_ism2_317_);
v___x_367_ = lean_array_push(v___x_363_, v_a_343_);
v___x_368_ = l_Array_append___redArg(v___x_366_, v___x_367_);
lean_dec_ref(v___x_367_);
v___x_369_ = l_Lean_mkAppN(v___x_362_, v___x_368_);
lean_dec_ref(v___x_368_);
v___y_345_ = v___x_369_;
goto v___jp_344_;
}
v___jp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = lean_array_push(v_zs1_324_, v_h_332_);
v___x_347_ = l_Lean_Meta_mkLambdaFVars(v___x_346_, v___y_345_, v___x_319_, v___x_320_, v___x_319_, v___x_320_, v___x_321_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
lean_dec_ref(v___x_346_);
return v___x_347_;
}
}
else
{
lean_dec(v_a_341_);
lean_dec_ref(v_h_332_);
lean_dec(v___x_331_);
lean_dec_ref(v_params_330_);
lean_dec(v___x_329_);
lean_dec(v_v_328_);
lean_dec(v_indName_327_);
lean_dec_ref(v_zs1_324_);
return v___x_342_;
}
}
else
{
lean_dec_ref(v_h_332_);
lean_dec(v___x_331_);
lean_dec_ref(v_params_330_);
lean_dec(v___x_329_);
lean_dec(v_v_328_);
lean_dec(v_indName_327_);
lean_dec_ref(v_zs1_324_);
lean_dec_ref(v___f_323_);
lean_dec_ref(v_a_322_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_370_ = _args[0];
lean_object* v_ism2_371_ = _args[1];
lean_object* v_motive_372_ = _args[2];
lean_object* v___x_373_ = _args[3];
lean_object* v___x_374_ = _args[4];
lean_object* v___x_375_ = _args[5];
lean_object* v_a_376_ = _args[6];
lean_object* v___f_377_ = _args[7];
lean_object* v_zs1_378_ = _args[8];
lean_object* v_val_379_ = _args[9];
lean_object* v___x_380_ = _args[10];
lean_object* v_indName_381_ = _args[11];
lean_object* v_v_382_ = _args[12];
lean_object* v___x_383_ = _args[13];
lean_object* v_params_384_ = _args[14];
lean_object* v___x_385_ = _args[15];
lean_object* v_h_386_ = _args[16];
lean_object* v___y_387_ = _args[17];
lean_object* v___y_388_ = _args[18];
lean_object* v___y_389_ = _args[19];
lean_object* v___y_390_ = _args[20];
lean_object* v___y_391_ = _args[21];
_start:
{
uint8_t v___x_22098__boxed_392_; uint8_t v___x_22099__boxed_393_; uint8_t v___x_22100__boxed_394_; lean_object* v_res_395_; 
v___x_22098__boxed_392_ = lean_unbox(v___x_373_);
v___x_22099__boxed_393_ = lean_unbox(v___x_374_);
v___x_22100__boxed_394_ = lean_unbox(v___x_375_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_370_, v_ism2_371_, v_motive_372_, v___x_22098__boxed_392_, v___x_22099__boxed_393_, v___x_22100__boxed_394_, v_a_376_, v___f_377_, v_zs1_378_, v_val_379_, v___x_380_, v_indName_381_, v_v_382_, v___x_383_, v_params_384_, v___x_385_, v_h_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
lean_dec(v___x_380_);
lean_dec_ref(v_val_379_);
lean_dec_ref(v_ism2_371_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(lean_object* v___x_396_, lean_object* v_alts_397_, lean_object* v___x_398_, lean_object* v_zs1_399_, uint8_t v___x_400_, uint8_t v___x_401_, uint8_t v___x_402_, lean_object* v_zs2_403_, lean_object* v_x_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_410_ = lean_array_get_borrowed(v___x_396_, v_alts_397_, v___x_398_);
v___x_411_ = l_Array_append___redArg(v_zs1_399_, v_zs2_403_);
lean_inc(v___x_410_);
v___x_412_ = l_Lean_mkAppN(v___x_410_, v___x_411_);
lean_dec_ref(v___x_411_);
v___x_413_ = l_Lean_Meta_mkLambdaFVars(v_zs2_403_, v___x_412_, v___x_400_, v___x_401_, v___x_400_, v___x_401_, v___x_402_, v___y_405_, v___y_406_, v___y_407_, v___y_408_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(lean_object* v___x_414_, lean_object* v_alts_415_, lean_object* v___x_416_, lean_object* v_zs1_417_, lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v___x_420_, lean_object* v_zs2_421_, lean_object* v_x_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
uint8_t v___x_22210__boxed_428_; uint8_t v___x_22211__boxed_429_; uint8_t v___x_22212__boxed_430_; lean_object* v_res_431_; 
v___x_22210__boxed_428_ = lean_unbox(v___x_418_);
v___x_22211__boxed_429_ = lean_unbox(v___x_419_);
v___x_22212__boxed_430_ = lean_unbox(v___x_420_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_414_, v_alts_415_, v___x_416_, v_zs1_417_, v___x_22210__boxed_428_, v___x_22211__boxed_429_, v___x_22212__boxed_430_, v_zs2_421_, v_x_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec_ref(v_x_422_);
lean_dec_ref(v_zs2_421_);
lean_dec(v___x_416_);
lean_dec_ref(v_alts_415_);
lean_dec_ref(v___x_414_);
return v_res_431_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0(void){
_start:
{
lean_object* v___x_432_; lean_object* v_dummy_433_; 
v___x_432_ = lean_box(0);
v_dummy_433_ = l_Lean_Expr_sort___override(v___x_432_);
return v_dummy_433_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_box(0);
v___x_441_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4));
v___x_442_ = l_Lean_mkConst(v___x_441_, v___x_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(lean_object* v___x_443_, lean_object* v_alts_444_, lean_object* v___x_445_, uint8_t v___x_446_, uint8_t v___x_447_, uint8_t v___x_448_, lean_object* v___x_449_, lean_object* v___x_450_, lean_object* v___x_451_, lean_object* v_ism2_452_, lean_object* v_motive_453_, lean_object* v_a_454_, lean_object* v_val_455_, lean_object* v_indName_456_, lean_object* v_v_457_, lean_object* v___x_458_, lean_object* v_params_459_, lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v___x_462_, lean_object* v_zs1_463_, lean_object* v_ctorRet1_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___f_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_470_ = lean_box(v___x_446_);
v___x_471_ = lean_box(v___x_447_);
v___x_472_ = lean_box(v___x_448_);
lean_inc_ref(v_zs1_463_);
lean_inc(v___x_445_);
v___f_473_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed), 14, 7);
lean_closure_set(v___f_473_, 0, v___x_443_);
lean_closure_set(v___f_473_, 1, v_alts_444_);
lean_closure_set(v___f_473_, 2, v___x_445_);
lean_closure_set(v___f_473_, 3, v_zs1_463_);
lean_closure_set(v___f_473_, 4, v___x_470_);
lean_closure_set(v___f_473_, 5, v___x_471_);
lean_closure_set(v___f_473_, 6, v___x_472_);
v___x_474_ = l_Lean_mkAppN(v___x_449_, v_zs1_463_);
lean_inc(v___y_468_);
lean_inc_ref(v___y_467_);
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
v___x_475_ = lean_whnf(v_ctorRet1_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v_dummy_477_; lean_object* v_nargs_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___f_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v___x_475_, 1);
v_dummy_477_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_478_ = l_Lean_Expr_getAppNumArgs(v_a_476_);
lean_inc(v_nargs_478_);
v___x_479_ = lean_mk_array(v_nargs_478_, v_dummy_477_);
v___x_480_ = lean_nat_sub(v_nargs_478_, v___x_450_);
lean_dec(v_nargs_478_);
v___x_481_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_476_, v___x_479_, v___x_480_);
v___x_482_ = lean_array_get_size(v___x_481_);
v___x_483_ = l_Array_toSubarray___redArg(v___x_481_, v___x_451_, v___x_482_);
v___x_484_ = l_Subarray_copy___redArg(v___x_483_);
v___x_485_ = lean_array_push(v___x_484_, v___x_474_);
v___x_486_ = lean_box(v___x_446_);
v___x_487_ = lean_box(v___x_447_);
v___x_488_ = lean_box(v___x_448_);
lean_inc(v___x_450_);
v___f_489_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed), 22, 16);
lean_closure_set(v___f_489_, 0, v___x_485_);
lean_closure_set(v___f_489_, 1, v_ism2_452_);
lean_closure_set(v___f_489_, 2, v_motive_453_);
lean_closure_set(v___f_489_, 3, v___x_486_);
lean_closure_set(v___f_489_, 4, v___x_487_);
lean_closure_set(v___f_489_, 5, v___x_488_);
lean_closure_set(v___f_489_, 6, v_a_454_);
lean_closure_set(v___f_489_, 7, v___f_473_);
lean_closure_set(v___f_489_, 8, v_zs1_463_);
lean_closure_set(v___f_489_, 9, v_val_455_);
lean_closure_set(v___f_489_, 10, v___x_450_);
lean_closure_set(v___f_489_, 11, v_indName_456_);
lean_closure_set(v___f_489_, 12, v_v_457_);
lean_closure_set(v___f_489_, 13, v___x_458_);
lean_closure_set(v___f_489_, 14, v_params_459_);
lean_closure_set(v___f_489_, 15, v___x_460_);
v___x_490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2));
v___x_491_ = l_Lean_Level_ofNat(v___x_450_);
lean_dec(v___x_450_);
v___x_492_ = lean_box(0);
v___x_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = l_Lean_mkConst(v___x_490_, v___x_493_);
v___x_495_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
v___x_496_ = l_Lean_mkRawNatLit(v___x_445_);
v___x_497_ = l_Lean_mkApp3(v___x_494_, v___x_495_, v___x_461_, v___x_496_);
v___x_498_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_462_, v___x_497_, v___f_489_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_498_;
}
else
{
lean_dec_ref(v___x_474_);
lean_dec_ref(v___f_473_);
lean_dec_ref(v_zs1_463_);
lean_dec(v___x_462_);
lean_dec_ref(v___x_461_);
lean_dec(v___x_460_);
lean_dec_ref(v_params_459_);
lean_dec(v___x_458_);
lean_dec(v_v_457_);
lean_dec(v_indName_456_);
lean_dec_ref(v_val_455_);
lean_dec_ref(v_a_454_);
lean_dec_ref(v_motive_453_);
lean_dec_ref(v_ism2_452_);
lean_dec(v___x_451_);
lean_dec(v___x_450_);
lean_dec(v___x_445_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(lean_object** _args){
lean_object* v___x_499_ = _args[0];
lean_object* v_alts_500_ = _args[1];
lean_object* v___x_501_ = _args[2];
lean_object* v___x_502_ = _args[3];
lean_object* v___x_503_ = _args[4];
lean_object* v___x_504_ = _args[5];
lean_object* v___x_505_ = _args[6];
lean_object* v___x_506_ = _args[7];
lean_object* v___x_507_ = _args[8];
lean_object* v_ism2_508_ = _args[9];
lean_object* v_motive_509_ = _args[10];
lean_object* v_a_510_ = _args[11];
lean_object* v_val_511_ = _args[12];
lean_object* v_indName_512_ = _args[13];
lean_object* v_v_513_ = _args[14];
lean_object* v___x_514_ = _args[15];
lean_object* v_params_515_ = _args[16];
lean_object* v___x_516_ = _args[17];
lean_object* v___x_517_ = _args[18];
lean_object* v___x_518_ = _args[19];
lean_object* v_zs1_519_ = _args[20];
lean_object* v_ctorRet1_520_ = _args[21];
lean_object* v___y_521_ = _args[22];
lean_object* v___y_522_ = _args[23];
lean_object* v___y_523_ = _args[24];
lean_object* v___y_524_ = _args[25];
lean_object* v___y_525_ = _args[26];
_start:
{
uint8_t v___x_22271__boxed_526_; uint8_t v___x_22272__boxed_527_; uint8_t v___x_22273__boxed_528_; lean_object* v_res_529_; 
v___x_22271__boxed_526_ = lean_unbox(v___x_502_);
v___x_22272__boxed_527_ = lean_unbox(v___x_503_);
v___x_22273__boxed_528_ = lean_unbox(v___x_504_);
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_499_, v_alts_500_, v___x_501_, v___x_22271__boxed_526_, v___x_22272__boxed_527_, v___x_22273__boxed_528_, v___x_505_, v___x_506_, v___x_507_, v_ism2_508_, v_motive_509_, v_a_510_, v_val_511_, v_indName_512_, v_v_513_, v___x_514_, v_params_515_, v___x_516_, v___x_517_, v___x_518_, v_zs1_519_, v_ctorRet1_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(lean_object* v_tail_533_, lean_object* v_params_534_, lean_object* v_alts_535_, lean_object* v___x_536_, lean_object* v_ism2_537_, lean_object* v_motive_538_, lean_object* v_val_539_, lean_object* v_indName_540_, lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v___x_543_, size_t v_sz_544_, size_t v_i_545_, lean_object* v_bs_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
uint8_t v___x_552_; 
v___x_552_ = lean_usize_dec_lt(v_i_545_, v_sz_544_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_dec_ref(v___x_543_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
lean_dec(v_indName_540_);
lean_dec_ref(v_val_539_);
lean_dec_ref(v_motive_538_);
lean_dec_ref(v_ism2_537_);
lean_dec(v___x_536_);
lean_dec_ref(v_alts_535_);
lean_dec_ref(v_params_534_);
lean_dec(v_tail_533_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v_bs_546_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; uint8_t v___x_555_; uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v_v_559_; lean_object* v___x_560_; lean_object* v_bs_x27_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_554_ = l_Lean_instInhabitedExpr;
v___x_555_ = 0;
v___x_556_ = 1;
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v_v_559_ = lean_array_uget(v_bs_546_, v_i_545_);
v___x_560_ = lean_unsigned_to_nat(0u);
v_bs_x27_561_ = lean_array_uset(v_bs_546_, v_i_545_, v___x_560_);
v___x_562_ = lean_usize_to_nat(v_i_545_);
lean_inc(v_tail_533_);
lean_inc(v_v_559_);
v___x_563_ = l_Lean_mkConst(v_v_559_, v_tail_533_);
v___x_564_ = l_Lean_mkAppN(v___x_563_, v_params_534_);
lean_inc(v___y_550_);
lean_inc_ref(v___y_549_);
lean_inc(v___y_548_);
lean_inc_ref(v___y_547_);
lean_inc_ref(v___x_564_);
v___x_565_ = lean_infer_type(v___x_564_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v___x_571_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc_n(v_a_566_, 2);
lean_dec_ref_known(v___x_565_, 1);
v___x_567_ = lean_box(v___x_555_);
v___x_568_ = lean_box(v___x_552_);
v___x_569_ = lean_box(v___x_556_);
lean_inc_ref(v___x_543_);
lean_inc(v___x_542_);
lean_inc_ref(v_params_534_);
lean_inc(v___x_541_);
lean_inc(v_indName_540_);
lean_inc_ref(v_val_539_);
lean_inc_ref(v_motive_538_);
lean_inc_ref(v_ism2_537_);
lean_inc(v___x_536_);
lean_inc_ref(v_alts_535_);
v___f_570_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed), 27, 20);
lean_closure_set(v___f_570_, 0, v___x_554_);
lean_closure_set(v___f_570_, 1, v_alts_535_);
lean_closure_set(v___f_570_, 2, v___x_562_);
lean_closure_set(v___f_570_, 3, v___x_567_);
lean_closure_set(v___f_570_, 4, v___x_568_);
lean_closure_set(v___f_570_, 5, v___x_569_);
lean_closure_set(v___f_570_, 6, v___x_564_);
lean_closure_set(v___f_570_, 7, v___x_557_);
lean_closure_set(v___f_570_, 8, v___x_536_);
lean_closure_set(v___f_570_, 9, v_ism2_537_);
lean_closure_set(v___f_570_, 10, v_motive_538_);
lean_closure_set(v___f_570_, 11, v_a_566_);
lean_closure_set(v___f_570_, 12, v_val_539_);
lean_closure_set(v___f_570_, 13, v_indName_540_);
lean_closure_set(v___f_570_, 14, v_v_559_);
lean_closure_set(v___f_570_, 15, v___x_541_);
lean_closure_set(v___f_570_, 16, v_params_534_);
lean_closure_set(v___f_570_, 17, v___x_542_);
lean_closure_set(v___f_570_, 18, v___x_543_);
lean_closure_set(v___f_570_, 19, v___x_558_);
v___x_571_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_566_, v___f_570_, v___x_555_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
if (lean_obj_tag(v___x_571_) == 0)
{
lean_object* v_a_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; 
v_a_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_a_572_);
lean_dec_ref_known(v___x_571_, 1);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_545_, v___x_573_);
v___x_575_ = lean_array_uset(v_bs_x27_561_, v_i_545_, v_a_572_);
v_i_545_ = v___x_574_;
v_bs_546_ = v___x_575_;
goto _start;
}
else
{
lean_object* v_a_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_584_; 
lean_dec_ref(v_bs_x27_561_);
lean_dec_ref(v___x_543_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
lean_dec(v_indName_540_);
lean_dec_ref(v_val_539_);
lean_dec_ref(v_motive_538_);
lean_dec_ref(v_ism2_537_);
lean_dec(v___x_536_);
lean_dec_ref(v_alts_535_);
lean_dec_ref(v_params_534_);
lean_dec(v_tail_533_);
v_a_577_ = lean_ctor_get(v___x_571_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_584_ == 0)
{
v___x_579_ = v___x_571_;
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_a_577_);
lean_dec(v___x_571_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_584_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_582_; 
if (v_isShared_580_ == 0)
{
v___x_582_ = v___x_579_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v_a_577_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
else
{
lean_object* v_a_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref(v___x_564_);
lean_dec(v___x_562_);
lean_dec_ref(v_bs_x27_561_);
lean_dec(v_v_559_);
lean_dec_ref(v___x_543_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
lean_dec(v_indName_540_);
lean_dec_ref(v_val_539_);
lean_dec_ref(v_motive_538_);
lean_dec_ref(v_ism2_537_);
lean_dec(v___x_536_);
lean_dec_ref(v_alts_535_);
lean_dec_ref(v_params_534_);
lean_dec(v_tail_533_);
v_a_585_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_592_ == 0)
{
v___x_587_ = v___x_565_;
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_a_585_);
lean_dec(v___x_565_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_592_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_590_; 
if (v_isShared_588_ == 0)
{
v___x_590_ = v___x_587_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_a_585_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(lean_object** _args){
lean_object* v_tail_593_ = _args[0];
lean_object* v_params_594_ = _args[1];
lean_object* v_alts_595_ = _args[2];
lean_object* v___x_596_ = _args[3];
lean_object* v_ism2_597_ = _args[4];
lean_object* v_motive_598_ = _args[5];
lean_object* v_val_599_ = _args[6];
lean_object* v_indName_600_ = _args[7];
lean_object* v___x_601_ = _args[8];
lean_object* v___x_602_ = _args[9];
lean_object* v___x_603_ = _args[10];
lean_object* v_sz_604_ = _args[11];
lean_object* v_i_605_ = _args[12];
lean_object* v_bs_606_ = _args[13];
lean_object* v___y_607_ = _args[14];
lean_object* v___y_608_ = _args[15];
lean_object* v___y_609_ = _args[16];
lean_object* v___y_610_ = _args[17];
lean_object* v___y_611_ = _args[18];
_start:
{
size_t v_sz_boxed_612_; size_t v_i_boxed_613_; lean_object* v_res_614_; 
v_sz_boxed_612_ = lean_unbox_usize(v_sz_604_);
lean_dec(v_sz_604_);
v_i_boxed_613_ = lean_unbox_usize(v_i_605_);
lean_dec(v_i_605_);
v_res_614_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_593_, v_params_594_, v_alts_595_, v___x_596_, v_ism2_597_, v_motive_598_, v_val_599_, v_indName_600_, v___x_601_, v___x_602_, v___x_603_, v_sz_boxed_612_, v_i_boxed_613_, v_bs_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0(lean_object* v_motive_615_, lean_object* v___x_616_, lean_object* v_a_617_, lean_object* v_ism1_618_, uint8_t v___x_619_, uint8_t v___x_620_, uint8_t v___x_621_, lean_object* v_name_622_, lean_object* v___x_623_, lean_object* v_params_624_, lean_object* v___x_625_, lean_object* v_tail_626_, lean_object* v_alts_627_, lean_object* v_numParams_628_, lean_object* v_ism2_629_, lean_object* v_val_630_, lean_object* v_indName_631_, lean_object* v___x_632_, lean_object* v___x_633_, lean_object* v___x_634_, lean_object* v_heq_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
lean_inc_ref(v_motive_615_);
v___x_641_ = l_Lean_mkAppN(v_motive_615_, v___x_616_);
v___x_642_ = l_Lean_mkArrow(v_a_617_, v___x_641_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v___x_644_ = l_Lean_Meta_mkLambdaFVars(v_ism1_618_, v_a_643_, v___x_619_, v___x_620_, v___x_619_, v___x_620_, v___x_621_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v_a_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; size_t v_sz_650_; size_t v___x_651_; lean_object* v___x_652_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v___x_644_, 1);
lean_inc(v___x_623_);
v___x_646_ = l_Lean_mkConst(v_name_622_, v___x_623_);
v___x_647_ = l_Lean_mkAppN(v___x_646_, v_params_624_);
v___x_648_ = l_Lean_Expr_app___override(v___x_647_, v_a_645_);
v___x_649_ = l_Lean_mkAppN(v___x_648_, v_ism1_618_);
v_sz_650_ = lean_array_size(v___x_625_);
v___x_651_ = ((size_t)0ULL);
lean_inc_ref(v_motive_615_);
lean_inc_ref(v_ism2_629_);
lean_inc_ref(v_alts_627_);
lean_inc_ref(v_params_624_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_626_, v_params_624_, v_alts_627_, v_numParams_628_, v_ism2_629_, v_motive_615_, v_val_630_, v_indName_631_, v___x_623_, v___x_632_, v___x_633_, v_sz_650_, v___x_651_, v___x_625_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v___x_652_, 1);
v___x_654_ = l_Lean_mkAppN(v___x_649_, v_a_653_);
lean_dec(v_a_653_);
lean_inc_ref(v_heq_635_);
v___x_655_ = l_Lean_Meta_mkEqSymm(v_heq_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_a_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v___x_655_, 1);
v___x_657_ = l_Lean_Expr_app___override(v___x_654_, v_a_656_);
v___x_658_ = lean_mk_empty_array_with_capacity(v___x_634_);
lean_inc_ref(v___x_658_);
v___x_659_ = lean_array_push(v___x_658_, v_motive_615_);
v___x_660_ = l_Array_append___redArg(v_params_624_, v___x_659_);
lean_dec_ref(v___x_659_);
v___x_661_ = l_Array_append___redArg(v___x_660_, v_ism1_618_);
v___x_662_ = l_Array_append___redArg(v___x_661_, v_ism2_629_);
lean_dec_ref(v_ism2_629_);
v___x_663_ = lean_array_push(v___x_658_, v_heq_635_);
v___x_664_ = l_Array_append___redArg(v___x_662_, v___x_663_);
lean_dec_ref(v___x_663_);
v___x_665_ = l_Array_append___redArg(v___x_664_, v_alts_627_);
lean_dec_ref(v_alts_627_);
v___x_666_ = l_Lean_Meta_mkLambdaFVars(v___x_665_, v___x_657_, v___x_619_, v___x_620_, v___x_619_, v___x_620_, v___x_621_, v___y_636_, v___y_637_, v___y_638_, v___y_639_);
lean_dec_ref(v___x_665_);
return v___x_666_;
}
else
{
lean_dec_ref(v___x_654_);
lean_dec_ref(v_heq_635_);
lean_dec_ref(v_ism2_629_);
lean_dec_ref(v_alts_627_);
lean_dec_ref(v_params_624_);
lean_dec_ref(v_motive_615_);
return v___x_655_;
}
}
else
{
lean_object* v_a_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_674_; 
lean_dec_ref(v___x_649_);
lean_dec_ref(v_heq_635_);
lean_dec_ref(v_ism2_629_);
lean_dec_ref(v_alts_627_);
lean_dec_ref(v_params_624_);
lean_dec_ref(v_motive_615_);
v_a_667_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_674_ == 0)
{
v___x_669_ = v___x_652_;
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_a_667_);
lean_dec(v___x_652_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_674_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_672_; 
if (v_isShared_670_ == 0)
{
v___x_672_ = v___x_669_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v_a_667_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
}
else
{
lean_dec_ref(v_heq_635_);
lean_dec_ref(v___x_633_);
lean_dec(v___x_632_);
lean_dec(v_indName_631_);
lean_dec_ref(v_val_630_);
lean_dec_ref(v_ism2_629_);
lean_dec(v_numParams_628_);
lean_dec_ref(v_alts_627_);
lean_dec(v_tail_626_);
lean_dec_ref(v___x_625_);
lean_dec_ref(v_params_624_);
lean_dec(v___x_623_);
lean_dec(v_name_622_);
lean_dec_ref(v_motive_615_);
return v___x_644_;
}
}
else
{
lean_dec_ref(v_heq_635_);
lean_dec_ref(v___x_633_);
lean_dec(v___x_632_);
lean_dec(v_indName_631_);
lean_dec_ref(v_val_630_);
lean_dec_ref(v_ism2_629_);
lean_dec(v_numParams_628_);
lean_dec_ref(v_alts_627_);
lean_dec(v_tail_626_);
lean_dec_ref(v___x_625_);
lean_dec_ref(v_params_624_);
lean_dec(v___x_623_);
lean_dec(v_name_622_);
lean_dec_ref(v_motive_615_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(lean_object** _args){
lean_object* v_motive_675_ = _args[0];
lean_object* v___x_676_ = _args[1];
lean_object* v_a_677_ = _args[2];
lean_object* v_ism1_678_ = _args[3];
lean_object* v___x_679_ = _args[4];
lean_object* v___x_680_ = _args[5];
lean_object* v___x_681_ = _args[6];
lean_object* v_name_682_ = _args[7];
lean_object* v___x_683_ = _args[8];
lean_object* v_params_684_ = _args[9];
lean_object* v___x_685_ = _args[10];
lean_object* v_tail_686_ = _args[11];
lean_object* v_alts_687_ = _args[12];
lean_object* v_numParams_688_ = _args[13];
lean_object* v_ism2_689_ = _args[14];
lean_object* v_val_690_ = _args[15];
lean_object* v_indName_691_ = _args[16];
lean_object* v___x_692_ = _args[17];
lean_object* v___x_693_ = _args[18];
lean_object* v___x_694_ = _args[19];
lean_object* v_heq_695_ = _args[20];
lean_object* v___y_696_ = _args[21];
lean_object* v___y_697_ = _args[22];
lean_object* v___y_698_ = _args[23];
lean_object* v___y_699_ = _args[24];
lean_object* v___y_700_ = _args[25];
_start:
{
uint8_t v___x_22513__boxed_701_; uint8_t v___x_22514__boxed_702_; uint8_t v___x_22515__boxed_703_; lean_object* v_res_704_; 
v___x_22513__boxed_701_ = lean_unbox(v___x_679_);
v___x_22514__boxed_702_ = lean_unbox(v___x_680_);
v___x_22515__boxed_703_ = lean_unbox(v___x_681_);
v_res_704_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_675_, v___x_676_, v_a_677_, v_ism1_678_, v___x_22513__boxed_701_, v___x_22514__boxed_702_, v___x_22515__boxed_703_, v_name_682_, v___x_683_, v_params_684_, v___x_685_, v_tail_686_, v_alts_687_, v_numParams_688_, v_ism2_689_, v_val_690_, v_indName_691_, v___x_692_, v___x_693_, v___x_694_, v_heq_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___x_694_);
lean_dec_ref(v_ism1_678_);
lean_dec_ref(v___x_676_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1(lean_object* v_indName_705_, lean_object* v_tail_706_, lean_object* v_params_707_, lean_object* v_ism1_708_, lean_object* v_ism2_709_, lean_object* v_motive_710_, lean_object* v___x_711_, uint8_t v___x_712_, uint8_t v___x_713_, uint8_t v___x_714_, lean_object* v_name_715_, lean_object* v___x_716_, lean_object* v___x_717_, lean_object* v_numParams_718_, lean_object* v_val_719_, lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v_alts_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
lean_inc(v_indName_705_);
v___x_728_ = l_Lean_mkCtorIdxName(v_indName_705_);
lean_inc(v_tail_706_);
v___x_729_ = l_Lean_mkConst(v___x_728_, v_tail_706_);
lean_inc_ref_n(v_params_707_, 2);
v___x_730_ = l_Array_append___redArg(v_params_707_, v_ism1_708_);
lean_inc_ref(v___x_729_);
v___x_731_ = l_Lean_mkAppN(v___x_729_, v___x_730_);
lean_dec_ref(v___x_730_);
v___x_732_ = l_Array_append___redArg(v_params_707_, v_ism2_709_);
v___x_733_ = l_Lean_mkAppN(v___x_729_, v___x_732_);
lean_dec_ref(v___x_732_);
lean_inc_ref(v___x_733_);
lean_inc_ref(v___x_731_);
v___x_734_ = l_Lean_Meta_mkEq(v___x_731_, v___x_733_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_736_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
lean_inc(v_a_735_);
lean_dec_ref_known(v___x_734_, 1);
lean_inc_ref(v___x_733_);
v___x_736_ = l_Lean_Meta_mkEq(v___x_733_, v___x_731_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___f_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = lean_box(v___x_712_);
v___x_739_ = lean_box(v___x_713_);
v___x_740_ = lean_box(v___x_714_);
v___f_741_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__0___boxed), 26, 20);
lean_closure_set(v___f_741_, 0, v_motive_710_);
lean_closure_set(v___f_741_, 1, v___x_711_);
lean_closure_set(v___f_741_, 2, v_a_737_);
lean_closure_set(v___f_741_, 3, v_ism1_708_);
lean_closure_set(v___f_741_, 4, v___x_738_);
lean_closure_set(v___f_741_, 5, v___x_739_);
lean_closure_set(v___f_741_, 6, v___x_740_);
lean_closure_set(v___f_741_, 7, v_name_715_);
lean_closure_set(v___f_741_, 8, v___x_716_);
lean_closure_set(v___f_741_, 9, v_params_707_);
lean_closure_set(v___f_741_, 10, v___x_717_);
lean_closure_set(v___f_741_, 11, v_tail_706_);
lean_closure_set(v___f_741_, 12, v_alts_722_);
lean_closure_set(v___f_741_, 13, v_numParams_718_);
lean_closure_set(v___f_741_, 14, v_ism2_709_);
lean_closure_set(v___f_741_, 15, v_val_719_);
lean_closure_set(v___f_741_, 16, v_indName_705_);
lean_closure_set(v___f_741_, 17, v___x_720_);
lean_closure_set(v___f_741_, 18, v___x_733_);
lean_closure_set(v___f_741_, 19, v___x_721_);
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_743_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_742_, v_a_735_, v___f_741_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
return v___x_743_;
}
else
{
lean_dec(v_a_735_);
lean_dec_ref(v___x_733_);
lean_dec_ref(v_alts_722_);
lean_dec(v___x_721_);
lean_dec(v___x_720_);
lean_dec_ref(v_val_719_);
lean_dec(v_numParams_718_);
lean_dec_ref(v___x_717_);
lean_dec(v___x_716_);
lean_dec(v_name_715_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v_motive_710_);
lean_dec_ref(v_ism2_709_);
lean_dec_ref(v_ism1_708_);
lean_dec_ref(v_params_707_);
lean_dec(v_tail_706_);
lean_dec(v_indName_705_);
return v___x_736_;
}
}
else
{
lean_dec_ref(v___x_733_);
lean_dec_ref(v___x_731_);
lean_dec_ref(v_alts_722_);
lean_dec(v___x_721_);
lean_dec(v___x_720_);
lean_dec_ref(v_val_719_);
lean_dec(v_numParams_718_);
lean_dec_ref(v___x_717_);
lean_dec(v___x_716_);
lean_dec(v_name_715_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v_motive_710_);
lean_dec_ref(v_ism2_709_);
lean_dec_ref(v_ism1_708_);
lean_dec_ref(v_params_707_);
lean_dec(v_tail_706_);
lean_dec(v_indName_705_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(lean_object** _args){
lean_object* v_indName_744_ = _args[0];
lean_object* v_tail_745_ = _args[1];
lean_object* v_params_746_ = _args[2];
lean_object* v_ism1_747_ = _args[3];
lean_object* v_ism2_748_ = _args[4];
lean_object* v_motive_749_ = _args[5];
lean_object* v___x_750_ = _args[6];
lean_object* v___x_751_ = _args[7];
lean_object* v___x_752_ = _args[8];
lean_object* v___x_753_ = _args[9];
lean_object* v_name_754_ = _args[10];
lean_object* v___x_755_ = _args[11];
lean_object* v___x_756_ = _args[12];
lean_object* v_numParams_757_ = _args[13];
lean_object* v_val_758_ = _args[14];
lean_object* v___x_759_ = _args[15];
lean_object* v___x_760_ = _args[16];
lean_object* v_alts_761_ = _args[17];
lean_object* v___y_762_ = _args[18];
lean_object* v___y_763_ = _args[19];
lean_object* v___y_764_ = _args[20];
lean_object* v___y_765_ = _args[21];
lean_object* v___y_766_ = _args[22];
_start:
{
uint8_t v___x_22636__boxed_767_; uint8_t v___x_22637__boxed_768_; uint8_t v___x_22638__boxed_769_; lean_object* v_res_770_; 
v___x_22636__boxed_767_ = lean_unbox(v___x_751_);
v___x_22637__boxed_768_ = lean_unbox(v___x_752_);
v___x_22638__boxed_769_ = lean_unbox(v___x_753_);
v_res_770_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_744_, v_tail_745_, v_params_746_, v_ism1_747_, v_ism2_748_, v_motive_749_, v___x_750_, v___x_22636__boxed_767_, v___x_22637__boxed_768_, v___x_22638__boxed_769_, v_name_754_, v___x_755_, v___x_756_, v_numParams_757_, v_val_758_, v___x_759_, v___x_760_, v_alts_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
lean_dec(v___y_765_);
lean_dec_ref(v___y_764_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(lean_object* v_snd_771_, lean_object* v_x_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v_snd_771_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(lean_object* v_snd_779_, lean_object* v_x_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_779_, v_x_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec_ref(v_x_780_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(size_t v_sz_787_, size_t v_i_788_, lean_object* v_bs_789_){
_start:
{
uint8_t v___x_790_; 
v___x_790_ = lean_usize_dec_lt(v_i_788_, v_sz_787_);
if (v___x_790_ == 0)
{
return v_bs_789_;
}
else
{
lean_object* v_v_791_; lean_object* v_fst_792_; lean_object* v_snd_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_807_; 
v_v_791_ = lean_array_uget(v_bs_789_, v_i_788_);
v_fst_792_ = lean_ctor_get(v_v_791_, 0);
v_snd_793_ = lean_ctor_get(v_v_791_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_v_791_);
if (v_isSharedCheck_807_ == 0)
{
v___x_795_ = v_v_791_;
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snd_793_);
lean_inc(v_fst_792_);
lean_dec(v_v_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_807_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v_bs_x27_798_; lean_object* v___f_799_; lean_object* v___x_801_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v_bs_x27_798_ = lean_array_uset(v_bs_789_, v_i_788_, v___x_797_);
v___f_799_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed), 7, 1);
lean_closure_set(v___f_799_, 0, v_snd_793_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 1, v___f_799_);
v___x_801_ = v___x_795_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_fst_792_);
lean_ctor_set(v_reuseFailAlloc_806_, 1, v___f_799_);
v___x_801_ = v_reuseFailAlloc_806_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_788_, v___x_802_);
v___x_804_ = lean_array_uset(v_bs_x27_798_, v_i_788_, v___x_801_);
v_i_788_ = v___x_803_;
v_bs_789_ = v___x_804_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(lean_object* v_sz_808_, lean_object* v_i_809_, lean_object* v_bs_810_){
_start:
{
size_t v_sz_boxed_811_; size_t v_i_boxed_812_; lean_object* v_res_813_; 
v_sz_boxed_811_ = lean_unbox_usize(v_sz_808_);
lean_dec(v_sz_808_);
v_i_boxed_812_ = lean_unbox_usize(v_i_809_);
lean_dec(v_i_809_);
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_811_, v_i_boxed_812_, v_bs_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0(lean_object* v___x_814_, lean_object* v___x_815_, lean_object* v_a_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_21755__overap_822_; lean_object* v___x_823_; 
v___x_21755__overap_822_ = l_instInhabitedOfMonad___redArg(v___x_814_, v___x_815_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
v___x_823_ = lean_apply_5(v___x_21755__overap_822_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, lean_box(0));
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0___boxed(lean_object* v___x_824_, lean_object* v___x_825_, lean_object* v_a_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0(v___x_824_, v___x_825_, v_a_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec_ref(v_a_826_);
return v_res_832_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0(void){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_instMonadEIO___redArg();
return v___x_833_;
}
}
static lean_object* _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__0);
v___x_835_ = l_StateRefT_x27_instMonad___redArg(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1___boxed(lean_object* v_acc_840_, lean_object* v_declInfos_841_, lean_object* v_k_842_, lean_object* v_kind_843_, lean_object* v_x_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
uint8_t v_kind_boxed_850_; lean_object* v_res_851_; 
v_kind_boxed_850_ = lean_unbox(v_kind_843_);
v_res_851_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1(v_acc_840_, v_declInfos_841_, v_k_842_, v_kind_boxed_850_, v_x_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23(lean_object* v_declInfos_852_, lean_object* v_k_853_, uint8_t v_kind_854_, lean_object* v_acc_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; lean_object* v_toApplicative_862_; lean_object* v_toFunctor_863_; lean_object* v_toSeq_864_; lean_object* v_toSeqLeft_865_; lean_object* v_toSeqRight_866_; lean_object* v___f_867_; lean_object* v___f_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___x_871_; lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___f_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v_toApplicative_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_928_; 
v___x_861_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1);
v_toApplicative_862_ = lean_ctor_get(v___x_861_, 0);
v_toFunctor_863_ = lean_ctor_get(v_toApplicative_862_, 0);
v_toSeq_864_ = lean_ctor_get(v_toApplicative_862_, 2);
v_toSeqLeft_865_ = lean_ctor_get(v_toApplicative_862_, 3);
v_toSeqRight_866_ = lean_ctor_get(v_toApplicative_862_, 4);
v___f_867_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2));
v___f_868_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3));
lean_inc_ref_n(v_toFunctor_863_, 2);
v___f_869_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_869_, 0, v_toFunctor_863_);
v___f_870_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_870_, 0, v_toFunctor_863_);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___f_869_);
lean_ctor_set(v___x_871_, 1, v___f_870_);
lean_inc(v_toSeqRight_866_);
v___f_872_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_872_, 0, v_toSeqRight_866_);
lean_inc(v_toSeqLeft_865_);
v___f_873_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_873_, 0, v_toSeqLeft_865_);
lean_inc(v_toSeq_864_);
v___f_874_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_874_, 0, v_toSeq_864_);
v___x_875_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_875_, 0, v___x_871_);
lean_ctor_set(v___x_875_, 1, v___f_867_);
lean_ctor_set(v___x_875_, 2, v___f_874_);
lean_ctor_set(v___x_875_, 3, v___f_873_);
lean_ctor_set(v___x_875_, 4, v___f_872_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v___f_868_);
v___x_877_ = l_StateRefT_x27_instMonad___redArg(v___x_876_);
v_toApplicative_878_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v___x_877_, 1);
lean_dec(v_unused_929_);
v___x_880_ = v___x_877_;
v_isShared_881_ = v_isSharedCheck_928_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_toApplicative_878_);
lean_dec(v___x_877_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_928_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v_toFunctor_882_; lean_object* v_toSeq_883_; lean_object* v_toSeqLeft_884_; lean_object* v_toSeqRight_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_926_; 
v_toFunctor_882_ = lean_ctor_get(v_toApplicative_878_, 0);
v_toSeq_883_ = lean_ctor_get(v_toApplicative_878_, 2);
v_toSeqLeft_884_ = lean_ctor_get(v_toApplicative_878_, 3);
v_toSeqRight_885_ = lean_ctor_get(v_toApplicative_878_, 4);
v_isSharedCheck_926_ = !lean_is_exclusive(v_toApplicative_878_);
if (v_isSharedCheck_926_ == 0)
{
lean_object* v_unused_927_; 
v_unused_927_ = lean_ctor_get(v_toApplicative_878_, 1);
lean_dec(v_unused_927_);
v___x_887_ = v_toApplicative_878_;
v_isShared_888_ = v_isSharedCheck_926_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_toSeqRight_885_);
lean_inc(v_toSeqLeft_884_);
lean_inc(v_toSeq_883_);
lean_inc(v_toFunctor_882_);
lean_dec(v_toApplicative_878_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_926_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___f_889_; lean_object* v___f_890_; lean_object* v___f_891_; lean_object* v___f_892_; lean_object* v___x_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___x_898_; 
v___f_889_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4));
v___f_890_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5));
lean_inc_ref(v_toFunctor_882_);
v___f_891_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_891_, 0, v_toFunctor_882_);
v___f_892_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_892_, 0, v_toFunctor_882_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___f_891_);
lean_ctor_set(v___x_893_, 1, v___f_892_);
v___f_894_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_894_, 0, v_toSeqRight_885_);
v___f_895_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_895_, 0, v_toSeqLeft_884_);
v___f_896_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_896_, 0, v_toSeq_883_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 4, v___f_894_);
lean_ctor_set(v___x_887_, 3, v___f_895_);
lean_ctor_set(v___x_887_, 2, v___f_896_);
lean_ctor_set(v___x_887_, 1, v___f_889_);
lean_ctor_set(v___x_887_, 0, v___x_893_);
v___x_898_ = v___x_887_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v___f_889_);
lean_ctor_set(v_reuseFailAlloc_925_, 2, v___f_896_);
lean_ctor_set(v_reuseFailAlloc_925_, 3, v___f_895_);
lean_ctor_set(v_reuseFailAlloc_925_, 4, v___f_894_);
v___x_898_ = v_reuseFailAlloc_925_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
lean_object* v___x_900_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v___f_890_);
lean_ctor_set(v___x_880_, 0, v___x_898_);
v___x_900_ = v___x_880_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_898_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v___f_890_);
v___x_900_ = v_reuseFailAlloc_924_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_901_ = lean_array_get_size(v_acc_855_);
v___x_902_ = lean_array_get_size(v_declInfos_852_);
v___x_903_ = lean_nat_dec_lt(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec_ref(v___x_900_);
lean_dec_ref(v_declInfos_852_);
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
v___x_904_ = lean_apply_6(v_k_853_, v_acc_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, lean_box(0));
return v___x_904_;
}
else
{
lean_object* v___x_905_; uint8_t v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___f_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v_snd_914_; lean_object* v_fst_915_; lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v___x_918_; lean_object* v___f_919_; lean_object* v___x_920_; 
v___x_905_ = lean_box(0);
v___x_906_ = 0;
v___x_907_ = l_Lean_instInhabitedExpr;
v___f_908_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0___boxed), 8, 2);
lean_closure_set(v___f_908_, 0, v___x_900_);
lean_closure_set(v___f_908_, 1, v___x_907_);
v___f_909_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_909_, 0, v___f_908_);
v___x_910_ = lean_box(v___x_906_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___f_909_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_905_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_array_get(v___x_912_, v_declInfos_852_, v___x_901_);
lean_dec_ref_known(v___x_912_, 2);
v_snd_914_ = lean_ctor_get(v___x_913_, 1);
lean_inc(v_snd_914_);
v_fst_915_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_fst_915_);
lean_dec(v___x_913_);
v_fst_916_ = lean_ctor_get(v_snd_914_, 0);
lean_inc(v_fst_916_);
v_snd_917_ = lean_ctor_get(v_snd_914_, 1);
lean_inc(v_snd_917_);
lean_dec(v_snd_914_);
v___x_918_ = lean_box(v_kind_854_);
lean_inc_ref(v_acc_855_);
v___f_919_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1___boxed), 10, 4);
lean_closure_set(v___f_919_, 0, v_acc_855_);
lean_closure_set(v___f_919_, 1, v_declInfos_852_);
lean_closure_set(v___f_919_, 2, v_k_853_);
lean_closure_set(v___f_919_, 3, v___x_918_);
lean_inc(v___y_859_);
lean_inc_ref(v___y_858_);
lean_inc(v___y_857_);
lean_inc_ref(v___y_856_);
v___x_920_ = lean_apply_6(v_snd_917_, v_acc_855_, v___y_856_, v___y_857_, v___y_858_, v___y_859_, lean_box(0));
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; uint8_t v___x_922_; lean_object* v___x_923_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
lean_inc(v_a_921_);
lean_dec_ref_known(v___x_920_, 1);
v___x_922_ = lean_unbox(v_fst_916_);
lean_dec(v_fst_916_);
v___x_923_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_915_, v___x_922_, v_a_921_, v___f_919_, v_kind_854_, v___y_856_, v___y_857_, v___y_858_, v___y_859_);
return v___x_923_;
}
else
{
lean_dec_ref(v___f_919_);
lean_dec(v_fst_916_);
lean_dec(v_fst_915_);
return v___x_920_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__1(lean_object* v_acc_930_, lean_object* v_declInfos_931_, lean_object* v_k_932_, uint8_t v_kind_933_, lean_object* v_x_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_array_push(v_acc_930_, v_x_934_);
v___x_941_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23(v_declInfos_931_, v_k_932_, v_kind_933_, v___x_940_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___boxed(lean_object* v_declInfos_942_, lean_object* v_k_943_, lean_object* v_kind_944_, lean_object* v_acc_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
uint8_t v_kind_boxed_951_; lean_object* v_res_952_; 
v_kind_boxed_951_ = lean_unbox(v_kind_944_);
v_res_952_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23(v_declInfos_942_, v_k_943_, v_kind_boxed_951_, v_acc_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(lean_object* v_declInfos_955_, lean_object* v_k_956_, uint8_t v_kind_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0));
v___x_964_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23(v_declInfos_955_, v_k_956_, v_kind_957_, v___x_963_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(lean_object* v_declInfos_965_, lean_object* v_k_966_, lean_object* v_kind_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v_kind_boxed_973_; lean_object* v_res_974_; 
v_kind_boxed_973_ = lean_unbox(v_kind_967_);
v_res_974_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_declInfos_965_, v_k_966_, v_kind_boxed_973_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(size_t v_sz_975_, size_t v_i_976_, lean_object* v_bs_977_){
_start:
{
uint8_t v___x_978_; 
v___x_978_ = lean_usize_dec_lt(v_i_976_, v_sz_975_);
if (v___x_978_ == 0)
{
return v_bs_977_;
}
else
{
lean_object* v_v_979_; lean_object* v_fst_980_; lean_object* v_snd_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_997_; 
v_v_979_ = lean_array_uget(v_bs_977_, v_i_976_);
v_fst_980_ = lean_ctor_get(v_v_979_, 0);
v_snd_981_ = lean_ctor_get(v_v_979_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_v_979_);
if (v_isSharedCheck_997_ == 0)
{
v___x_983_ = v_v_979_;
v_isShared_984_ = v_isSharedCheck_997_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snd_981_);
lean_inc(v_fst_980_);
lean_dec(v_v_979_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_997_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_985_; lean_object* v_bs_x27_986_; uint8_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_990_; 
v___x_985_ = lean_unsigned_to_nat(0u);
v_bs_x27_986_ = lean_array_uset(v_bs_977_, v_i_976_, v___x_985_);
v___x_987_ = 0;
v___x_988_ = lean_box(v___x_987_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_988_);
v___x_990_ = v___x_983_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_snd_981_);
v___x_990_ = v_reuseFailAlloc_996_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
lean_object* v___x_991_; size_t v___x_992_; size_t v___x_993_; lean_object* v___x_994_; 
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v_fst_980_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = ((size_t)1ULL);
v___x_993_ = lean_usize_add(v_i_976_, v___x_992_);
v___x_994_ = lean_array_uset(v_bs_x27_986_, v_i_976_, v___x_991_);
v_i_976_ = v___x_993_;
v_bs_977_ = v___x_994_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15___boxed(lean_object* v_sz_998_, lean_object* v_i_999_, lean_object* v_bs_1000_){
_start:
{
size_t v_sz_boxed_1001_; size_t v_i_boxed_1002_; lean_object* v_res_1003_; 
v_sz_boxed_1001_ = lean_unbox_usize(v_sz_998_);
lean_dec(v_sz_998_);
v_i_boxed_1002_ = lean_unbox_usize(v_i_999_);
lean_dec(v_i_999_);
v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(v_sz_boxed_1001_, v_i_boxed_1002_, v_bs_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(lean_object* v_declInfos_1004_, lean_object* v_k_1005_, uint8_t v_kind_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
size_t v_sz_1012_; size_t v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v_sz_1012_ = lean_array_size(v_declInfos_1004_);
v___x_1013_ = ((size_t)0ULL);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(v_sz_1012_, v___x_1013_, v_declInfos_1004_);
v___x_1015_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v___x_1014_, v_k_1005_, v_kind_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(lean_object* v_declInfos_1016_, lean_object* v_k_1017_, lean_object* v_kind_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
uint8_t v_kind_boxed_1024_; lean_object* v_res_1025_; 
v_kind_boxed_1024_ = lean_unbox(v_kind_1018_);
v_res_1025_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_1016_, v_k_1017_, v_kind_boxed_1024_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(lean_object* v_declInfos_1026_, lean_object* v_k_1027_, uint8_t v_kind_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
size_t v_sz_1034_; size_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_sz_1034_ = lean_array_size(v_declInfos_1026_);
v___x_1035_ = ((size_t)0ULL);
v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_1034_, v___x_1035_, v_declInfos_1026_);
v___x_1037_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_1036_, v_k_1027_, v_kind_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(lean_object* v_declInfos_1038_, lean_object* v_k_1039_, lean_object* v_kind_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
uint8_t v_kind_boxed_1046_; lean_object* v_res_1047_; 
v_kind_boxed_1046_ = lean_unbox(v_kind_1040_);
v_res_1047_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_declInfos_1038_, v_k_1039_, v_kind_boxed_1046_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(lean_object* v___x_1049_, lean_object* v_dummy_1050_, lean_object* v___x_1051_, lean_object* v___x_1052_, lean_object* v___x_1053_, lean_object* v_motive_1054_, lean_object* v_zs1_1055_, uint8_t v___x_1056_, uint8_t v___x_1057_, uint8_t v___x_1058_, lean_object* v_v_1059_, lean_object* v___x_1060_, lean_object* v_zs2_1061_, lean_object* v_ctorRet2_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = l_Lean_mkAppN(v___x_1049_, v_zs2_1061_);
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
v___x_1069_ = lean_whnf(v_ctorRet2_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v_a_1070_; lean_object* v_nargs_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref_known(v___x_1069_, 1);
v_nargs_1071_ = l_Lean_Expr_getAppNumArgs(v_a_1070_);
lean_inc(v_nargs_1071_);
v___x_1072_ = lean_mk_array(v_nargs_1071_, v_dummy_1050_);
v___x_1073_ = lean_nat_sub(v_nargs_1071_, v___x_1051_);
lean_dec(v_nargs_1071_);
v___x_1074_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1070_, v___x_1072_, v___x_1073_);
v___x_1075_ = lean_array_get_size(v___x_1074_);
v___x_1076_ = l_Array_toSubarray___redArg(v___x_1074_, v___x_1052_, v___x_1075_);
v___x_1077_ = l_Subarray_copy___redArg(v___x_1076_);
v___x_1078_ = lean_array_push(v___x_1077_, v___x_1068_);
v___x_1079_ = l_Array_append___redArg(v___x_1053_, v___x_1078_);
lean_dec_ref(v___x_1078_);
v___x_1080_ = l_Lean_mkAppN(v_motive_1054_, v___x_1079_);
lean_dec_ref(v___x_1079_);
v___x_1081_ = l_Array_append___redArg(v_zs1_1055_, v_zs2_1061_);
v___x_1082_ = l_Lean_Meta_mkForallFVars(v___x_1081_, v___x_1080_, v___x_1056_, v___x_1057_, v___x_1057_, v___x_1058_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec_ref(v___x_1081_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1102_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1102_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_a_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1102_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___y_1088_; 
if (lean_obj_tag(v_v_1059_) == 1)
{
lean_object* v_str_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_str_1093_ = lean_ctor_get(v_v_1059_, 1);
lean_inc_ref(v_str_1093_);
lean_dec_ref_known(v_v_1059_, 2);
v___x_1094_ = lean_box(0);
v___x_1095_ = l_Lean_Name_str___override(v___x_1094_, v_str_1093_);
v___y_1088_ = v___x_1095_;
goto v___jp_1087_;
}
else
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_dec(v_v_1059_);
v___x_1096_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_1097_ = lean_nat_add(v___x_1060_, v___x_1051_);
v___x_1098_ = l_Nat_reprFast(v___x_1097_);
v___x_1099_ = lean_string_append(v___x_1096_, v___x_1098_);
lean_dec_ref(v___x_1098_);
v___x_1100_ = lean_box(0);
v___x_1101_ = l_Lean_Name_str___override(v___x_1100_, v___x_1099_);
v___y_1088_ = v___x_1101_;
goto v___jp_1087_;
}
v___jp_1087_:
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
v___x_1089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___y_1088_);
lean_ctor_set(v___x_1089_, 1, v_a_1083_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1089_);
v___x_1091_ = v___x_1085_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec(v_v_1059_);
v_a_1103_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1082_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1082_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec_ref(v___x_1068_);
lean_dec(v_v_1059_);
lean_dec_ref(v_zs1_1055_);
lean_dec_ref(v_motive_1054_);
lean_dec_ref(v___x_1053_);
lean_dec(v___x_1052_);
lean_dec_ref(v_dummy_1050_);
v_a_1111_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1118_ == 0)
{
v___x_1113_ = v___x_1069_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1069_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1111_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_1119_ = _args[0];
lean_object* v_dummy_1120_ = _args[1];
lean_object* v___x_1121_ = _args[2];
lean_object* v___x_1122_ = _args[3];
lean_object* v___x_1123_ = _args[4];
lean_object* v_motive_1124_ = _args[5];
lean_object* v_zs1_1125_ = _args[6];
lean_object* v___x_1126_ = _args[7];
lean_object* v___x_1127_ = _args[8];
lean_object* v___x_1128_ = _args[9];
lean_object* v_v_1129_ = _args[10];
lean_object* v___x_1130_ = _args[11];
lean_object* v_zs2_1131_ = _args[12];
lean_object* v_ctorRet2_1132_ = _args[13];
lean_object* v___y_1133_ = _args[14];
lean_object* v___y_1134_ = _args[15];
lean_object* v___y_1135_ = _args[16];
lean_object* v___y_1136_ = _args[17];
lean_object* v___y_1137_ = _args[18];
_start:
{
uint8_t v___x_23075__boxed_1138_; uint8_t v___x_23076__boxed_1139_; uint8_t v___x_23077__boxed_1140_; lean_object* v_res_1141_; 
v___x_23075__boxed_1138_ = lean_unbox(v___x_1126_);
v___x_23076__boxed_1139_ = lean_unbox(v___x_1127_);
v___x_23077__boxed_1140_ = lean_unbox(v___x_1128_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1119_, v_dummy_1120_, v___x_1121_, v___x_1122_, v___x_1123_, v_motive_1124_, v_zs1_1125_, v___x_23075__boxed_1138_, v___x_23076__boxed_1139_, v___x_23077__boxed_1140_, v_v_1129_, v___x_1130_, v_zs2_1131_, v_ctorRet2_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec_ref(v_zs2_1131_);
lean_dec(v___x_1130_);
lean_dec(v___x_1121_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(lean_object* v___x_1142_, lean_object* v___x_1143_, lean_object* v___x_1144_, lean_object* v_motive_1145_, uint8_t v___x_1146_, uint8_t v___x_1147_, uint8_t v___x_1148_, lean_object* v_v_1149_, lean_object* v___x_1150_, lean_object* v_a_1151_, lean_object* v_zs1_1152_, lean_object* v_ctorRet1_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
lean_inc_ref(v___x_1142_);
v___x_1159_ = l_Lean_mkAppN(v___x_1142_, v_zs1_1152_);
lean_inc(v___y_1157_);
lean_inc_ref(v___y_1156_);
lean_inc(v___y_1155_);
lean_inc_ref(v___y_1154_);
v___x_1160_ = lean_whnf(v_ctorRet1_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v_dummy_1162_; lean_object* v_nargs_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
lean_inc(v_a_1161_);
lean_dec_ref_known(v___x_1160_, 1);
v_dummy_1162_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
v_nargs_1163_ = l_Lean_Expr_getAppNumArgs(v_a_1161_);
lean_inc(v_nargs_1163_);
v___x_1164_ = lean_mk_array(v_nargs_1163_, v_dummy_1162_);
v___x_1165_ = lean_nat_sub(v_nargs_1163_, v___x_1143_);
lean_dec(v_nargs_1163_);
v___x_1166_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1161_, v___x_1164_, v___x_1165_);
v___x_1167_ = lean_array_get_size(v___x_1166_);
lean_inc(v___x_1144_);
v___x_1168_ = l_Array_toSubarray___redArg(v___x_1166_, v___x_1144_, v___x_1167_);
v___x_1169_ = l_Subarray_copy___redArg(v___x_1168_);
v___x_1170_ = lean_array_push(v___x_1169_, v___x_1159_);
v___x_1171_ = lean_box(v___x_1146_);
v___x_1172_ = lean_box(v___x_1147_);
v___x_1173_ = lean_box(v___x_1148_);
v___f_1174_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed), 19, 12);
lean_closure_set(v___f_1174_, 0, v___x_1142_);
lean_closure_set(v___f_1174_, 1, v_dummy_1162_);
lean_closure_set(v___f_1174_, 2, v___x_1143_);
lean_closure_set(v___f_1174_, 3, v___x_1144_);
lean_closure_set(v___f_1174_, 4, v___x_1170_);
lean_closure_set(v___f_1174_, 5, v_motive_1145_);
lean_closure_set(v___f_1174_, 6, v_zs1_1152_);
lean_closure_set(v___f_1174_, 7, v___x_1171_);
lean_closure_set(v___f_1174_, 8, v___x_1172_);
lean_closure_set(v___f_1174_, 9, v___x_1173_);
lean_closure_set(v___f_1174_, 10, v_v_1149_);
lean_closure_set(v___f_1174_, 11, v___x_1150_);
v___x_1175_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1151_, v___f_1174_, v___x_1146_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
return v___x_1175_;
}
else
{
lean_object* v_a_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1183_; 
lean_dec_ref(v___x_1159_);
lean_dec_ref(v_zs1_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v___x_1150_);
lean_dec(v_v_1149_);
lean_dec_ref(v_motive_1145_);
lean_dec(v___x_1144_);
lean_dec(v___x_1143_);
lean_dec_ref(v___x_1142_);
v_a_1176_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1178_ = v___x_1160_;
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_a_1176_);
lean_dec(v___x_1160_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1183_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1181_; 
if (v_isShared_1179_ == 0)
{
v___x_1181_ = v___x_1178_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(lean_object** _args){
lean_object* v___x_1184_ = _args[0];
lean_object* v___x_1185_ = _args[1];
lean_object* v___x_1186_ = _args[2];
lean_object* v_motive_1187_ = _args[3];
lean_object* v___x_1188_ = _args[4];
lean_object* v___x_1189_ = _args[5];
lean_object* v___x_1190_ = _args[6];
lean_object* v_v_1191_ = _args[7];
lean_object* v___x_1192_ = _args[8];
lean_object* v_a_1193_ = _args[9];
lean_object* v_zs1_1194_ = _args[10];
lean_object* v_ctorRet1_1195_ = _args[11];
lean_object* v___y_1196_ = _args[12];
lean_object* v___y_1197_ = _args[13];
lean_object* v___y_1198_ = _args[14];
lean_object* v___y_1199_ = _args[15];
lean_object* v___y_1200_ = _args[16];
_start:
{
uint8_t v___x_23216__boxed_1201_; uint8_t v___x_23217__boxed_1202_; uint8_t v___x_23218__boxed_1203_; lean_object* v_res_1204_; 
v___x_23216__boxed_1201_ = lean_unbox(v___x_1188_);
v___x_23217__boxed_1202_ = lean_unbox(v___x_1189_);
v___x_23218__boxed_1203_ = lean_unbox(v___x_1190_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1184_, v___x_1185_, v___x_1186_, v_motive_1187_, v___x_23216__boxed_1201_, v___x_23217__boxed_1202_, v___x_23218__boxed_1203_, v_v_1191_, v___x_1192_, v_a_1193_, v_zs1_1194_, v_ctorRet1_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(lean_object* v_tail_1205_, lean_object* v_params_1206_, lean_object* v___x_1207_, lean_object* v_motive_1208_, size_t v_sz_1209_, size_t v_i_1210_, lean_object* v_bs_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_usize_dec_lt(v_i_1210_, v_sz_1209_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; 
lean_dec_ref(v_motive_1208_);
lean_dec(v___x_1207_);
lean_dec(v_tail_1205_);
v___x_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1218_, 0, v_bs_1211_);
return v___x_1218_;
}
else
{
uint8_t v___x_1219_; uint8_t v___x_1220_; lean_object* v___x_1221_; lean_object* v_v_1222_; lean_object* v___x_1223_; lean_object* v_bs_x27_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v___x_1219_ = 0;
v___x_1220_ = 1;
v___x_1221_ = lean_unsigned_to_nat(1u);
v_v_1222_ = lean_array_uget(v_bs_1211_, v_i_1210_);
v___x_1223_ = lean_unsigned_to_nat(0u);
v_bs_x27_1224_ = lean_array_uset(v_bs_1211_, v_i_1210_, v___x_1223_);
v___x_1225_ = lean_usize_to_nat(v_i_1210_);
lean_inc(v_tail_1205_);
lean_inc(v_v_1222_);
v___x_1226_ = l_Lean_mkConst(v_v_1222_, v_tail_1205_);
v___x_1227_ = l_Lean_mkAppN(v___x_1226_, v_params_1206_);
lean_inc(v___y_1215_);
lean_inc_ref(v___y_1214_);
lean_inc(v___y_1213_);
lean_inc_ref(v___y_1212_);
lean_inc_ref(v___x_1227_);
v___x_1228_ = lean_infer_type(v___x_1227_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc_n(v_a_1229_, 2);
lean_dec_ref_known(v___x_1228_, 1);
v___x_1230_ = lean_box(v___x_1219_);
v___x_1231_ = lean_box(v___x_1217_);
v___x_1232_ = lean_box(v___x_1220_);
lean_inc_ref(v_motive_1208_);
lean_inc(v___x_1207_);
v___f_1233_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed), 17, 10);
lean_closure_set(v___f_1233_, 0, v___x_1227_);
lean_closure_set(v___f_1233_, 1, v___x_1221_);
lean_closure_set(v___f_1233_, 2, v___x_1207_);
lean_closure_set(v___f_1233_, 3, v_motive_1208_);
lean_closure_set(v___f_1233_, 4, v___x_1230_);
lean_closure_set(v___f_1233_, 5, v___x_1231_);
lean_closure_set(v___f_1233_, 6, v___x_1232_);
lean_closure_set(v___f_1233_, 7, v_v_1222_);
lean_closure_set(v___f_1233_, 8, v___x_1225_);
lean_closure_set(v___f_1233_, 9, v_a_1229_);
v___x_1234_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_1229_, v___f_1233_, v___x_1219_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; size_t v___x_1236_; size_t v___x_1237_; lean_object* v___x_1238_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = ((size_t)1ULL);
v___x_1237_ = lean_usize_add(v_i_1210_, v___x_1236_);
v___x_1238_ = lean_array_uset(v_bs_x27_1224_, v_i_1210_, v_a_1235_);
v_i_1210_ = v___x_1237_;
v_bs_1211_ = v___x_1238_;
goto _start;
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v_bs_x27_1224_);
lean_dec_ref(v_motive_1208_);
lean_dec(v___x_1207_);
lean_dec(v_tail_1205_);
v_a_1240_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1234_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1234_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v___x_1227_);
lean_dec(v___x_1225_);
lean_dec_ref(v_bs_x27_1224_);
lean_dec(v_v_1222_);
lean_dec_ref(v_motive_1208_);
lean_dec(v___x_1207_);
lean_dec(v_tail_1205_);
v_a_1248_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1228_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1228_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(lean_object* v_tail_1256_, lean_object* v_params_1257_, lean_object* v___x_1258_, lean_object* v_motive_1259_, lean_object* v_sz_1260_, lean_object* v_i_1261_, lean_object* v_bs_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
size_t v_sz_boxed_1268_; size_t v_i_boxed_1269_; lean_object* v_res_1270_; 
v_sz_boxed_1268_ = lean_unbox_usize(v_sz_1260_);
lean_dec(v_sz_1260_);
v_i_boxed_1269_ = lean_unbox_usize(v_i_1261_);
lean_dec(v_i_1261_);
v_res_1270_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1256_, v_params_1257_, v___x_1258_, v_motive_1259_, v_sz_boxed_1268_, v_i_boxed_1269_, v_bs_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec_ref(v_params_1257_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2(lean_object* v_ctors_1271_, lean_object* v_indName_1272_, lean_object* v_tail_1273_, lean_object* v_params_1274_, lean_object* v_ism1_1275_, lean_object* v_ism2_1276_, lean_object* v___x_1277_, uint8_t v___x_1278_, uint8_t v___x_1279_, uint8_t v___x_1280_, lean_object* v_name_1281_, lean_object* v___x_1282_, lean_object* v_numParams_1283_, lean_object* v_val_1284_, lean_object* v___x_1285_, lean_object* v___x_1286_, lean_object* v_motive_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___f_1297_; size_t v_sz_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1293_ = lean_array_mk(v_ctors_1271_);
v___x_1294_ = lean_box(v___x_1278_);
v___x_1295_ = lean_box(v___x_1279_);
v___x_1296_ = lean_box(v___x_1280_);
lean_inc(v_numParams_1283_);
lean_inc_ref(v___x_1293_);
lean_inc_ref(v_motive_1287_);
lean_inc_ref(v_params_1274_);
lean_inc(v_tail_1273_);
v___f_1297_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__1___boxed), 23, 17);
lean_closure_set(v___f_1297_, 0, v_indName_1272_);
lean_closure_set(v___f_1297_, 1, v_tail_1273_);
lean_closure_set(v___f_1297_, 2, v_params_1274_);
lean_closure_set(v___f_1297_, 3, v_ism1_1275_);
lean_closure_set(v___f_1297_, 4, v_ism2_1276_);
lean_closure_set(v___f_1297_, 5, v_motive_1287_);
lean_closure_set(v___f_1297_, 6, v___x_1277_);
lean_closure_set(v___f_1297_, 7, v___x_1294_);
lean_closure_set(v___f_1297_, 8, v___x_1295_);
lean_closure_set(v___f_1297_, 9, v___x_1296_);
lean_closure_set(v___f_1297_, 10, v_name_1281_);
lean_closure_set(v___f_1297_, 11, v___x_1282_);
lean_closure_set(v___f_1297_, 12, v___x_1293_);
lean_closure_set(v___f_1297_, 13, v_numParams_1283_);
lean_closure_set(v___f_1297_, 14, v_val_1284_);
lean_closure_set(v___f_1297_, 15, v___x_1285_);
lean_closure_set(v___f_1297_, 16, v___x_1286_);
v_sz_1298_ = lean_array_size(v___x_1293_);
v___x_1299_ = ((size_t)0ULL);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_1273_, v_params_1274_, v_numParams_1283_, v_motive_1287_, v_sz_1298_, v___x_1299_, v___x_1293_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec_ref(v_params_1274_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; uint8_t v___x_1302_; lean_object* v___x_1303_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref_known(v___x_1300_, 1);
v___x_1302_ = 0;
v___x_1303_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(v_a_1301_, v___f_1297_, v___x_1302_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
return v___x_1303_;
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v___f_1297_);
v_a_1304_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1300_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1300_);
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
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(lean_object** _args){
lean_object* v_ctors_1312_ = _args[0];
lean_object* v_indName_1313_ = _args[1];
lean_object* v_tail_1314_ = _args[2];
lean_object* v_params_1315_ = _args[3];
lean_object* v_ism1_1316_ = _args[4];
lean_object* v_ism2_1317_ = _args[5];
lean_object* v___x_1318_ = _args[6];
lean_object* v___x_1319_ = _args[7];
lean_object* v___x_1320_ = _args[8];
lean_object* v___x_1321_ = _args[9];
lean_object* v_name_1322_ = _args[10];
lean_object* v___x_1323_ = _args[11];
lean_object* v_numParams_1324_ = _args[12];
lean_object* v_val_1325_ = _args[13];
lean_object* v___x_1326_ = _args[14];
lean_object* v___x_1327_ = _args[15];
lean_object* v_motive_1328_ = _args[16];
lean_object* v___y_1329_ = _args[17];
lean_object* v___y_1330_ = _args[18];
lean_object* v___y_1331_ = _args[19];
lean_object* v___y_1332_ = _args[20];
lean_object* v___y_1333_ = _args[21];
_start:
{
uint8_t v___x_23396__boxed_1334_; uint8_t v___x_23397__boxed_1335_; uint8_t v___x_23398__boxed_1336_; lean_object* v_res_1337_; 
v___x_23396__boxed_1334_ = lean_unbox(v___x_1319_);
v___x_23397__boxed_1335_ = lean_unbox(v___x_1320_);
v___x_23398__boxed_1336_ = lean_unbox(v___x_1321_);
v_res_1337_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1312_, v_indName_1313_, v_tail_1314_, v_params_1315_, v_ism1_1316_, v_ism2_1317_, v___x_1318_, v___x_23396__boxed_1334_, v___x_23397__boxed_1335_, v___x_23398__boxed_1336_, v_name_1322_, v___x_1323_, v_numParams_1324_, v_val_1325_, v___x_1326_, v___x_1327_, v_motive_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
lean_dec(v___y_1332_);
lean_dec_ref(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v___y_1329_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3(lean_object* v_ism1_1341_, lean_object* v_head_1342_, lean_object* v_ctors_1343_, lean_object* v_indName_1344_, lean_object* v_tail_1345_, lean_object* v_params_1346_, lean_object* v_name_1347_, lean_object* v___x_1348_, lean_object* v_numParams_1349_, lean_object* v_val_1350_, lean_object* v___x_1351_, lean_object* v___x_1352_, lean_object* v_ism2_1353_, lean_object* v_x_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; uint8_t v___x_1363_; uint8_t v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; 
lean_inc_ref(v_ism1_1341_);
v___x_1360_ = l_Array_append___redArg(v_ism1_1341_, v_ism2_1353_);
v___x_1361_ = l_Lean_mkSort(v_head_1342_);
v___x_1362_ = 0;
v___x_1363_ = 1;
v___x_1364_ = 1;
v___x_1365_ = lean_box(v___x_1362_);
v___x_1366_ = lean_box(v___x_1363_);
v___x_1367_ = lean_box(v___x_1364_);
lean_inc_ref(v___x_1360_);
v___f_1368_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__2___boxed), 22, 16);
lean_closure_set(v___f_1368_, 0, v_ctors_1343_);
lean_closure_set(v___f_1368_, 1, v_indName_1344_);
lean_closure_set(v___f_1368_, 2, v_tail_1345_);
lean_closure_set(v___f_1368_, 3, v_params_1346_);
lean_closure_set(v___f_1368_, 4, v_ism1_1341_);
lean_closure_set(v___f_1368_, 5, v_ism2_1353_);
lean_closure_set(v___f_1368_, 6, v___x_1360_);
lean_closure_set(v___f_1368_, 7, v___x_1365_);
lean_closure_set(v___f_1368_, 8, v___x_1366_);
lean_closure_set(v___f_1368_, 9, v___x_1367_);
lean_closure_set(v___f_1368_, 10, v_name_1347_);
lean_closure_set(v___f_1368_, 11, v___x_1348_);
lean_closure_set(v___f_1368_, 12, v_numParams_1349_);
lean_closure_set(v___f_1368_, 13, v_val_1350_);
lean_closure_set(v___f_1368_, 14, v___x_1351_);
lean_closure_set(v___f_1368_, 15, v___x_1352_);
v___x_1369_ = l_Lean_Meta_mkForallFVars(v___x_1360_, v___x_1361_, v___x_1362_, v___x_1363_, v___x_1363_, v___x_1364_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec_ref(v___x_1360_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v___x_1371_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_1372_ = 0;
v___x_1373_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_1371_, v___x_1364_, v_a_1370_, v___f_1368_, v___x_1372_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
return v___x_1373_;
}
else
{
lean_dec_ref(v___f_1368_);
return v___x_1369_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(lean_object** _args){
lean_object* v_ism1_1374_ = _args[0];
lean_object* v_head_1375_ = _args[1];
lean_object* v_ctors_1376_ = _args[2];
lean_object* v_indName_1377_ = _args[3];
lean_object* v_tail_1378_ = _args[4];
lean_object* v_params_1379_ = _args[5];
lean_object* v_name_1380_ = _args[6];
lean_object* v___x_1381_ = _args[7];
lean_object* v_numParams_1382_ = _args[8];
lean_object* v_val_1383_ = _args[9];
lean_object* v___x_1384_ = _args[10];
lean_object* v___x_1385_ = _args[11];
lean_object* v_ism2_1386_ = _args[12];
lean_object* v_x_1387_ = _args[13];
lean_object* v___y_1388_ = _args[14];
lean_object* v___y_1389_ = _args[15];
lean_object* v___y_1390_ = _args[16];
lean_object* v___y_1391_ = _args[17];
lean_object* v___y_1392_ = _args[18];
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_mkCasesOnSameCtorHet___lam__3(v_ism1_1374_, v_head_1375_, v_ctors_1376_, v_indName_1377_, v_tail_1378_, v_params_1379_, v_name_1380_, v___x_1381_, v_numParams_1382_, v_val_1383_, v___x_1384_, v___x_1385_, v_ism2_1386_, v_x_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec_ref(v_x_1387_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4(lean_object* v_head_1394_, lean_object* v_ctors_1395_, lean_object* v_indName_1396_, lean_object* v_tail_1397_, lean_object* v_params_1398_, lean_object* v_name_1399_, lean_object* v___x_1400_, lean_object* v_numParams_1401_, lean_object* v_val_1402_, lean_object* v___x_1403_, lean_object* v___x_1404_, lean_object* v_t_1405_, lean_object* v___x_1406_, lean_object* v_ism1_1407_, lean_object* v_x_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___f_1414_; uint8_t v___x_1415_; lean_object* v___x_1416_; 
v___f_1414_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__3___boxed), 19, 12);
lean_closure_set(v___f_1414_, 0, v_ism1_1407_);
lean_closure_set(v___f_1414_, 1, v_head_1394_);
lean_closure_set(v___f_1414_, 2, v_ctors_1395_);
lean_closure_set(v___f_1414_, 3, v_indName_1396_);
lean_closure_set(v___f_1414_, 4, v_tail_1397_);
lean_closure_set(v___f_1414_, 5, v_params_1398_);
lean_closure_set(v___f_1414_, 6, v_name_1399_);
lean_closure_set(v___f_1414_, 7, v___x_1400_);
lean_closure_set(v___f_1414_, 8, v_numParams_1401_);
lean_closure_set(v___f_1414_, 9, v_val_1402_);
lean_closure_set(v___f_1414_, 10, v___x_1403_);
lean_closure_set(v___f_1414_, 11, v___x_1404_);
v___x_1415_ = 0;
v___x_1416_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1405_, v___x_1406_, v___f_1414_, v___x_1415_, v___x_1415_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(lean_object** _args){
lean_object* v_head_1417_ = _args[0];
lean_object* v_ctors_1418_ = _args[1];
lean_object* v_indName_1419_ = _args[2];
lean_object* v_tail_1420_ = _args[3];
lean_object* v_params_1421_ = _args[4];
lean_object* v_name_1422_ = _args[5];
lean_object* v___x_1423_ = _args[6];
lean_object* v_numParams_1424_ = _args[7];
lean_object* v_val_1425_ = _args[8];
lean_object* v___x_1426_ = _args[9];
lean_object* v___x_1427_ = _args[10];
lean_object* v_t_1428_ = _args[11];
lean_object* v___x_1429_ = _args[12];
lean_object* v_ism1_1430_ = _args[13];
lean_object* v_x_1431_ = _args[14];
lean_object* v___y_1432_ = _args[15];
lean_object* v___y_1433_ = _args[16];
lean_object* v___y_1434_ = _args[17];
lean_object* v___y_1435_ = _args[18];
lean_object* v___y_1436_ = _args[19];
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_mkCasesOnSameCtorHet___lam__4(v_head_1417_, v_ctors_1418_, v_indName_1419_, v_tail_1420_, v_params_1421_, v_name_1422_, v___x_1423_, v_numParams_1424_, v_val_1425_, v___x_1426_, v___x_1427_, v_t_1428_, v___x_1429_, v_ism1_1430_, v_x_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec_ref(v_x_1431_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5(lean_object* v_numIndices_1438_, lean_object* v___x_1439_, lean_object* v_head_1440_, lean_object* v_ctors_1441_, lean_object* v_indName_1442_, lean_object* v_tail_1443_, lean_object* v_params_1444_, lean_object* v_name_1445_, lean_object* v___x_1446_, lean_object* v_numParams_1447_, lean_object* v_val_1448_, lean_object* v___x_1449_, lean_object* v_x_1450_, lean_object* v_t_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___f_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; 
v___x_1457_ = lean_nat_add(v_numIndices_1438_, v___x_1439_);
v___x_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_inc_ref(v___x_1458_);
lean_inc_ref(v_t_1451_);
v___f_1459_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__4___boxed), 20, 13);
lean_closure_set(v___f_1459_, 0, v_head_1440_);
lean_closure_set(v___f_1459_, 1, v_ctors_1441_);
lean_closure_set(v___f_1459_, 2, v_indName_1442_);
lean_closure_set(v___f_1459_, 3, v_tail_1443_);
lean_closure_set(v___f_1459_, 4, v_params_1444_);
lean_closure_set(v___f_1459_, 5, v_name_1445_);
lean_closure_set(v___f_1459_, 6, v___x_1446_);
lean_closure_set(v___f_1459_, 7, v_numParams_1447_);
lean_closure_set(v___f_1459_, 8, v_val_1448_);
lean_closure_set(v___f_1459_, 9, v___x_1449_);
lean_closure_set(v___f_1459_, 10, v___x_1439_);
lean_closure_set(v___f_1459_, 11, v_t_1451_);
lean_closure_set(v___f_1459_, 12, v___x_1458_);
v___x_1460_ = 0;
v___x_1461_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1451_, v___x_1458_, v___f_1459_, v___x_1460_, v___x_1460_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_1462_ = _args[0];
lean_object* v___x_1463_ = _args[1];
lean_object* v_head_1464_ = _args[2];
lean_object* v_ctors_1465_ = _args[3];
lean_object* v_indName_1466_ = _args[4];
lean_object* v_tail_1467_ = _args[5];
lean_object* v_params_1468_ = _args[6];
lean_object* v_name_1469_ = _args[7];
lean_object* v___x_1470_ = _args[8];
lean_object* v_numParams_1471_ = _args[9];
lean_object* v_val_1472_ = _args[10];
lean_object* v___x_1473_ = _args[11];
lean_object* v_x_1474_ = _args[12];
lean_object* v_t_1475_ = _args[13];
lean_object* v___y_1476_ = _args[14];
lean_object* v___y_1477_ = _args[15];
lean_object* v___y_1478_ = _args[16];
lean_object* v___y_1479_ = _args[17];
lean_object* v___y_1480_ = _args[18];
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_mkCasesOnSameCtorHet___lam__5(v_numIndices_1462_, v___x_1463_, v_head_1464_, v_ctors_1465_, v_indName_1466_, v_tail_1467_, v_params_1468_, v_name_1469_, v___x_1470_, v_numParams_1471_, v_val_1472_, v___x_1473_, v_x_1474_, v_t_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec_ref(v_x_1474_);
lean_dec(v_numIndices_1462_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6(lean_object* v_numIndices_1484_, lean_object* v_head_1485_, lean_object* v_ctors_1486_, lean_object* v_indName_1487_, lean_object* v_tail_1488_, lean_object* v_name_1489_, lean_object* v___x_1490_, lean_object* v_numParams_1491_, lean_object* v_val_1492_, lean_object* v___x_1493_, lean_object* v_params_1494_, lean_object* v_t_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___f_1502_; lean_object* v___x_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; 
v___x_1501_ = lean_unsigned_to_nat(1u);
v___f_1502_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__5___boxed), 19, 12);
lean_closure_set(v___f_1502_, 0, v_numIndices_1484_);
lean_closure_set(v___f_1502_, 1, v___x_1501_);
lean_closure_set(v___f_1502_, 2, v_head_1485_);
lean_closure_set(v___f_1502_, 3, v_ctors_1486_);
lean_closure_set(v___f_1502_, 4, v_indName_1487_);
lean_closure_set(v___f_1502_, 5, v_tail_1488_);
lean_closure_set(v___f_1502_, 6, v_params_1494_);
lean_closure_set(v___f_1502_, 7, v_name_1489_);
lean_closure_set(v___f_1502_, 8, v___x_1490_);
lean_closure_set(v___f_1502_, 9, v_numParams_1491_);
lean_closure_set(v___f_1502_, 10, v_val_1492_);
lean_closure_set(v___f_1502_, 11, v___x_1493_);
v___x_1503_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
v___x_1504_ = 0;
v___x_1505_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_1495_, v___x_1503_, v___f_1502_, v___x_1504_, v___x_1504_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(lean_object** _args){
lean_object* v_numIndices_1506_ = _args[0];
lean_object* v_head_1507_ = _args[1];
lean_object* v_ctors_1508_ = _args[2];
lean_object* v_indName_1509_ = _args[3];
lean_object* v_tail_1510_ = _args[4];
lean_object* v_name_1511_ = _args[5];
lean_object* v___x_1512_ = _args[6];
lean_object* v_numParams_1513_ = _args[7];
lean_object* v_val_1514_ = _args[8];
lean_object* v___x_1515_ = _args[9];
lean_object* v_params_1516_ = _args[10];
lean_object* v_t_1517_ = _args[11];
lean_object* v___y_1518_ = _args[12];
lean_object* v___y_1519_ = _args[13];
lean_object* v___y_1520_ = _args[14];
lean_object* v___y_1521_ = _args[15];
lean_object* v___y_1522_ = _args[16];
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_mkCasesOnSameCtorHet___lam__6(v_numIndices_1506_, v_head_1507_, v_ctors_1508_, v_indName_1509_, v_tail_1510_, v_name_1511_, v___x_1512_, v_numParams_1513_, v_val_1514_, v___x_1515_, v_params_1516_, v_t_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7(lean_object* v_a_1524_, lean_object* v_declName_1525_, lean_object* v_levelParams_1526_, uint8_t v___x_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v___x_1533_; 
lean_inc(v___y_1531_);
lean_inc_ref(v___y_1530_);
lean_inc_ref(v_a_1524_);
v___x_1533_ = lean_infer_type(v_a_1524_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1545_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v___x_1533_, 1);
v___x_1535_ = lean_box(1);
v___x_1536_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_1525_, v_levelParams_1526_, v_a_1534_, v_a_1524_, v___x_1535_, v___y_1531_);
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1545_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_addDecl(v___x_1542_, v___x_1527_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v___x_1543_;
}
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v_levelParams_1526_);
lean_dec(v_declName_1525_);
lean_dec_ref(v_a_1524_);
v_a_1546_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1533_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1533_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(lean_object* v_a_1554_, lean_object* v_declName_1555_, lean_object* v_levelParams_1556_, lean_object* v___x_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
uint8_t v___x_23684__boxed_1563_; lean_object* v_res_1564_; 
v___x_23684__boxed_1563_ = lean_unbox(v___x_1557_);
v_res_1564_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1554_, v_declName_1555_, v_levelParams_1556_, v___x_23684__boxed_1563_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
if (lean_obj_tag(v_a_1565_) == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = l_List_reverse___redArg(v_a_1566_);
return v___x_1567_;
}
else
{
lean_object* v_head_1568_; lean_object* v_tail_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1578_; 
v_head_1568_ = lean_ctor_get(v_a_1565_, 0);
v_tail_1569_ = lean_ctor_get(v_a_1565_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_a_1565_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1571_ = v_a_1565_;
v_isShared_1572_ = v_isSharedCheck_1578_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_tail_1569_);
lean_inc(v_head_1568_);
lean_dec(v_a_1565_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1578_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1573_ = l_Lean_mkLevelParam(v_head_1568_);
if (v_isShared_1572_ == 0)
{
lean_ctor_set(v___x_1571_, 1, v_a_1566_);
lean_ctor_set(v___x_1571_, 0, v___x_1573_);
v___x_1575_ = v___x_1571_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1573_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_a_1566_);
v___x_1575_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
v_a_1565_ = v_tail_1569_;
v_a_1566_ = v___x_1575_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26(lean_object* v_msgData_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v_env_1586_; uint8_t v___x_1587_; lean_object* v_env_1588_; lean_object* v___x_1589_; lean_object* v_toCold_1590_; lean_object* v_mctx_1591_; lean_object* v_lctx_1592_; lean_object* v_options_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1585_ = lean_st_ref_get(v___y_1583_);
v_env_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc_ref(v_env_1586_);
lean_dec(v___x_1585_);
v___x_1587_ = 0;
v_env_1588_ = l_Lean_Environment_setRecordingDeps(v_env_1586_, v___x_1587_);
v___x_1589_ = lean_st_ref_get(v___y_1581_);
v_toCold_1590_ = lean_ctor_get(v___y_1582_, 0);
v_mctx_1591_ = lean_ctor_get(v___x_1589_, 0);
lean_inc_ref(v_mctx_1591_);
lean_dec(v___x_1589_);
v_lctx_1592_ = lean_ctor_get(v___y_1580_, 2);
v_options_1593_ = lean_ctor_get(v_toCold_1590_, 2);
lean_inc_ref(v_options_1593_);
lean_inc_ref(v_lctx_1592_);
v___x_1594_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1594_, 0, v_env_1588_);
lean_ctor_set(v___x_1594_, 1, v_mctx_1591_);
lean_ctor_set(v___x_1594_, 2, v_lctx_1592_);
lean_ctor_set(v___x_1594_, 3, v_options_1593_);
v___x_1595_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v_msgData_1579_);
v___x_1596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26___boxed(lean_object* v_msgData_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26(v_msgData_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(lean_object* v_msg_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v_ref_1610_; lean_object* v___x_1611_; lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1620_; 
v_ref_1610_ = lean_ctor_get(v___y_1607_, 2);
v___x_1611_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22_spec__26(v_msg_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
v_a_1612_ = lean_ctor_get(v___x_1611_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1611_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1614_ = v___x_1611_;
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
lean_inc(v_ref_1610_);
v___x_1616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1616_, 0, v_ref_1610_);
lean_ctor_set(v___x_1616_, 1, v_a_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set_tag(v___x_1614_, 1);
lean_ctor_set(v___x_1614_, 0, v___x_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg___boxed(lean_object* v_msg_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v_msg_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(lean_object* v_ref_1628_, lean_object* v_msg_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_toCold_1635_; lean_object* v_currRecDepth_1636_; lean_object* v_ref_1637_; uint16_t v_optionFlags_1638_; uint8_t v_suppressElabErrors_1639_; uint8_t v_checkDeprecated_1640_; uint8_t v_isRecordingDeps_1641_; lean_object* v_ref_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_toCold_1635_ = lean_ctor_get(v___y_1632_, 0);
v_currRecDepth_1636_ = lean_ctor_get(v___y_1632_, 1);
v_ref_1637_ = lean_ctor_get(v___y_1632_, 2);
v_optionFlags_1638_ = lean_ctor_get_uint16(v___y_1632_, sizeof(void*)*3);
v_suppressElabErrors_1639_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3 + 2);
v_checkDeprecated_1640_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1641_ = lean_ctor_get_uint8(v___y_1632_, sizeof(void*)*3 + 4);
v_ref_1642_ = l_Lean_replaceRef(v_ref_1628_, v_ref_1637_);
lean_inc(v_currRecDepth_1636_);
lean_inc_ref(v_toCold_1635_);
v___x_1643_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1643_, 0, v_toCold_1635_);
lean_ctor_set(v___x_1643_, 1, v_currRecDepth_1636_);
lean_ctor_set(v___x_1643_, 2, v_ref_1642_);
lean_ctor_set_uint16(v___x_1643_, sizeof(void*)*3, v_optionFlags_1638_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*3 + 2, v_suppressElabErrors_1639_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*3 + 3, v_checkDeprecated_1640_);
lean_ctor_set_uint8(v___x_1643_, sizeof(void*)*3 + 4, v_isRecordingDeps_1641_);
v___x_1644_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v_msg_1629_, v___y_1630_, v___y_1631_, v___x_1643_, v___y_1633_);
lean_dec_ref_known(v___x_1643_, 3);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg___boxed(lean_object* v_ref_1645_, lean_object* v_msg_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(v_ref_1645_, v_msg_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v_ref_1645_);
return v_res_1652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0(void){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1653_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1);
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
lean_ctor_set(v___x_1658_, 2, v___x_1657_);
lean_ctor_set(v___x_1658_, 3, v___x_1657_);
lean_ctor_set(v___x_1658_, 4, v___x_1656_);
lean_ctor_set(v___x_1658_, 5, v___x_1656_);
lean_ctor_set(v___x_1658_, 6, v___x_1656_);
lean_ctor_set(v___x_1658_, 7, v___x_1656_);
lean_ctor_set(v___x_1658_, 8, v___x_1656_);
lean_ctor_set(v___x_1658_, 9, v___x_1656_);
lean_ctor_set(v___x_1658_, 10, v___x_1656_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_unsigned_to_nat(32u);
v___x_1660_ = lean_mk_empty_array_with_capacity(v___x_1659_);
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4(void){
_start:
{
size_t v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1662_ = ((size_t)5ULL);
v___x_1663_ = lean_unsigned_to_nat(0u);
v___x_1664_ = lean_unsigned_to_nat(32u);
v___x_1665_ = lean_mk_empty_array_with_capacity(v___x_1664_);
v___x_1666_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__3);
v___x_1667_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
lean_ctor_set(v___x_1667_, 1, v___x_1665_);
lean_ctor_set(v___x_1667_, 2, v___x_1663_);
lean_ctor_set(v___x_1667_, 3, v___x_1663_);
lean_ctor_set_usize(v___x_1667_, 4, v___x_1662_);
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1668_ = lean_box(1);
v___x_1669_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__4);
v___x_1670_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__1);
v___x_1671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
lean_ctor_set(v___x_1671_, 2, v___x_1668_);
return v___x_1671_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__6));
v___x_1674_ = l_Lean_stringToMessageData(v___x_1673_);
return v___x_1674_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1676_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__8));
v___x_1677_ = l_Lean_stringToMessageData(v___x_1676_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__10));
v___x_1680_ = l_Lean_stringToMessageData(v___x_1679_);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__12));
v___x_1683_ = l_Lean_stringToMessageData(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1685_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__14));
v___x_1686_ = l_Lean_stringToMessageData(v___x_1685_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16));
v___x_1689_ = l_Lean_stringToMessageData(v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19(void){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18));
v___x_1692_ = l_Lean_stringToMessageData(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(lean_object* v_msg_1693_, lean_object* v_declHint_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v_env_1699_; uint8_t v___x_1700_; 
v___x_1697_ = lean_box(0);
v___x_1698_ = lean_st_ref_get(v___y_1695_);
v_env_1699_ = lean_ctor_get(v___x_1698_, 0);
lean_inc_ref(v_env_1699_);
lean_dec(v___x_1698_);
v___x_1700_ = l_Lean_Name_isAnonymous(v_declHint_1694_);
if (v___x_1700_ == 0)
{
uint8_t v_isExporting_1701_; 
v_isExporting_1701_ = lean_ctor_get_uint8(v_env_1699_, sizeof(void*)*13);
if (v_isExporting_1701_ == 0)
{
lean_object* v___x_1702_; 
lean_dec_ref(v_env_1699_);
lean_dec(v_declHint_1694_);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v_msg_1693_);
return v___x_1702_;
}
else
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
lean_inc_ref(v_env_1699_);
v___x_1703_ = l_Lean_Environment_setExporting(v_env_1699_, v___x_1700_);
lean_inc(v_declHint_1694_);
lean_inc_ref(v___x_1703_);
v___x_1704_ = l_Lean_Environment_contains(v___x_1703_, v_declHint_1694_, v_isExporting_1701_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; 
lean_dec_ref(v___x_1703_);
lean_dec_ref(v_env_1699_);
lean_dec(v_declHint_1694_);
v___x_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1705_, 0, v_msg_1693_);
return v___x_1705_;
}
else
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v_c_1711_; lean_object* v___x_1712_; 
v___x_1706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2);
v___x_1707_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5);
v___x_1708_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1703_);
v___x_1709_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1703_);
lean_ctor_set(v___x_1709_, 1, v___x_1706_);
lean_ctor_set(v___x_1709_, 2, v___x_1707_);
lean_ctor_set(v___x_1709_, 3, v___x_1708_);
lean_inc(v_declHint_1694_);
v___x_1710_ = l_Lean_MessageData_ofConstName(v_declHint_1694_, v___x_1700_);
v_c_1711_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1711_, 0, v___x_1709_);
lean_ctor_set(v_c_1711_, 1, v___x_1710_);
v___x_1712_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1703_, v_declHint_1694_);
lean_dec_ref(v___x_1703_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec_ref(v_env_1699_);
lean_dec(v_declHint_1694_);
v___x_1713_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7);
v___x_1714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1714_, 0, v___x_1713_);
lean_ctor_set(v___x_1714_, 1, v_c_1711_);
v___x_1715_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9);
v___x_1716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1714_);
lean_ctor_set(v___x_1716_, 1, v___x_1715_);
v___x_1717_ = l_Lean_MessageData_note(v___x_1716_);
v___x_1718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_msg_1693_);
lean_ctor_set(v___x_1718_, 1, v___x_1717_);
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1718_);
return v___x_1719_;
}
else
{
lean_object* v_val_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1754_; 
v_val_1720_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1722_ = v___x_1712_;
v_isShared_1723_ = v_isSharedCheck_1754_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_val_1720_);
lean_dec(v___x_1712_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1754_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1724_; lean_object* v_moduleNames_1725_; lean_object* v_mod_1726_; uint8_t v___x_1727_; 
v___x_1724_ = l_Lean_Environment_header(v_env_1699_);
lean_dec_ref(v_env_1699_);
v_moduleNames_1725_ = lean_ctor_get(v___x_1724_, 4);
lean_inc_ref(v_moduleNames_1725_);
lean_dec_ref(v___x_1724_);
v_mod_1726_ = lean_array_get(v___x_1697_, v_moduleNames_1725_, v_val_1720_);
lean_dec(v_val_1720_);
lean_dec_ref(v_moduleNames_1725_);
v___x_1727_ = l_Lean_isPrivateName(v_declHint_1694_);
lean_dec(v_declHint_1694_);
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1728_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11);
v___x_1729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v_c_1711_);
v___x_1730_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1729_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = l_Lean_MessageData_ofName(v_mod_1726_);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15);
v___x_1735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v___x_1736_ = l_Lean_MessageData_note(v___x_1735_);
v___x_1737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1737_, 0, v_msg_1693_);
lean_ctor_set(v___x_1737_, 1, v___x_1736_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1737_);
v___x_1739_ = v___x_1722_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
else
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7);
v___x_1742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v_c_1711_);
v___x_1743_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = l_Lean_MessageData_ofName(v_mod_1726_);
v___x_1746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1746_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = l_Lean_MessageData_note(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v_msg_1693_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
if (v_isShared_1723_ == 0)
{
lean_ctor_set_tag(v___x_1722_, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1750_);
v___x_1752_ = v___x_1722_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
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
}
}
else
{
lean_object* v___x_1755_; 
lean_dec_ref(v_env_1699_);
lean_dec(v_declHint_1694_);
v___x_1755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_msg_1693_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___boxed(lean_object* v_msg_1756_, lean_object* v_declHint_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(v_msg_1756_, v_declHint_1757_, v___y_1758_);
lean_dec(v___y_1758_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(lean_object* v_msg_1761_, lean_object* v_declHint_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v___x_1768_; lean_object* v_a_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1778_; 
v___x_1768_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(v_msg_1761_, v_declHint_1762_, v___y_1766_);
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1768_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1771_ = v___x_1768_;
v_isShared_1772_ = v_isSharedCheck_1778_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_a_1769_);
lean_dec(v___x_1768_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1778_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1776_; 
v___x_1773_ = l_Lean_unknownIdentifierMessageTag;
v___x_1774_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
lean_ctor_set(v___x_1774_, 1, v_a_1769_);
if (v_isShared_1772_ == 0)
{
lean_ctor_set(v___x_1771_, 0, v___x_1774_);
v___x_1776_ = v___x_1771_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24___boxed(lean_object* v_msg_1779_, lean_object* v_declHint_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(v_msg_1779_, v_declHint_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(lean_object* v_ref_1787_, lean_object* v_msg_1788_, lean_object* v_declHint_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; lean_object* v_a_1796_; lean_object* v___x_1797_; 
v___x_1795_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(v_msg_1788_, v_declHint_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
v_a_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_a_1796_);
lean_dec_ref(v___x_1795_);
v___x_1797_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(v_ref_1787_, v_a_1796_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg___boxed(lean_object* v_ref_1798_, lean_object* v_msg_1799_, lean_object* v_declHint_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(v_ref_1798_, v_msg_1799_, v_declHint_1800_, v___y_1801_, v___y_1802_, v___y_1803_, v___y_1804_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v_ref_1798_);
return v_res_1806_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__0));
v___x_1809_ = l_Lean_stringToMessageData(v___x_1808_);
return v___x_1809_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
v___x_1811_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__2));
v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(lean_object* v_ref_1813_, lean_object* v_constName_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; uint8_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1820_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1);
v___x_1821_ = 0;
lean_inc(v_constName_1814_);
v___x_1822_ = l_Lean_MessageData_ofConstName(v_constName_1814_, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1820_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3);
v___x_1825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1823_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(v_ref_1813_, v___x_1825_, v_constName_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1827_, lean_object* v_constName_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(v_ref_1827_, v_constName_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v_ref_1827_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_ref_1841_; lean_object* v___x_1842_; 
v_ref_1841_ = lean_ctor_get(v___y_1838_, 2);
v___x_1842_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(v_ref_1841_, v_constName_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_1843_, v___y_1844_, v___y_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; lean_object* v_env_1857_; uint8_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1856_ = lean_st_ref_get(v___y_1854_);
v_env_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc_ref(v_env_1857_);
lean_dec(v___x_1856_);
v___x_1858_ = 0;
lean_inc(v_constName_1850_);
v___x_1859_ = l_Lean_Environment_findConstVal_x3f(v_env_1857_, v_constName_1850_, v___x_1858_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_);
return v___x_1860_;
}
else
{
lean_object* v_val_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_constName_1850_);
v_val_1861_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1859_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_val_1861_);
lean_dec(v___x_1859_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
lean_ctor_set_tag(v___x_1863_, 0);
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_val_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1875_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v___dummy_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg();
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object* v___y_1882_, uint8_t v_isExporting_1883_, lean_object* v___x_1884_, lean_object* v___y_1885_, lean_object* v___x_1886_, lean_object* v_a_x3f_1887_){
_start:
{
lean_object* v___x_1889_; lean_object* v_env_1890_; lean_object* v_nextMacroScope_1891_; lean_object* v_ngen_1892_; lean_object* v_auxDeclNGen_1893_; lean_object* v_traceState_1894_; lean_object* v_recordedDeps_1895_; lean_object* v_messages_1896_; lean_object* v_infoState_1897_; lean_object* v_snapshotTasks_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1923_; 
v___x_1889_ = lean_st_ref_take(v___y_1882_);
v_env_1890_ = lean_ctor_get(v___x_1889_, 0);
v_nextMacroScope_1891_ = lean_ctor_get(v___x_1889_, 1);
v_ngen_1892_ = lean_ctor_get(v___x_1889_, 2);
v_auxDeclNGen_1893_ = lean_ctor_get(v___x_1889_, 3);
v_traceState_1894_ = lean_ctor_get(v___x_1889_, 4);
v_recordedDeps_1895_ = lean_ctor_get(v___x_1889_, 6);
v_messages_1896_ = lean_ctor_get(v___x_1889_, 7);
v_infoState_1897_ = lean_ctor_get(v___x_1889_, 8);
v_snapshotTasks_1898_ = lean_ctor_get(v___x_1889_, 9);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1923_ == 0)
{
lean_object* v_unused_1924_; 
v_unused_1924_ = lean_ctor_get(v___x_1889_, 5);
lean_dec(v_unused_1924_);
v___x_1900_ = v___x_1889_;
v_isShared_1901_ = v_isSharedCheck_1923_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_snapshotTasks_1898_);
lean_inc(v_infoState_1897_);
lean_inc(v_messages_1896_);
lean_inc(v_recordedDeps_1895_);
lean_inc(v_traceState_1894_);
lean_inc(v_auxDeclNGen_1893_);
lean_inc(v_ngen_1892_);
lean_inc(v_nextMacroScope_1891_);
lean_inc(v_env_1890_);
lean_dec(v___x_1889_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1923_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = l_Lean_Environment_setExporting(v_env_1890_, v_isExporting_1883_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 5, v___x_1884_);
lean_ctor_set(v___x_1900_, 0, v___x_1902_);
v___x_1904_ = v___x_1900_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_nextMacroScope_1891_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_ngen_1892_);
lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_auxDeclNGen_1893_);
lean_ctor_set(v_reuseFailAlloc_1922_, 4, v_traceState_1894_);
lean_ctor_set(v_reuseFailAlloc_1922_, 5, v___x_1884_);
lean_ctor_set(v_reuseFailAlloc_1922_, 6, v_recordedDeps_1895_);
lean_ctor_set(v_reuseFailAlloc_1922_, 7, v_messages_1896_);
lean_ctor_set(v_reuseFailAlloc_1922_, 8, v_infoState_1897_);
lean_ctor_set(v_reuseFailAlloc_1922_, 9, v_snapshotTasks_1898_);
v___x_1904_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v_mctx_1907_; lean_object* v_zetaDeltaFVarIds_1908_; lean_object* v_postponed_1909_; lean_object* v_diag_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1920_; 
v___x_1905_ = lean_st_ref_put(v___y_1882_, v___x_1904_);
v___x_1906_ = lean_st_ref_take(v___y_1885_);
v_mctx_1907_ = lean_ctor_get(v___x_1906_, 0);
v_zetaDeltaFVarIds_1908_ = lean_ctor_get(v___x_1906_, 2);
v_postponed_1909_ = lean_ctor_get(v___x_1906_, 3);
v_diag_1910_ = lean_ctor_get(v___x_1906_, 4);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1920_ == 0)
{
lean_object* v_unused_1921_; 
v_unused_1921_ = lean_ctor_get(v___x_1906_, 1);
lean_dec(v_unused_1921_);
v___x_1912_ = v___x_1906_;
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_diag_1910_);
lean_inc(v_postponed_1909_);
lean_inc(v_zetaDeltaFVarIds_1908_);
lean_inc(v_mctx_1907_);
lean_dec(v___x_1906_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_box(0);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v___x_1886_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_mctx_1907_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1886_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_zetaDeltaFVarIds_1908_);
lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_postponed_1909_);
lean_ctor_set(v_reuseFailAlloc_1919_, 4, v_diag_1910_);
v___x_1916_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_st_ref_put(v___y_1885_, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1914_);
return v___x_1918_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object* v___y_1925_, lean_object* v_isExporting_1926_, lean_object* v___x_1927_, lean_object* v___y_1928_, lean_object* v___x_1929_, lean_object* v_a_x3f_1930_, lean_object* v___y_1931_){
_start:
{
uint8_t v_isExporting_boxed_1932_; lean_object* v_res_1933_; 
v_isExporting_boxed_1932_ = lean_unbox(v_isExporting_1926_);
v_res_1933_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_1925_, v_isExporting_boxed_1932_, v___x_1927_, v___y_1928_, v___x_1929_, v_a_x3f_1930_);
lean_dec(v_a_x3f_1930_);
lean_dec(v___y_1928_);
lean_dec(v___y_1925_);
return v_res_1933_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg();
return v___x_1938_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
return v___x_1940_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__4(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1943_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
lean_ctor_set(v___x_1943_, 2, v___x_1941_);
return v___x_1943_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1944_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__4, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__4_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__4);
v___x_1945_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
v___x_1946_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1947_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
v___x_1948_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
lean_ctor_set(v___x_1948_, 1, v___x_1946_);
lean_ctor_set(v___x_1948_, 2, v___x_1945_);
lean_ctor_set(v___x_1948_, 3, v___x_1946_);
lean_ctor_set(v___x_1948_, 4, v___x_1946_);
lean_ctor_set(v___x_1948_, 5, v___x_1946_);
lean_ctor_set(v___x_1948_, 6, v___x_1946_);
lean_ctor_set(v___x_1948_, 7, v___x_1944_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object* v_x_1949_, uint8_t v_isExporting_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v___x_1956_; lean_object* v_env_1957_; lean_object* v___x_1958_; uint8_t v_isModule_1959_; 
v___x_1956_ = lean_st_ref_get(v___y_1954_);
v_env_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc_ref(v_env_1957_);
lean_dec(v___x_1956_);
v___x_1958_ = l_Lean_Environment_header(v_env_1957_);
v_isModule_1959_ = lean_ctor_get_uint8(v___x_1958_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1958_);
if (v_isModule_1959_ == 0)
{
lean_object* v___x_1960_; 
lean_dec_ref(v_env_1957_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
v___x_1960_ = lean_apply_5(v_x_1949_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, lean_box(0));
return v___x_1960_;
}
else
{
uint8_t v_isExporting_1961_; 
v_isExporting_1961_ = lean_ctor_get_uint8(v_env_1957_, sizeof(void*)*13);
lean_dec_ref(v_env_1957_);
if (v_isExporting_1950_ == 0)
{
if (v_isExporting_1961_ == 0)
{
lean_object* v___x_2028_; 
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
v___x_2028_ = lean_apply_5(v_x_1949_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, lean_box(0));
return v___x_2028_;
}
else
{
goto v___jp_1962_;
}
}
else
{
if (v_isExporting_1961_ == 0)
{
goto v___jp_1962_;
}
else
{
lean_object* v___x_2029_; 
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
v___x_2029_ = lean_apply_5(v_x_1949_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, lean_box(0));
return v___x_2029_;
}
}
v___jp_1962_:
{
lean_object* v___x_1963_; lean_object* v_env_1964_; lean_object* v_nextMacroScope_1965_; lean_object* v_ngen_1966_; lean_object* v_auxDeclNGen_1967_; lean_object* v_traceState_1968_; lean_object* v_recordedDeps_1969_; lean_object* v_messages_1970_; lean_object* v_infoState_1971_; lean_object* v_snapshotTasks_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2026_; 
v___x_1963_ = lean_st_ref_take(v___y_1954_);
v_env_1964_ = lean_ctor_get(v___x_1963_, 0);
v_nextMacroScope_1965_ = lean_ctor_get(v___x_1963_, 1);
v_ngen_1966_ = lean_ctor_get(v___x_1963_, 2);
v_auxDeclNGen_1967_ = lean_ctor_get(v___x_1963_, 3);
v_traceState_1968_ = lean_ctor_get(v___x_1963_, 4);
v_recordedDeps_1969_ = lean_ctor_get(v___x_1963_, 6);
v_messages_1970_ = lean_ctor_get(v___x_1963_, 7);
v_infoState_1971_ = lean_ctor_get(v___x_1963_, 8);
v_snapshotTasks_1972_ = lean_ctor_get(v___x_1963_, 9);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; 
v_unused_2027_ = lean_ctor_get(v___x_1963_, 5);
lean_dec(v_unused_2027_);
v___x_1974_ = v___x_1963_;
v_isShared_1975_ = v_isSharedCheck_2026_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_snapshotTasks_1972_);
lean_inc(v_infoState_1971_);
lean_inc(v_messages_1970_);
lean_inc(v_recordedDeps_1969_);
lean_inc(v_traceState_1968_);
lean_inc(v_auxDeclNGen_1967_);
lean_inc(v_ngen_1966_);
lean_inc(v_nextMacroScope_1965_);
lean_inc(v_env_1964_);
lean_dec(v___x_1963_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2026_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1976_ = l_Lean_Environment_setExporting(v_env_1964_, v_isExporting_1950_);
v___x_1977_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 5, v___x_1977_);
lean_ctor_set(v___x_1974_, 0, v___x_1976_);
v___x_1979_ = v___x_1974_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_nextMacroScope_1965_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_ngen_1966_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_auxDeclNGen_1967_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v_traceState_1968_);
lean_ctor_set(v_reuseFailAlloc_2025_, 5, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_2025_, 6, v_recordedDeps_1969_);
lean_ctor_set(v_reuseFailAlloc_2025_, 7, v_messages_1970_);
lean_ctor_set(v_reuseFailAlloc_2025_, 8, v_infoState_1971_);
lean_ctor_set(v_reuseFailAlloc_2025_, 9, v_snapshotTasks_1972_);
v___x_1979_ = v_reuseFailAlloc_2025_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v_mctx_1982_; lean_object* v_zetaDeltaFVarIds_1983_; lean_object* v_postponed_1984_; lean_object* v_diag_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_2023_; 
v___x_1980_ = lean_st_ref_put(v___y_1954_, v___x_1979_);
v___x_1981_ = lean_st_ref_take(v___y_1952_);
v_mctx_1982_ = lean_ctor_get(v___x_1981_, 0);
v_zetaDeltaFVarIds_1983_ = lean_ctor_get(v___x_1981_, 2);
v_postponed_1984_ = lean_ctor_get(v___x_1981_, 3);
v_diag_1985_ = lean_ctor_get(v___x_1981_, 4);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v___x_1981_, 1);
lean_dec(v_unused_2024_);
v___x_1987_ = v___x_1981_;
v_isShared_1988_ = v_isSharedCheck_2023_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_diag_1985_);
lean_inc(v_postponed_1984_);
lean_inc(v_zetaDeltaFVarIds_1983_);
lean_inc(v_mctx_1982_);
lean_dec(v___x_1981_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_2023_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1989_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5);
if (v_isShared_1988_ == 0)
{
lean_ctor_set(v___x_1987_, 1, v___x_1989_);
v___x_1991_ = v___x_1987_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_mctx_1982_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_zetaDeltaFVarIds_1983_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_postponed_1984_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_diag_1985_);
v___x_1991_ = v_reuseFailAlloc_2022_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; lean_object* v_r_1993_; 
v___x_1992_ = lean_st_ref_put(v___y_1952_, v___x_1991_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v___y_1952_);
lean_inc_ref(v___y_1951_);
v_r_1993_ = lean_apply_5(v_x_1949_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_, lean_box(0));
if (lean_obj_tag(v_r_1993_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2010_; 
v_a_1994_ = lean_ctor_get(v_r_1993_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_r_1993_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1996_ = v_r_1993_;
v_isShared_1997_ = v_isSharedCheck_2010_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v_r_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2010_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
lean_inc(v_a_1994_);
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 1);
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
v___x_2000_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_1954_, v_isExporting_1961_, v___x_1977_, v___y_1952_, v___x_1989_, v___x_1999_);
lean_dec_ref(v___x_1999_);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; 
v_unused_2008_ = lean_ctor_get(v___x_2000_, 0);
lean_dec(v_unused_2008_);
v___x_2002_ = v___x_2000_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_dec(v___x_2000_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v_a_1994_);
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_1994_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
v_a_2011_ = lean_ctor_get(v_r_1993_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v_r_1993_, 1);
v___x_2012_ = lean_box(0);
v___x_2013_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_1954_, v_isExporting_1961_, v___x_1977_, v___y_1952_, v___x_1989_, v___x_2012_);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v___x_2013_, 0);
lean_dec(v_unused_2021_);
v___x_2015_ = v___x_2013_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_dec(v___x_2013_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
lean_ctor_set_tag(v___x_2015_, 1);
lean_ctor_set(v___x_2015_, 0, v_a_2011_);
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2011_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_2030_, lean_object* v_isExporting_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
uint8_t v_isExporting_boxed_2037_; lean_object* v_res_2038_; 
v_isExporting_boxed_2037_ = lean_unbox(v_isExporting_2031_);
v_res_2038_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_2030_, v_isExporting_boxed_2037_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
lean_dec(v___y_2033_);
lean_dec_ref(v___y_2032_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___lam__0(lean_object* v_addEntryFn_2039_, lean_object* v_decl_2040_, lean_object* v_s_2041_){
_start:
{
lean_object* v_importedEntries_2042_; lean_object* v_state_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2051_; 
v_importedEntries_2042_ = lean_ctor_get(v_s_2041_, 0);
v_state_2043_ = lean_ctor_get(v_s_2041_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_s_2041_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2045_ = v_s_2041_;
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_state_2043_);
lean_inc(v_importedEntries_2042_);
lean_dec(v_s_2041_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v_state_2047_; lean_object* v___x_2049_; 
v_state_2047_ = lean_apply_2(v_addEntryFn_2039_, v_state_2043_, v_decl_2040_);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 1, v_state_2047_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_importedEntries_2042_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_state_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__0));
v___x_2054_ = l_Lean_stringToMessageData(v___x_2053_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__2));
v___x_2057_ = l_Lean_stringToMessageData(v___x_2056_);
return v___x_2057_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2059_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__4));
v___x_2060_ = l_Lean_stringToMessageData(v___x_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_attrName_2061_, lean_object* v_declName_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2068_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1);
v___x_2069_ = l_Lean_MessageData_ofName(v_attrName_2061_);
v___x_2070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2068_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
v___x_2071_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3);
v___x_2072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2070_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
v___x_2073_ = 0;
v___x_2074_ = l_Lean_MessageData_ofConstName(v_declName_2062_, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2072_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5);
v___x_2077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2077_, 0, v___x_2075_);
lean_ctor_set(v___x_2077_, 1, v___x_2076_);
v___x_2078_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_2077_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_attrName_2079_, lean_object* v_declName_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_attrName_2079_, v_declName_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
return v_res_2086_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__0));
v___x_2089_ = l_Lean_stringToMessageData(v___x_2088_);
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__2));
v___x_2092_ = l_Lean_stringToMessageData(v___x_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(lean_object* v_attrName_2093_, lean_object* v_declName_2094_, lean_object* v_asyncPrefix_x3f_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___y_2102_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2095_) == 0)
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_MessageData_nil;
v___y_2102_ = v___x_2115_;
goto v___jp_2101_;
}
else
{
lean_object* v_val_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_val_2116_ = lean_ctor_get(v_asyncPrefix_x3f_2095_, 0);
lean_inc(v_val_2116_);
lean_dec_ref_known(v_asyncPrefix_x3f_2095_, 1);
v___x_2117_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3);
v___x_2118_ = l_Lean_MessageData_ofName(v_val_2116_);
v___x_2119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2117_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
v___x_2120_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3);
v___x_2121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2119_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
v___y_2102_ = v___x_2121_;
goto v___jp_2101_;
}
v___jp_2101_:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2103_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1);
v___x_2104_ = l_Lean_MessageData_ofName(v_attrName_2093_);
v___x_2105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2103_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3);
v___x_2107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2105_);
lean_ctor_set(v___x_2107_, 1, v___x_2106_);
v___x_2108_ = 0;
v___x_2109_ = l_Lean_MessageData_ofConstName(v_declName_2094_, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2107_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1);
v___x_2112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2110_);
lean_ctor_set(v___x_2112_, 1, v___x_2111_);
v___x_2113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
lean_ctor_set(v___x_2113_, 1, v___y_2102_);
v___x_2114_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_2113_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
return v___x_2114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___boxed(lean_object* v_attrName_2122_, lean_object* v_declName_2123_, lean_object* v_asyncPrefix_x3f_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(v_attrName_2122_, v_declName_2123_, v_asyncPrefix_x3f_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_attr_2131_, lean_object* v_decl_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___y_2139_; lean_object* v___y_2140_; lean_object* v___y_2141_; lean_object* v___y_2142_; lean_object* v___y_2143_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; lean_object* v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___x_2193_; lean_object* v_env_2194_; lean_object* v___y_2196_; lean_object* v___y_2197_; lean_object* v___y_2198_; lean_object* v___y_2199_; lean_object* v___x_2209_; 
v___x_2193_ = lean_st_ref_get(v___y_2136_);
v_env_2194_ = lean_ctor_get(v___x_2193_, 0);
lean_inc_ref(v_env_2194_);
lean_dec(v___x_2193_);
v___x_2209_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2194_, v_decl_2132_);
if (lean_obj_tag(v___x_2209_) == 0)
{
v___y_2196_ = v___y_2133_;
v___y_2197_ = v___y_2134_;
v___y_2198_ = v___y_2135_;
v___y_2199_ = v___y_2136_;
goto v___jp_2195_;
}
else
{
lean_object* v_attr_2210_; lean_object* v_toAttributeImplCore_2211_; lean_object* v_name_2212_; lean_object* v___x_2213_; 
lean_dec_ref_known(v___x_2209_, 1);
lean_dec_ref(v_env_2194_);
v_attr_2210_ = lean_ctor_get(v_attr_2131_, 0);
lean_inc_ref(v_attr_2210_);
lean_dec_ref(v_attr_2131_);
v_toAttributeImplCore_2211_ = lean_ctor_get(v_attr_2210_, 0);
lean_inc_ref(v_toAttributeImplCore_2211_);
lean_dec_ref(v_attr_2210_);
v_name_2212_ = lean_ctor_get(v_toAttributeImplCore_2211_, 1);
lean_inc(v_name_2212_);
lean_dec_ref(v_toAttributeImplCore_2211_);
v___x_2213_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_name_2212_, v_decl_2132_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
return v___x_2213_;
}
v___jp_2138_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v_mctx_2154_; lean_object* v_zetaDeltaFVarIds_2155_; lean_object* v_postponed_2156_; lean_object* v_diag_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2168_; 
v___x_2150_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_2151_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2151_, 0, v___y_2149_);
lean_ctor_set(v___x_2151_, 1, v___y_2141_);
lean_ctor_set(v___x_2151_, 2, v___y_2142_);
lean_ctor_set(v___x_2151_, 3, v___y_2146_);
lean_ctor_set(v___x_2151_, 4, v___y_2140_);
lean_ctor_set(v___x_2151_, 5, v___x_2150_);
lean_ctor_set(v___x_2151_, 6, v___y_2144_);
lean_ctor_set(v___x_2151_, 7, v___y_2139_);
lean_ctor_set(v___x_2151_, 8, v___y_2145_);
lean_ctor_set(v___x_2151_, 9, v___y_2143_);
v___x_2152_ = lean_st_ref_put(v___y_2147_, v___x_2151_);
v___x_2153_ = lean_st_ref_take(v___y_2148_);
v_mctx_2154_ = lean_ctor_get(v___x_2153_, 0);
v_zetaDeltaFVarIds_2155_ = lean_ctor_get(v___x_2153_, 2);
v_postponed_2156_ = lean_ctor_get(v___x_2153_, 3);
v_diag_2157_ = lean_ctor_get(v___x_2153_, 4);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2168_ == 0)
{
lean_object* v_unused_2169_; 
v_unused_2169_ = lean_ctor_get(v___x_2153_, 1);
lean_dec(v_unused_2169_);
v___x_2159_ = v___x_2153_;
v_isShared_2160_ = v_isSharedCheck_2168_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_diag_2157_);
lean_inc(v_postponed_2156_);
lean_inc(v_zetaDeltaFVarIds_2155_);
lean_inc(v_mctx_2154_);
lean_dec(v___x_2153_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2168_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2161_ = lean_box(0);
v___x_2162_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v___x_2162_);
v___x_2164_ = v___x_2159_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_mctx_2154_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2167_, 2, v_zetaDeltaFVarIds_2155_);
lean_ctor_set(v_reuseFailAlloc_2167_, 3, v_postponed_2156_);
lean_ctor_set(v_reuseFailAlloc_2167_, 4, v_diag_2157_);
v___x_2164_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_st_ref_put(v___y_2148_, v___x_2164_);
v___x_2166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2161_);
return v___x_2166_;
}
}
}
v___jp_2170_:
{
lean_object* v___x_2173_; lean_object* v_ext_2174_; lean_object* v_toEnvExtension_2175_; lean_object* v_env_2176_; lean_object* v_nextMacroScope_2177_; lean_object* v_ngen_2178_; lean_object* v_auxDeclNGen_2179_; lean_object* v_traceState_2180_; lean_object* v_recordedDeps_2181_; lean_object* v_messages_2182_; lean_object* v_infoState_2183_; lean_object* v_snapshotTasks_2184_; lean_object* v_addEntryFn_2185_; lean_object* v_asyncMode_2186_; uint8_t v_logWrites_2187_; lean_object* v___f_2188_; uint8_t v___x_2189_; 
v___x_2173_ = lean_st_ref_take(v___y_2172_);
v_ext_2174_ = lean_ctor_get(v_attr_2131_, 1);
lean_inc_ref(v_ext_2174_);
lean_dec_ref(v_attr_2131_);
v_toEnvExtension_2175_ = lean_ctor_get(v_ext_2174_, 0);
lean_inc_ref(v_toEnvExtension_2175_);
v_env_2176_ = lean_ctor_get(v___x_2173_, 0);
lean_inc_ref(v_env_2176_);
v_nextMacroScope_2177_ = lean_ctor_get(v___x_2173_, 1);
lean_inc(v_nextMacroScope_2177_);
v_ngen_2178_ = lean_ctor_get(v___x_2173_, 2);
lean_inc_ref(v_ngen_2178_);
v_auxDeclNGen_2179_ = lean_ctor_get(v___x_2173_, 3);
lean_inc_ref(v_auxDeclNGen_2179_);
v_traceState_2180_ = lean_ctor_get(v___x_2173_, 4);
lean_inc_ref(v_traceState_2180_);
v_recordedDeps_2181_ = lean_ctor_get(v___x_2173_, 6);
lean_inc_ref(v_recordedDeps_2181_);
v_messages_2182_ = lean_ctor_get(v___x_2173_, 7);
lean_inc_ref(v_messages_2182_);
v_infoState_2183_ = lean_ctor_get(v___x_2173_, 8);
lean_inc_ref(v_infoState_2183_);
v_snapshotTasks_2184_ = lean_ctor_get(v___x_2173_, 9);
lean_inc_ref(v_snapshotTasks_2184_);
lean_dec(v___x_2173_);
v_addEntryFn_2185_ = lean_ctor_get(v_ext_2174_, 3);
lean_inc(v_addEntryFn_2185_);
lean_dec_ref(v_ext_2174_);
v_asyncMode_2186_ = lean_ctor_get(v_toEnvExtension_2175_, 2);
lean_inc(v_asyncMode_2186_);
v_logWrites_2187_ = lean_ctor_get_uint8(v_toEnvExtension_2175_, sizeof(void*)*6);
lean_inc(v_decl_2132_);
v___f_2188_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___lam__0), 3, 2);
lean_closure_set(v___f_2188_, 0, v_addEntryFn_2185_);
lean_closure_set(v___f_2188_, 1, v_decl_2132_);
v___x_2189_ = 1;
if (v_logWrites_2187_ == 0)
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2175_, v_env_2176_, v___f_2188_, v_asyncMode_2186_, v_decl_2132_, v___x_2189_);
lean_dec(v_asyncMode_2186_);
v___y_2139_ = v_messages_2182_;
v___y_2140_ = v_traceState_2180_;
v___y_2141_ = v_nextMacroScope_2177_;
v___y_2142_ = v_ngen_2178_;
v___y_2143_ = v_snapshotTasks_2184_;
v___y_2144_ = v_recordedDeps_2181_;
v___y_2145_ = v_infoState_2183_;
v___y_2146_ = v_auxDeclNGen_2179_;
v___y_2147_ = v___y_2172_;
v___y_2148_ = v___y_2171_;
v___y_2149_ = v___x_2190_;
goto v___jp_2138_;
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_inc_ref(v_toEnvExtension_2175_);
v___x_2191_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2175_, v_env_2176_);
lean_dec_ref(v_env_2176_);
v___x_2192_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2175_, v___x_2191_, v___f_2188_, v_asyncMode_2186_, v_decl_2132_, v___x_2189_);
lean_dec(v_asyncMode_2186_);
v___y_2139_ = v_messages_2182_;
v___y_2140_ = v_traceState_2180_;
v___y_2141_ = v_nextMacroScope_2177_;
v___y_2142_ = v_ngen_2178_;
v___y_2143_ = v_snapshotTasks_2184_;
v___y_2144_ = v_recordedDeps_2181_;
v___y_2145_ = v_infoState_2183_;
v___y_2146_ = v_auxDeclNGen_2179_;
v___y_2147_ = v___y_2172_;
v___y_2148_ = v___y_2171_;
v___y_2149_ = v___x_2192_;
goto v___jp_2138_;
}
}
v___jp_2195_:
{
lean_object* v_ext_2200_; lean_object* v_toEnvExtension_2201_; lean_object* v_attr_2202_; lean_object* v_asyncMode_2203_; uint8_t v___x_2204_; 
v_ext_2200_ = lean_ctor_get(v_attr_2131_, 1);
v_toEnvExtension_2201_ = lean_ctor_get(v_ext_2200_, 0);
v_attr_2202_ = lean_ctor_get(v_attr_2131_, 0);
v_asyncMode_2203_ = lean_ctor_get(v_toEnvExtension_2201_, 2);
lean_inc(v_decl_2132_);
lean_inc_ref(v_env_2194_);
v___x_2204_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2194_, v_decl_2132_, v_asyncMode_2203_);
if (v___x_2204_ == 0)
{
lean_object* v_toAttributeImplCore_2205_; lean_object* v_name_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_inc_ref(v_attr_2202_);
lean_dec_ref(v_attr_2131_);
v_toAttributeImplCore_2205_ = lean_ctor_get(v_attr_2202_, 0);
lean_inc_ref(v_toAttributeImplCore_2205_);
lean_dec_ref(v_attr_2202_);
v_name_2206_ = lean_ctor_get(v_toAttributeImplCore_2205_, 1);
lean_inc(v_name_2206_);
lean_dec_ref(v_toAttributeImplCore_2205_);
v___x_2207_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2194_);
v___x_2208_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(v_name_2206_, v_decl_2132_, v___x_2207_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
return v___x_2208_;
}
else
{
lean_dec_ref(v_env_2194_);
v___y_2171_ = v___y_2197_;
v___y_2172_ = v___y_2199_;
goto v___jp_2170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_attr_2214_, lean_object* v_decl_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_attr_2214_, v_decl_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v_env_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; 
v___x_2228_ = lean_st_ref_get(v___y_2226_);
v_env_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc_ref(v_env_2229_);
lean_dec(v___x_2228_);
v___x_2230_ = 0;
lean_inc(v_constName_2222_);
v___x_2231_ = l_Lean_Environment_find_x3f(v_env_2229_, v_constName_2222_, v___x_2230_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_);
return v___x_2232_;
}
else
{
lean_object* v_val_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
lean_dec(v_constName_2222_);
v_val_2233_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2231_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_val_2233_);
lean_dec(v___x_2231_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
lean_ctor_set_tag(v___x_2235_, 0);
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_val_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(lean_object* v_declName_2248_, uint8_t v_s_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v_env_2254_; lean_object* v_nextMacroScope_2255_; lean_object* v_ngen_2256_; lean_object* v_auxDeclNGen_2257_; lean_object* v_traceState_2258_; lean_object* v_recordedDeps_2259_; lean_object* v_messages_2260_; lean_object* v_infoState_2261_; lean_object* v_snapshotTasks_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2291_; 
v___x_2253_ = lean_st_ref_take(v___y_2251_);
v_env_2254_ = lean_ctor_get(v___x_2253_, 0);
v_nextMacroScope_2255_ = lean_ctor_get(v___x_2253_, 1);
v_ngen_2256_ = lean_ctor_get(v___x_2253_, 2);
v_auxDeclNGen_2257_ = lean_ctor_get(v___x_2253_, 3);
v_traceState_2258_ = lean_ctor_get(v___x_2253_, 4);
v_recordedDeps_2259_ = lean_ctor_get(v___x_2253_, 6);
v_messages_2260_ = lean_ctor_get(v___x_2253_, 7);
v_infoState_2261_ = lean_ctor_get(v___x_2253_, 8);
v_snapshotTasks_2262_ = lean_ctor_get(v___x_2253_, 9);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v___x_2253_, 5);
lean_dec(v_unused_2292_);
v___x_2264_ = v___x_2253_;
v_isShared_2265_ = v_isSharedCheck_2291_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_snapshotTasks_2262_);
lean_inc(v_infoState_2261_);
lean_inc(v_messages_2260_);
lean_inc(v_recordedDeps_2259_);
lean_inc(v_traceState_2258_);
lean_inc(v_auxDeclNGen_2257_);
lean_inc(v_ngen_2256_);
lean_inc(v_nextMacroScope_2255_);
lean_inc(v_env_2254_);
lean_dec(v___x_2253_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2291_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
uint8_t v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2266_ = 0;
v___x_2267_ = lean_box(0);
v___x_2268_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2254_, v_declName_2248_, v_s_2249_, v___x_2266_, v___x_2267_);
v___x_2269_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 5, v___x_2269_);
lean_ctor_set(v___x_2264_, 0, v___x_2268_);
v___x_2271_ = v___x_2264_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2268_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_nextMacroScope_2255_);
lean_ctor_set(v_reuseFailAlloc_2290_, 2, v_ngen_2256_);
lean_ctor_set(v_reuseFailAlloc_2290_, 3, v_auxDeclNGen_2257_);
lean_ctor_set(v_reuseFailAlloc_2290_, 4, v_traceState_2258_);
lean_ctor_set(v_reuseFailAlloc_2290_, 5, v___x_2269_);
lean_ctor_set(v_reuseFailAlloc_2290_, 6, v_recordedDeps_2259_);
lean_ctor_set(v_reuseFailAlloc_2290_, 7, v_messages_2260_);
lean_ctor_set(v_reuseFailAlloc_2290_, 8, v_infoState_2261_);
lean_ctor_set(v_reuseFailAlloc_2290_, 9, v_snapshotTasks_2262_);
v___x_2271_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v_mctx_2274_; lean_object* v_zetaDeltaFVarIds_2275_; lean_object* v_postponed_2276_; lean_object* v_diag_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2288_; 
v___x_2272_ = lean_st_ref_put(v___y_2251_, v___x_2271_);
v___x_2273_ = lean_st_ref_take(v___y_2250_);
v_mctx_2274_ = lean_ctor_get(v___x_2273_, 0);
v_zetaDeltaFVarIds_2275_ = lean_ctor_get(v___x_2273_, 2);
v_postponed_2276_ = lean_ctor_get(v___x_2273_, 3);
v_diag_2277_ = lean_ctor_get(v___x_2273_, 4);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2288_ == 0)
{
lean_object* v_unused_2289_; 
v_unused_2289_ = lean_ctor_get(v___x_2273_, 1);
lean_dec(v_unused_2289_);
v___x_2279_ = v___x_2273_;
v_isShared_2280_ = v_isSharedCheck_2288_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_diag_2277_);
lean_inc(v_postponed_2276_);
lean_inc(v_zetaDeltaFVarIds_2275_);
lean_inc(v_mctx_2274_);
lean_dec(v___x_2273_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2288_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2281_ = lean_box(0);
v___x_2282_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 1, v___x_2282_);
v___x_2284_ = v___x_2279_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_mctx_2274_);
lean_ctor_set(v_reuseFailAlloc_2287_, 1, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2287_, 2, v_zetaDeltaFVarIds_2275_);
lean_ctor_set(v_reuseFailAlloc_2287_, 3, v_postponed_2276_);
lean_ctor_set(v_reuseFailAlloc_2287_, 4, v_diag_2277_);
v___x_2284_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_st_ref_put(v___y_2250_, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2281_);
return v___x_2286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg___boxed(lean_object* v_declName_2293_, lean_object* v_s_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
uint8_t v_s_boxed_2298_; lean_object* v_res_2299_; 
v_s_boxed_2298_ = lean_unbox(v_s_2294_);
v_res_2299_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(v_declName_2293_, v_s_boxed_2298_, v___y_2295_, v___y_2296_);
lean_dec(v___y_2296_);
lean_dec(v___y_2295_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_declName_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = 0;
v___x_2307_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(v_declName_2300_, v___x_2306_, v___y_2302_, v___y_2304_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_declName_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_declName_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
return v_res_2314_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2318_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2319_ = lean_unsigned_to_nat(58u);
v___x_2320_ = lean_unsigned_to_nat(33u);
v___x_2321_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2322_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2323_ = l_mkPanicMessageWithDecl(v___x_2322_, v___x_2321_, v___x_2320_, v___x_2319_, v___x_2318_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2325_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2326_ = lean_unsigned_to_nat(60u);
v___x_2327_ = lean_unsigned_to_nat(30u);
v___x_2328_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2329_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2330_ = l_mkPanicMessageWithDecl(v___x_2329_, v___x_2328_, v___x_2327_, v___x_2326_, v___x_2325_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2331_, lean_object* v_indName_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v___x_2338_; 
lean_inc(v_indName_2332_);
v___x_2338_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2332_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
if (lean_obj_tag(v_a_2339_) == 5)
{
lean_object* v_val_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2530_; 
v_val_2340_ = lean_ctor_get(v_a_2339_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_a_2339_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2342_ = v_a_2339_;
v_isShared_2343_ = v_isSharedCheck_2530_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_val_2340_);
lean_dec(v_a_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2530_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
lean_inc(v_indName_2332_);
v___x_2344_ = l_Lean_mkCasesOnName(v_indName_2332_);
lean_inc(v___x_2344_);
v___x_2345_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2344_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v_name_2347_; lean_object* v_levelParams_2348_; lean_object* v_type_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v_name_2347_ = lean_ctor_get(v_a_2346_, 0);
lean_inc(v_name_2347_);
v_levelParams_2348_ = lean_ctor_get(v_a_2346_, 1);
lean_inc_n(v_levelParams_2348_, 2);
v_type_2349_ = lean_ctor_get(v_a_2346_, 2);
lean_inc_ref(v_type_2349_);
lean_dec(v_a_2346_);
v___x_2350_ = lean_box(0);
v___x_2351_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2348_, v___x_2350_);
if (lean_obj_tag(v___x_2351_) == 1)
{
lean_object* v_head_2352_; lean_object* v_tail_2353_; lean_object* v_numParams_2354_; lean_object* v_numIndices_2355_; lean_object* v_ctors_2356_; lean_object* v___f_2357_; lean_object* v___x_2359_; 
v_head_2352_ = lean_ctor_get(v___x_2351_, 0);
lean_inc(v_head_2352_);
v_tail_2353_ = lean_ctor_get(v___x_2351_, 1);
lean_inc(v_tail_2353_);
v_numParams_2354_ = lean_ctor_get(v_val_2340_, 1);
lean_inc_n(v_numParams_2354_, 2);
v_numIndices_2355_ = lean_ctor_get(v_val_2340_, 2);
lean_inc(v_numIndices_2355_);
v_ctors_2356_ = lean_ctor_get(v_val_2340_, 4);
lean_inc(v_ctors_2356_);
v___f_2357_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2357_, 0, v_numIndices_2355_);
lean_closure_set(v___f_2357_, 1, v_head_2352_);
lean_closure_set(v___f_2357_, 2, v_ctors_2356_);
lean_closure_set(v___f_2357_, 3, v_indName_2332_);
lean_closure_set(v___f_2357_, 4, v_tail_2353_);
lean_closure_set(v___f_2357_, 5, v_name_2347_);
lean_closure_set(v___f_2357_, 6, v___x_2351_);
lean_closure_set(v___f_2357_, 7, v_numParams_2354_);
lean_closure_set(v___f_2357_, 8, v_val_2340_);
lean_closure_set(v___f_2357_, 9, v___x_2344_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set_tag(v___x_2342_, 1);
lean_ctor_set(v___x_2342_, 0, v_numParams_2354_);
v___x_2359_ = v___x_2342_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_numParams_2354_);
v___x_2359_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
uint8_t v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = 0;
v___x_2361_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2349_, v___x_2359_, v___f_2357_, v___x_2360_, v___x_2360_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; lean_object* v___f_2364_; uint8_t v___y_2366_; uint8_t v___x_2509_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = lean_box(v___x_2360_);
lean_inc(v_declName_2331_);
v___f_2364_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2364_, 0, v_a_2362_);
lean_closure_set(v___f_2364_, 1, v_declName_2331_);
lean_closure_set(v___f_2364_, 2, v_levelParams_2348_);
lean_closure_set(v___f_2364_, 3, v___x_2363_);
v___x_2509_ = l_Lean_isPrivateName(v_declName_2331_);
if (v___x_2509_ == 0)
{
uint8_t v___x_2510_; 
v___x_2510_ = 1;
v___y_2366_ = v___x_2510_;
goto v___jp_2365_;
}
else
{
v___y_2366_ = v___x_2360_;
goto v___jp_2365_;
}
v___jp_2365_:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2364_, v___y_2366_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v___x_2368_; lean_object* v_env_2369_; lean_object* v_nextMacroScope_2370_; lean_object* v_ngen_2371_; lean_object* v_auxDeclNGen_2372_; lean_object* v_traceState_2373_; lean_object* v_recordedDeps_2374_; lean_object* v_messages_2375_; lean_object* v_infoState_2376_; lean_object* v_snapshotTasks_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2507_; 
lean_dec_ref_known(v___x_2367_, 1);
v___x_2368_ = lean_st_ref_take(v_a_2336_);
v_env_2369_ = lean_ctor_get(v___x_2368_, 0);
v_nextMacroScope_2370_ = lean_ctor_get(v___x_2368_, 1);
v_ngen_2371_ = lean_ctor_get(v___x_2368_, 2);
v_auxDeclNGen_2372_ = lean_ctor_get(v___x_2368_, 3);
v_traceState_2373_ = lean_ctor_get(v___x_2368_, 4);
v_recordedDeps_2374_ = lean_ctor_get(v___x_2368_, 6);
v_messages_2375_ = lean_ctor_get(v___x_2368_, 7);
v_infoState_2376_ = lean_ctor_get(v___x_2368_, 8);
v_snapshotTasks_2377_ = lean_ctor_get(v___x_2368_, 9);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v___x_2368_, 5);
lean_dec(v_unused_2508_);
v___x_2379_ = v___x_2368_;
v_isShared_2380_ = v_isSharedCheck_2507_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_snapshotTasks_2377_);
lean_inc(v_infoState_2376_);
lean_inc(v_messages_2375_);
lean_inc(v_recordedDeps_2374_);
lean_inc(v_traceState_2373_);
lean_inc(v_auxDeclNGen_2372_);
lean_inc(v_ngen_2371_);
lean_inc(v_nextMacroScope_2370_);
lean_inc(v_env_2369_);
lean_dec(v___x_2368_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2507_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
lean_inc(v_declName_2331_);
v___x_2381_ = l_Lean_Meta_markMatcherLike(v_env_2369_, v_declName_2331_);
v___x_2382_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 5, v___x_2382_);
lean_ctor_set(v___x_2379_, 0, v___x_2381_);
v___x_2384_ = v___x_2379_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2506_, 1, v_nextMacroScope_2370_);
lean_ctor_set(v_reuseFailAlloc_2506_, 2, v_ngen_2371_);
lean_ctor_set(v_reuseFailAlloc_2506_, 3, v_auxDeclNGen_2372_);
lean_ctor_set(v_reuseFailAlloc_2506_, 4, v_traceState_2373_);
lean_ctor_set(v_reuseFailAlloc_2506_, 5, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2506_, 6, v_recordedDeps_2374_);
lean_ctor_set(v_reuseFailAlloc_2506_, 7, v_messages_2375_);
lean_ctor_set(v_reuseFailAlloc_2506_, 8, v_infoState_2376_);
lean_ctor_set(v_reuseFailAlloc_2506_, 9, v_snapshotTasks_2377_);
v___x_2384_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v_mctx_2387_; lean_object* v_zetaDeltaFVarIds_2388_; lean_object* v_postponed_2389_; lean_object* v_diag_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2504_; 
v___x_2385_ = lean_st_ref_put(v_a_2336_, v___x_2384_);
v___x_2386_ = lean_st_ref_take(v_a_2334_);
v_mctx_2387_ = lean_ctor_get(v___x_2386_, 0);
v_zetaDeltaFVarIds_2388_ = lean_ctor_get(v___x_2386_, 2);
v_postponed_2389_ = lean_ctor_get(v___x_2386_, 3);
v_diag_2390_ = lean_ctor_get(v___x_2386_, 4);
v_isSharedCheck_2504_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2504_ == 0)
{
lean_object* v_unused_2505_; 
v_unused_2505_ = lean_ctor_get(v___x_2386_, 1);
lean_dec(v_unused_2505_);
v___x_2392_ = v___x_2386_;
v_isShared_2393_ = v_isSharedCheck_2504_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_diag_2390_);
lean_inc(v_postponed_2389_);
lean_inc(v_zetaDeltaFVarIds_2388_);
lean_inc(v_mctx_2387_);
lean_dec(v___x_2386_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2504_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2394_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5);
if (v_isShared_2393_ == 0)
{
lean_ctor_set(v___x_2392_, 1, v___x_2394_);
v___x_2396_ = v___x_2392_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2503_; 
v_reuseFailAlloc_2503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2503_, 0, v_mctx_2387_);
lean_ctor_set(v_reuseFailAlloc_2503_, 1, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2503_, 2, v_zetaDeltaFVarIds_2388_);
lean_ctor_set(v_reuseFailAlloc_2503_, 3, v_postponed_2389_);
lean_ctor_set(v_reuseFailAlloc_2503_, 4, v_diag_2390_);
v___x_2396_ = v_reuseFailAlloc_2503_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v_env_2399_; lean_object* v_nextMacroScope_2400_; lean_object* v_ngen_2401_; lean_object* v_auxDeclNGen_2402_; lean_object* v_traceState_2403_; lean_object* v_recordedDeps_2404_; lean_object* v_messages_2405_; lean_object* v_infoState_2406_; lean_object* v_snapshotTasks_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2501_; 
v___x_2397_ = lean_st_ref_put(v_a_2334_, v___x_2396_);
v___x_2398_ = lean_st_ref_take(v_a_2336_);
v_env_2399_ = lean_ctor_get(v___x_2398_, 0);
v_nextMacroScope_2400_ = lean_ctor_get(v___x_2398_, 1);
v_ngen_2401_ = lean_ctor_get(v___x_2398_, 2);
v_auxDeclNGen_2402_ = lean_ctor_get(v___x_2398_, 3);
v_traceState_2403_ = lean_ctor_get(v___x_2398_, 4);
v_recordedDeps_2404_ = lean_ctor_get(v___x_2398_, 6);
v_messages_2405_ = lean_ctor_get(v___x_2398_, 7);
v_infoState_2406_ = lean_ctor_get(v___x_2398_, 8);
v_snapshotTasks_2407_ = lean_ctor_get(v___x_2398_, 9);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2501_ == 0)
{
lean_object* v_unused_2502_; 
v_unused_2502_ = lean_ctor_get(v___x_2398_, 5);
lean_dec(v_unused_2502_);
v___x_2409_ = v___x_2398_;
v_isShared_2410_ = v_isSharedCheck_2501_;
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
v_isShared_2410_ = v_isSharedCheck_2501_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2413_; 
lean_inc(v_declName_2331_);
v___x_2411_ = l_Lean_markAuxRecursor(v_env_2399_, v_declName_2331_);
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 5, v___x_2382_);
lean_ctor_set(v___x_2409_, 0, v___x_2411_);
v___x_2413_ = v___x_2409_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v_nextMacroScope_2400_);
lean_ctor_set(v_reuseFailAlloc_2500_, 2, v_ngen_2401_);
lean_ctor_set(v_reuseFailAlloc_2500_, 3, v_auxDeclNGen_2402_);
lean_ctor_set(v_reuseFailAlloc_2500_, 4, v_traceState_2403_);
lean_ctor_set(v_reuseFailAlloc_2500_, 5, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2500_, 6, v_recordedDeps_2404_);
lean_ctor_set(v_reuseFailAlloc_2500_, 7, v_messages_2405_);
lean_ctor_set(v_reuseFailAlloc_2500_, 8, v_infoState_2406_);
lean_ctor_set(v_reuseFailAlloc_2500_, 9, v_snapshotTasks_2407_);
v___x_2413_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v_mctx_2416_; lean_object* v_zetaDeltaFVarIds_2417_; lean_object* v_postponed_2418_; lean_object* v_diag_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2498_; 
v___x_2414_ = lean_st_ref_put(v_a_2336_, v___x_2413_);
v___x_2415_ = lean_st_ref_take(v_a_2334_);
v_mctx_2416_ = lean_ctor_get(v___x_2415_, 0);
v_zetaDeltaFVarIds_2417_ = lean_ctor_get(v___x_2415_, 2);
v_postponed_2418_ = lean_ctor_get(v___x_2415_, 3);
v_diag_2419_ = lean_ctor_get(v___x_2415_, 4);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; 
v_unused_2499_ = lean_ctor_get(v___x_2415_, 1);
lean_dec(v_unused_2499_);
v___x_2421_ = v___x_2415_;
v_isShared_2422_ = v_isSharedCheck_2498_;
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
v_isShared_2422_ = v_isSharedCheck_2498_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v___x_2394_);
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_mctx_2416_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v_zetaDeltaFVarIds_2417_);
lean_ctor_set(v_reuseFailAlloc_2497_, 3, v_postponed_2418_);
lean_ctor_set(v_reuseFailAlloc_2497_, 4, v_diag_2419_);
v___x_2424_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v_env_2427_; lean_object* v_nextMacroScope_2428_; lean_object* v_ngen_2429_; lean_object* v_auxDeclNGen_2430_; lean_object* v_traceState_2431_; lean_object* v_recordedDeps_2432_; lean_object* v_messages_2433_; lean_object* v_infoState_2434_; lean_object* v_snapshotTasks_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2495_; 
v___x_2425_ = lean_st_ref_put(v_a_2334_, v___x_2424_);
v___x_2426_ = lean_st_ref_take(v_a_2336_);
v_env_2427_ = lean_ctor_get(v___x_2426_, 0);
v_nextMacroScope_2428_ = lean_ctor_get(v___x_2426_, 1);
v_ngen_2429_ = lean_ctor_get(v___x_2426_, 2);
v_auxDeclNGen_2430_ = lean_ctor_get(v___x_2426_, 3);
v_traceState_2431_ = lean_ctor_get(v___x_2426_, 4);
v_recordedDeps_2432_ = lean_ctor_get(v___x_2426_, 6);
v_messages_2433_ = lean_ctor_get(v___x_2426_, 7);
v_infoState_2434_ = lean_ctor_get(v___x_2426_, 8);
v_snapshotTasks_2435_ = lean_ctor_get(v___x_2426_, 9);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v___x_2426_, 5);
lean_dec(v_unused_2496_);
v___x_2437_ = v___x_2426_;
v_isShared_2438_ = v_isSharedCheck_2495_;
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
v_isShared_2438_ = v_isSharedCheck_2495_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_inc(v_declName_2331_);
v___x_2439_ = l_Lean_Meta_addToCompletionBlackList(v_env_2427_, v_declName_2331_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 5, v___x_2382_);
lean_ctor_set(v___x_2437_, 0, v___x_2439_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_nextMacroScope_2428_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_ngen_2429_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_auxDeclNGen_2430_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v_traceState_2431_);
lean_ctor_set(v_reuseFailAlloc_2494_, 5, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2494_, 6, v_recordedDeps_2432_);
lean_ctor_set(v_reuseFailAlloc_2494_, 7, v_messages_2433_);
lean_ctor_set(v_reuseFailAlloc_2494_, 8, v_infoState_2434_);
lean_ctor_set(v_reuseFailAlloc_2494_, 9, v_snapshotTasks_2435_);
v___x_2441_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_mctx_2444_; lean_object* v_zetaDeltaFVarIds_2445_; lean_object* v_postponed_2446_; lean_object* v_diag_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2492_; 
v___x_2442_ = lean_st_ref_put(v_a_2336_, v___x_2441_);
v___x_2443_ = lean_st_ref_take(v_a_2334_);
v_mctx_2444_ = lean_ctor_get(v___x_2443_, 0);
v_zetaDeltaFVarIds_2445_ = lean_ctor_get(v___x_2443_, 2);
v_postponed_2446_ = lean_ctor_get(v___x_2443_, 3);
v_diag_2447_ = lean_ctor_get(v___x_2443_, 4);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v___x_2443_, 1);
lean_dec(v_unused_2493_);
v___x_2449_ = v___x_2443_;
v_isShared_2450_ = v_isSharedCheck_2492_;
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
v_isShared_2450_ = v_isSharedCheck_2492_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v___x_2394_);
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_mctx_2444_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_zetaDeltaFVarIds_2445_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_postponed_2446_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_diag_2447_);
v___x_2452_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v_env_2455_; lean_object* v_nextMacroScope_2456_; lean_object* v_ngen_2457_; lean_object* v_auxDeclNGen_2458_; lean_object* v_traceState_2459_; lean_object* v_recordedDeps_2460_; lean_object* v_messages_2461_; lean_object* v_infoState_2462_; lean_object* v_snapshotTasks_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2489_; 
v___x_2453_ = lean_st_ref_put(v_a_2334_, v___x_2452_);
v___x_2454_ = lean_st_ref_take(v_a_2336_);
v_env_2455_ = lean_ctor_get(v___x_2454_, 0);
v_nextMacroScope_2456_ = lean_ctor_get(v___x_2454_, 1);
v_ngen_2457_ = lean_ctor_get(v___x_2454_, 2);
v_auxDeclNGen_2458_ = lean_ctor_get(v___x_2454_, 3);
v_traceState_2459_ = lean_ctor_get(v___x_2454_, 4);
v_recordedDeps_2460_ = lean_ctor_get(v___x_2454_, 6);
v_messages_2461_ = lean_ctor_get(v___x_2454_, 7);
v_infoState_2462_ = lean_ctor_get(v___x_2454_, 8);
v_snapshotTasks_2463_ = lean_ctor_get(v___x_2454_, 9);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; 
v_unused_2490_ = lean_ctor_get(v___x_2454_, 5);
lean_dec(v_unused_2490_);
v___x_2465_ = v___x_2454_;
v_isShared_2466_ = v_isSharedCheck_2489_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_snapshotTasks_2463_);
lean_inc(v_infoState_2462_);
lean_inc(v_messages_2461_);
lean_inc(v_recordedDeps_2460_);
lean_inc(v_traceState_2459_);
lean_inc(v_auxDeclNGen_2458_);
lean_inc(v_ngen_2457_);
lean_inc(v_nextMacroScope_2456_);
lean_inc(v_env_2455_);
lean_dec(v___x_2454_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2489_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
lean_inc(v_declName_2331_);
v___x_2467_ = l_Lean_addProtected(v_env_2455_, v_declName_2331_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 5, v___x_2382_);
lean_ctor_set(v___x_2465_, 0, v___x_2467_);
v___x_2469_ = v___x_2465_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_nextMacroScope_2456_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_ngen_2457_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_auxDeclNGen_2458_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_traceState_2459_);
lean_ctor_set(v_reuseFailAlloc_2488_, 5, v___x_2382_);
lean_ctor_set(v_reuseFailAlloc_2488_, 6, v_recordedDeps_2460_);
lean_ctor_set(v_reuseFailAlloc_2488_, 7, v_messages_2461_);
lean_ctor_set(v_reuseFailAlloc_2488_, 8, v_infoState_2462_);
lean_ctor_set(v_reuseFailAlloc_2488_, 9, v_snapshotTasks_2463_);
v___x_2469_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v_mctx_2472_; lean_object* v_zetaDeltaFVarIds_2473_; lean_object* v_postponed_2474_; lean_object* v_diag_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2486_; 
v___x_2470_ = lean_st_ref_put(v_a_2336_, v___x_2469_);
v___x_2471_ = lean_st_ref_take(v_a_2334_);
v_mctx_2472_ = lean_ctor_get(v___x_2471_, 0);
v_zetaDeltaFVarIds_2473_ = lean_ctor_get(v___x_2471_, 2);
v_postponed_2474_ = lean_ctor_get(v___x_2471_, 3);
v_diag_2475_ = lean_ctor_get(v___x_2471_, 4);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2471_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v___x_2471_, 1);
lean_dec(v_unused_2487_);
v___x_2477_ = v___x_2471_;
v_isShared_2478_ = v_isSharedCheck_2486_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_diag_2475_);
lean_inc(v_postponed_2474_);
lean_inc(v_zetaDeltaFVarIds_2473_);
lean_inc(v_mctx_2472_);
lean_dec(v___x_2471_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2486_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 1, v___x_2394_);
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_mctx_2472_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2394_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_zetaDeltaFVarIds_2473_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_postponed_2474_);
lean_ctor_set(v_reuseFailAlloc_2485_, 4, v_diag_2475_);
v___x_2480_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2481_ = lean_st_ref_put(v_a_2334_, v___x_2480_);
v___x_2482_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2331_);
v___x_2483_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(v___x_2482_, v_declName_2331_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v___x_2484_; 
lean_dec_ref_known(v___x_2483_, 1);
v___x_2484_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_declName_2331_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
return v___x_2484_;
}
else
{
lean_dec(v_declName_2331_);
return v___x_2483_;
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
lean_dec(v_declName_2331_);
return v___x_2367_;
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec(v_levelParams_2348_);
lean_dec(v_declName_2331_);
v_a_2511_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2361_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2361_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
else
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec(v___x_2351_);
lean_dec_ref(v_type_2349_);
lean_dec(v_levelParams_2348_);
lean_dec(v_name_2347_);
lean_dec(v___x_2344_);
lean_del_object(v___x_2342_);
lean_dec_ref(v_val_2340_);
lean_dec(v_indName_2332_);
lean_dec(v_declName_2331_);
v___x_2520_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2521_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_2520_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
return v___x_2521_;
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_dec(v___x_2344_);
lean_del_object(v___x_2342_);
lean_dec_ref(v_val_2340_);
lean_dec(v_indName_2332_);
lean_dec(v_declName_2331_);
v_a_2522_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2345_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2345_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
}
else
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec(v_a_2339_);
lean_dec(v_indName_2332_);
lean_dec(v_declName_2331_);
v___x_2531_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2532_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_2531_, v_a_2333_, v_a_2334_, v_a_2335_, v_a_2336_);
return v___x_2532_;
}
}
else
{
lean_object* v_a_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2540_; 
lean_dec(v_indName_2332_);
lean_dec(v_declName_2331_);
v_a_2533_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2540_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2540_ == 0)
{
v___x_2535_ = v___x_2338_;
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_a_2533_);
lean_dec(v___x_2338_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2540_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v___x_2538_; 
if (v_isShared_2536_ == 0)
{
v___x_2538_ = v___x_2535_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2533_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2541_, lean_object* v_indName_2542_, lean_object* v_a_2543_, lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2541_, v_indName_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_);
lean_dec(v_a_2546_);
lean_dec_ref(v_a_2545_);
lean_dec(v_a_2544_);
lean_dec_ref(v_a_2543_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2549_, lean_object* v_name_2550_, lean_object* v_type_2551_, lean_object* v_k_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2550_, v_type_2551_, v_k_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2559_, lean_object* v_name_2560_, lean_object* v_type_2561_, lean_object* v_k_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v_res_2568_; 
v_res_2568_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2559_, v_name_2560_, v_type_2561_, v_k_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2569_, lean_object* v_params_2570_, lean_object* v_alts_2571_, lean_object* v___x_2572_, lean_object* v_ism2_2573_, lean_object* v_motive_2574_, lean_object* v_val_2575_, lean_object* v_indName_2576_, lean_object* v___x_2577_, lean_object* v___x_2578_, lean_object* v___x_2579_, lean_object* v_as_2580_, size_t v_sz_2581_, size_t v_i_2582_, lean_object* v_bs_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2569_, v_params_2570_, v_alts_2571_, v___x_2572_, v_ism2_2573_, v_motive_2574_, v_val_2575_, v_indName_2576_, v___x_2577_, v___x_2578_, v___x_2579_, v_sz_2581_, v_i_2582_, v_bs_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2590_ = _args[0];
lean_object* v_params_2591_ = _args[1];
lean_object* v_alts_2592_ = _args[2];
lean_object* v___x_2593_ = _args[3];
lean_object* v_ism2_2594_ = _args[4];
lean_object* v_motive_2595_ = _args[5];
lean_object* v_val_2596_ = _args[6];
lean_object* v_indName_2597_ = _args[7];
lean_object* v___x_2598_ = _args[8];
lean_object* v___x_2599_ = _args[9];
lean_object* v___x_2600_ = _args[10];
lean_object* v_as_2601_ = _args[11];
lean_object* v_sz_2602_ = _args[12];
lean_object* v_i_2603_ = _args[13];
lean_object* v_bs_2604_ = _args[14];
lean_object* v___y_2605_ = _args[15];
lean_object* v___y_2606_ = _args[16];
lean_object* v___y_2607_ = _args[17];
lean_object* v___y_2608_ = _args[18];
lean_object* v___y_2609_ = _args[19];
_start:
{
size_t v_sz_boxed_2610_; size_t v_i_boxed_2611_; lean_object* v_res_2612_; 
v_sz_boxed_2610_ = lean_unbox_usize(v_sz_2602_);
lean_dec(v_sz_2602_);
v_i_boxed_2611_ = lean_unbox_usize(v_i_2603_);
lean_dec(v_i_2603_);
v_res_2612_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2590_, v_params_2591_, v_alts_2592_, v___x_2593_, v_ism2_2594_, v_motive_2595_, v_val_2596_, v_indName_2597_, v___x_2598_, v___x_2599_, v___x_2600_, v_as_2601_, v_sz_boxed_2610_, v_i_boxed_2611_, v_bs_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v_as_2601_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2613_, lean_object* v_params_2614_, lean_object* v___x_2615_, lean_object* v_motive_2616_, lean_object* v_as_2617_, size_t v_sz_2618_, size_t v_i_2619_, lean_object* v_bs_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___x_2626_; 
v___x_2626_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2613_, v_params_2614_, v___x_2615_, v_motive_2616_, v_sz_2618_, v_i_2619_, v_bs_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_);
return v___x_2626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2627_, lean_object* v_params_2628_, lean_object* v___x_2629_, lean_object* v_motive_2630_, lean_object* v_as_2631_, lean_object* v_sz_2632_, lean_object* v_i_2633_, lean_object* v_bs_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
size_t v_sz_boxed_2640_; size_t v_i_boxed_2641_; lean_object* v_res_2642_; 
v_sz_boxed_2640_ = lean_unbox_usize(v_sz_2632_);
lean_dec(v_sz_2632_);
v_i_boxed_2641_ = lean_unbox_usize(v_i_2633_);
lean_dec(v_i_2633_);
v_res_2642_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2627_, v_params_2628_, v___x_2629_, v_motive_2630_, v_as_2631_, v_sz_boxed_2640_, v_i_boxed_2641_, v_bs_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v_as_2631_);
lean_dec_ref(v_params_2628_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_2643_, lean_object* v_x_2644_, uint8_t v_isExporting_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_2644_, v_isExporting_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_2652_, lean_object* v_x_2653_, lean_object* v_isExporting_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
uint8_t v_isExporting_boxed_2660_; lean_object* v_res_2661_; 
v_isExporting_boxed_2660_ = lean_unbox(v_isExporting_2654_);
v_res_2661_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_2652_, v_x_2653_, v_isExporting_boxed_2660_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b2_2662_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg(){
_start:
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg___boxed(lean_object* v___dummy_2666_){
_start:
{
lean_object* v_res_2667_; 
v_res_2667_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg();
return v_res_2667_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_00_u03b2_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2670_, lean_object* v_constName_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_){
_start:
{
lean_object* v___x_2677_; 
v___x_2677_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2678_, lean_object* v_constName_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2678_, v_constName_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_);
lean_dec(v___y_2683_);
lean_dec_ref(v___y_2682_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17(lean_object* v_00_u03b1_2686_, lean_object* v_attrName_2687_, lean_object* v_declName_2688_, lean_object* v_asyncPrefix_x3f_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
lean_object* v___x_2695_; 
v___x_2695_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(v_attrName_2687_, v_declName_2688_, v_asyncPrefix_x3f_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___boxed(lean_object* v_00_u03b1_2696_, lean_object* v_attrName_2697_, lean_object* v_declName_2698_, lean_object* v_asyncPrefix_x3f_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17(v_00_u03b1_2696_, v_attrName_2697_, v_declName_2698_, v_asyncPrefix_x3f_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_00_u03b1_2706_, lean_object* v_attrName_2707_, lean_object* v_declName_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_){
_start:
{
lean_object* v___x_2714_; 
v___x_2714_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_attrName_2707_, v_declName_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_00_u03b1_2715_, lean_object* v_attrName_2716_, lean_object* v_declName_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_00_u03b1_2715_, v_attrName_2716_, v_declName_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20(lean_object* v_declName_2724_, uint8_t v_s_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(v_declName_2724_, v_s_2725_, v___y_2727_, v___y_2729_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___boxed(lean_object* v_declName_2732_, lean_object* v_s_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
uint8_t v_s_boxed_2739_; lean_object* v_res_2740_; 
v_s_boxed_2739_ = lean_unbox(v_s_2733_);
v_res_2740_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20(v_declName_2732_, v_s_boxed_2739_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6(lean_object* v_00_u03b1_2741_, lean_object* v_ref_2742_, lean_object* v_constName_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(v_ref_2742_, v_constName_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b1_2750_, lean_object* v_ref_2751_, lean_object* v_constName_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6(v_00_u03b1_2750_, v_ref_2751_, v_constName_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v_ref_2751_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22(lean_object* v_00_u03b1_2759_, lean_object* v_msg_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v_msg_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___boxed(lean_object* v_00_u03b1_2767_, lean_object* v_msg_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22(v_00_u03b1_2767_, v_msg_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
return v_res_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18(lean_object* v_00_u03b1_2775_, lean_object* v_ref_2776_, lean_object* v_msg_2777_, lean_object* v_declHint_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(v_ref_2776_, v_msg_2777_, v_declHint_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___boxed(lean_object* v_00_u03b1_2785_, lean_object* v_ref_2786_, lean_object* v_msg_2787_, lean_object* v_declHint_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18(v_00_u03b1_2785_, v_ref_2786_, v_msg_2787_, v_declHint_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v_ref_2786_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29(lean_object* v_msg_2795_, lean_object* v_declHint_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(v_msg_2795_, v_declHint_2796_, v___y_2800_);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___boxed(lean_object* v_msg_2803_, lean_object* v_declHint_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29(v_msg_2803_, v_declHint_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25(lean_object* v_00_u03b1_2811_, lean_object* v_ref_2812_, lean_object* v_msg_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(v_ref_2812_, v_msg_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___boxed(lean_object* v_00_u03b1_2820_, lean_object* v_ref_2821_, lean_object* v_msg_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25(v_00_u03b1_2820_, v_ref_2821_, v_msg_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec_ref(v___y_2823_);
lean_dec(v_ref_2821_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2829_, lean_object* v___y_2830_){
_start:
{
uint8_t v___x_2832_; 
v___x_2832_ = l_Lean_Expr_hasMVar(v_e_2829_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; 
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_e_2829_);
return v___x_2833_;
}
else
{
lean_object* v___x_2834_; lean_object* v_mctx_2835_; lean_object* v___x_2836_; lean_object* v_fst_2837_; lean_object* v_snd_2838_; lean_object* v___x_2839_; lean_object* v_cache_2840_; lean_object* v_zetaDeltaFVarIds_2841_; lean_object* v_postponed_2842_; lean_object* v_diag_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2852_; 
v___x_2834_ = lean_st_ref_get(v___y_2830_);
v_mctx_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc_ref(v_mctx_2835_);
lean_dec(v___x_2834_);
v___x_2836_ = l_Lean_instantiateMVarsCore(v_mctx_2835_, v_e_2829_);
v_fst_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_fst_2837_);
v_snd_2838_ = lean_ctor_get(v___x_2836_, 1);
lean_inc(v_snd_2838_);
lean_dec_ref(v___x_2836_);
v___x_2839_ = lean_st_ref_take(v___y_2830_);
v_cache_2840_ = lean_ctor_get(v___x_2839_, 1);
v_zetaDeltaFVarIds_2841_ = lean_ctor_get(v___x_2839_, 2);
v_postponed_2842_ = lean_ctor_get(v___x_2839_, 3);
v_diag_2843_ = lean_ctor_get(v___x_2839_, 4);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; 
v_unused_2853_ = lean_ctor_get(v___x_2839_, 0);
lean_dec(v_unused_2853_);
v___x_2845_ = v___x_2839_;
v_isShared_2846_ = v_isSharedCheck_2852_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_diag_2843_);
lean_inc(v_postponed_2842_);
lean_inc(v_zetaDeltaFVarIds_2841_);
lean_inc(v_cache_2840_);
lean_dec(v___x_2839_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2852_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v_snd_2838_);
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_snd_2838_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_cache_2840_);
lean_ctor_set(v_reuseFailAlloc_2851_, 2, v_zetaDeltaFVarIds_2841_);
lean_ctor_set(v_reuseFailAlloc_2851_, 3, v_postponed_2842_);
lean_ctor_set(v_reuseFailAlloc_2851_, 4, v_diag_2843_);
v___x_2848_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_st_ref_put(v___y_2830_, v___x_2848_);
v___x_2850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2850_, 0, v_fst_2837_);
return v___x_2850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2854_, v___y_2855_);
lean_dec(v___y_2855_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2858_, v___y_2860_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_){
_start:
{
lean_object* v_res_2871_; 
v_res_2871_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2865_, v___y_2866_, v___y_2867_, v___y_2868_, v___y_2869_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2872_, lean_object* v___x_2873_, lean_object* v_newEqs1_2874_, uint8_t v___x_2875_, uint8_t v___x_2876_, uint8_t v___x_2877_, lean_object* v_ism1_x27_2878_, lean_object* v_ism2_x27_2879_, lean_object* v_newRefls1_2880_, lean_object* v_newEqs2_2881_, lean_object* v_newRefls2_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2888_ = l_Lean_mkAppN(v_motive_2872_, v___x_2873_);
v___x_2889_ = l_Array_append___redArg(v_newEqs1_2874_, v_newEqs2_2881_);
v___x_2890_ = l_Lean_Meta_mkForallFVars(v___x_2889_, v___x_2888_, v___x_2875_, v___x_2876_, v___x_2876_, v___x_2877_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
lean_dec_ref(v___x_2889_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
v___x_2892_ = l_Array_append___redArg(v_ism1_x27_2878_, v_ism2_x27_2879_);
v___x_2893_ = l_Lean_Meta_mkLambdaFVars(v___x_2892_, v_a_2891_, v___x_2875_, v___x_2876_, v___x_2875_, v___x_2876_, v___x_2877_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
lean_dec_ref(v___x_2892_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2903_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2896_ = v___x_2893_;
v_isShared_2897_ = v_isSharedCheck_2903_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2893_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2903_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2898_ = l_Array_append___redArg(v_newRefls1_2880_, v_newRefls2_2882_);
v___x_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2899_, 0, v_a_2894_);
lean_ctor_set(v___x_2899_, 1, v___x_2898_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v___x_2899_);
v___x_2901_ = v___x_2896_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec_ref(v_newRefls1_2880_);
v_a_2904_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2893_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2893_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v_newRefls1_2880_);
lean_dec_ref(v_ism1_x27_2878_);
v_a_2912_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2890_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2890_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2920_, lean_object* v___x_2921_, lean_object* v_newEqs1_2922_, lean_object* v___x_2923_, lean_object* v___x_2924_, lean_object* v___x_2925_, lean_object* v_ism1_x27_2926_, lean_object* v_ism2_x27_2927_, lean_object* v_newRefls1_2928_, lean_object* v_newEqs2_2929_, lean_object* v_newRefls2_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
uint8_t v___x_14931__boxed_2936_; uint8_t v___x_14932__boxed_2937_; uint8_t v___x_14933__boxed_2938_; lean_object* v_res_2939_; 
v___x_14931__boxed_2936_ = lean_unbox(v___x_2923_);
v___x_14932__boxed_2937_ = lean_unbox(v___x_2924_);
v___x_14933__boxed_2938_ = lean_unbox(v___x_2925_);
v_res_2939_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2920_, v___x_2921_, v_newEqs1_2922_, v___x_14931__boxed_2936_, v___x_14932__boxed_2937_, v___x_14933__boxed_2938_, v_ism1_x27_2926_, v_ism2_x27_2927_, v_newRefls1_2928_, v_newEqs2_2929_, v_newRefls2_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v_newRefls2_2930_);
lean_dec_ref(v_newEqs2_2929_);
lean_dec_ref(v_ism2_x27_2927_);
lean_dec_ref(v___x_2921_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2940_, lean_object* v___x_2941_, uint8_t v___x_2942_, uint8_t v___x_2943_, uint8_t v___x_2944_, lean_object* v_ism1_x27_2945_, lean_object* v_ism2_x27_2946_, lean_object* v_is_2947_, lean_object* v___x_2948_, lean_object* v_newEqs1_2949_, lean_object* v_newRefls1_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___f_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2956_ = lean_box(v___x_2942_);
v___x_2957_ = lean_box(v___x_2943_);
v___x_2958_ = lean_box(v___x_2944_);
lean_inc_ref(v_ism2_x27_2946_);
v___f_2959_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2959_, 0, v_motive_2940_);
lean_closure_set(v___f_2959_, 1, v___x_2941_);
lean_closure_set(v___f_2959_, 2, v_newEqs1_2949_);
lean_closure_set(v___f_2959_, 3, v___x_2956_);
lean_closure_set(v___f_2959_, 4, v___x_2957_);
lean_closure_set(v___f_2959_, 5, v___x_2958_);
lean_closure_set(v___f_2959_, 6, v_ism1_x27_2945_);
lean_closure_set(v___f_2959_, 7, v_ism2_x27_2946_);
lean_closure_set(v___f_2959_, 8, v_newRefls1_2950_);
v___x_2960_ = lean_array_push(v_is_2947_, v___x_2948_);
v___x_2961_ = l_Lean_Meta_withNewEqs___redArg(v___x_2960_, v_ism2_x27_2946_, v___f_2959_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2962_, lean_object* v___x_2963_, lean_object* v___x_2964_, lean_object* v___x_2965_, lean_object* v___x_2966_, lean_object* v_ism1_x27_2967_, lean_object* v_ism2_x27_2968_, lean_object* v_is_2969_, lean_object* v___x_2970_, lean_object* v_newEqs1_2971_, lean_object* v_newRefls1_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
uint8_t v___x_15022__boxed_2978_; uint8_t v___x_15023__boxed_2979_; uint8_t v___x_15024__boxed_2980_; lean_object* v_res_2981_; 
v___x_15022__boxed_2978_ = lean_unbox(v___x_2964_);
v___x_15023__boxed_2979_ = lean_unbox(v___x_2965_);
v___x_15024__boxed_2980_ = lean_unbox(v___x_2966_);
v_res_2981_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2962_, v___x_2963_, v___x_15022__boxed_2978_, v___x_15023__boxed_2979_, v___x_15024__boxed_2980_, v_ism1_x27_2967_, v_ism2_x27_2968_, v_is_2969_, v___x_2970_, v_newEqs1_2971_, v_newRefls1_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_);
lean_dec(v___y_2976_);
lean_dec_ref(v___y_2975_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_2982_, uint8_t v___x_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_addDecl(v___x_2982_, v___x_2983_, v___y_2986_, v___y_2987_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_2990_, lean_object* v___x_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
uint8_t v___x_15064__boxed_2997_; lean_object* v_res_2998_; 
v___x_15064__boxed_2997_ = lean_unbox(v___x_2991_);
v_res_2998_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_2990_, v___x_15064__boxed_2997_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
return v_res_2998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_2999_, lean_object* v_info_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
lean_object* v___x_3004_; lean_object* v_env_3005_; lean_object* v_nextMacroScope_3006_; lean_object* v_ngen_3007_; lean_object* v_auxDeclNGen_3008_; lean_object* v_traceState_3009_; lean_object* v_recordedDeps_3010_; lean_object* v_messages_3011_; lean_object* v_infoState_3012_; lean_object* v_snapshotTasks_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3040_; 
v___x_3004_ = lean_st_ref_take(v___y_3002_);
v_env_3005_ = lean_ctor_get(v___x_3004_, 0);
v_nextMacroScope_3006_ = lean_ctor_get(v___x_3004_, 1);
v_ngen_3007_ = lean_ctor_get(v___x_3004_, 2);
v_auxDeclNGen_3008_ = lean_ctor_get(v___x_3004_, 3);
v_traceState_3009_ = lean_ctor_get(v___x_3004_, 4);
v_recordedDeps_3010_ = lean_ctor_get(v___x_3004_, 6);
v_messages_3011_ = lean_ctor_get(v___x_3004_, 7);
v_infoState_3012_ = lean_ctor_get(v___x_3004_, 8);
v_snapshotTasks_3013_ = lean_ctor_get(v___x_3004_, 9);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3040_ == 0)
{
lean_object* v_unused_3041_; 
v_unused_3041_ = lean_ctor_get(v___x_3004_, 5);
lean_dec(v_unused_3041_);
v___x_3015_ = v___x_3004_;
v_isShared_3016_ = v_isSharedCheck_3040_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_snapshotTasks_3013_);
lean_inc(v_infoState_3012_);
lean_inc(v_messages_3011_);
lean_inc(v_recordedDeps_3010_);
lean_inc(v_traceState_3009_);
lean_inc(v_auxDeclNGen_3008_);
lean_inc(v_ngen_3007_);
lean_inc(v_nextMacroScope_3006_);
lean_inc(v_env_3005_);
lean_dec(v___x_3004_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3040_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3020_; 
v___x_3017_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_3005_, v_matcherName_2999_, v_info_3000_);
v___x_3018_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 5, v___x_3018_);
lean_ctor_set(v___x_3015_, 0, v___x_3017_);
v___x_3020_ = v___x_3015_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v_nextMacroScope_3006_);
lean_ctor_set(v_reuseFailAlloc_3039_, 2, v_ngen_3007_);
lean_ctor_set(v_reuseFailAlloc_3039_, 3, v_auxDeclNGen_3008_);
lean_ctor_set(v_reuseFailAlloc_3039_, 4, v_traceState_3009_);
lean_ctor_set(v_reuseFailAlloc_3039_, 5, v___x_3018_);
lean_ctor_set(v_reuseFailAlloc_3039_, 6, v_recordedDeps_3010_);
lean_ctor_set(v_reuseFailAlloc_3039_, 7, v_messages_3011_);
lean_ctor_set(v_reuseFailAlloc_3039_, 8, v_infoState_3012_);
lean_ctor_set(v_reuseFailAlloc_3039_, 9, v_snapshotTasks_3013_);
v___x_3020_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v_mctx_3023_; lean_object* v_zetaDeltaFVarIds_3024_; lean_object* v_postponed_3025_; lean_object* v_diag_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3037_; 
v___x_3021_ = lean_st_ref_put(v___y_3002_, v___x_3020_);
v___x_3022_ = lean_st_ref_take(v___y_3001_);
v_mctx_3023_ = lean_ctor_get(v___x_3022_, 0);
v_zetaDeltaFVarIds_3024_ = lean_ctor_get(v___x_3022_, 2);
v_postponed_3025_ = lean_ctor_get(v___x_3022_, 3);
v_diag_3026_ = lean_ctor_get(v___x_3022_, 4);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3037_ == 0)
{
lean_object* v_unused_3038_; 
v_unused_3038_ = lean_ctor_get(v___x_3022_, 1);
lean_dec(v_unused_3038_);
v___x_3028_ = v___x_3022_;
v_isShared_3029_ = v_isSharedCheck_3037_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_diag_3026_);
lean_inc(v_postponed_3025_);
lean_inc(v_zetaDeltaFVarIds_3024_);
lean_inc(v_mctx_3023_);
lean_dec(v___x_3022_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3037_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3033_; 
v___x_3030_ = lean_box(0);
v___x_3031_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5);
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 1, v___x_3031_);
v___x_3033_ = v___x_3028_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_mctx_3023_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3031_);
lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_zetaDeltaFVarIds_3024_);
lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_postponed_3025_);
lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_diag_3026_);
v___x_3033_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = lean_st_ref_put(v___y_3001_, v___x_3033_);
v___x_3035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3030_);
return v___x_3035_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_3042_, lean_object* v_info_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_3042_, v_info_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec(v___y_3044_);
return v_res_3047_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3050_ = l_Lean_stringToMessageData(v___x_3049_);
return v___x_3050_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3053_ = l_Lean_stringToMessageData(v___x_3052_);
return v___x_3053_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3059_ = lean_box(0);
v___x_3060_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3061_ = l_Lean_mkConst(v___x_3060_, v___x_3059_);
return v___x_3061_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3064_ = l_Lean_stringToMessageData(v___x_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3065_, lean_object* v_a_3066_, lean_object* v___x_3067_, lean_object* v_zs1_3068_, lean_object* v_snd_3069_, uint8_t v___x_3070_, uint8_t v___x_3071_, uint8_t v___x_3072_, lean_object* v_alts_3073_, lean_object* v_zs2_3074_, lean_object* v___ctorRet2_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = lean_array_get_borrowed(v___x_3065_, v_a_3066_, v___x_3067_);
lean_inc_ref(v_zs1_3068_);
v___x_3082_ = l_Array_append___redArg(v_zs1_3068_, v_zs2_3074_);
lean_inc(v___x_3081_);
v___x_3083_ = l_Lean_Meta_instantiateForall(v___x_3081_, v___x_3082_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref_known(v___x_3083_, 1);
v___x_3085_ = lean_box(0);
v___x_3086_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3084_, v___x_3085_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_a_3087_);
lean_dec_ref_known(v___x_3086_, 1);
v___x_3088_ = l_Lean_Expr_mvarId_x21(v_a_3087_);
v___x_3089_ = lean_array_get_size(v_snd_3069_);
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_box(0);
lean_inc_ref(v___y_3078_);
v___x_3092_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3089_, v___x_3088_, v___x_3090_, v___x_3091_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3092_, 1);
if (lean_obj_tag(v_a_3093_) == 1)
{
lean_object* v_val_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3141_; 
v_val_3094_ = lean_ctor_get(v_a_3093_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v_a_3093_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3096_ = v_a_3093_;
v_isShared_3097_ = v_isSharedCheck_3141_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_val_3094_);
lean_dec(v_a_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3141_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_fst_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3139_; 
v_fst_3098_ = lean_ctor_get(v_val_3094_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v_val_3094_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v_val_3094_, 1);
lean_dec(v_unused_3140_);
v___x_3100_ = v_val_3094_;
v_isShared_3101_ = v_isSharedCheck_3139_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_fst_3098_);
lean_dec(v_val_3094_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3139_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___y_3103_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v___x_3131_ = lean_array_get_borrowed(v___x_3065_, v_alts_3073_, v___x_3067_);
v___x_3132_ = lean_array_get_size(v_zs1_3068_);
lean_dec_ref(v_zs1_3068_);
v___x_3133_ = lean_unsigned_to_nat(0u);
v___x_3134_ = lean_nat_dec_eq(v___x_3132_, v___x_3133_);
if (v___x_3134_ == 0)
{
lean_inc(v___x_3131_);
v___y_3103_ = v___x_3131_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3135_ = lean_array_get_size(v_zs2_3074_);
v___x_3136_ = lean_nat_dec_eq(v___x_3135_, v___x_3133_);
if (v___x_3136_ == 0)
{
lean_inc(v___x_3131_);
v___y_3103_ = v___x_3131_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3131_);
v___x_3138_ = l_Lean_Expr_app___override(v___x_3131_, v___x_3137_);
v___y_3103_ = v___x_3138_;
goto v___jp_3102_;
}
}
v___jp_3102_:
{
uint8_t v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = 0;
v___x_3105_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3105_, 0, v___x_3104_);
lean_ctor_set_uint8(v___x_3105_, 1, v___x_3070_);
lean_ctor_set_uint8(v___x_3105_, 2, v___x_3071_);
lean_ctor_set_uint8(v___x_3105_, 3, v___x_3070_);
lean_inc_ref(v___y_3103_);
lean_inc(v_fst_3098_);
v___x_3106_ = l_Lean_MVarId_apply(v_fst_3098_, v___y_3103_, v___x_3105_, v___x_3091_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v_a_3107_; 
v_a_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_a_3107_);
lean_dec_ref_known(v___x_3106_, 1);
if (lean_obj_tag(v_a_3107_) == 0)
{
lean_object* v___x_3108_; 
lean_dec_ref(v___y_3103_);
lean_del_object(v___x_3100_);
lean_dec(v_fst_3098_);
lean_del_object(v___x_3096_);
v___x_3108_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3087_, v___y_3077_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3110_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3108_, 1);
v___x_3110_ = l_Lean_Meta_mkLambdaFVars(v___x_3082_, v_a_3109_, v___x_3071_, v___x_3070_, v___x_3071_, v___x_3070_, v___x_3072_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec_ref(v___x_3082_);
return v___x_3110_;
}
else
{
lean_dec_ref(v___x_3082_);
return v___x_3108_;
}
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3114_; 
lean_dec(v_a_3107_);
lean_dec(v_a_3087_);
lean_dec_ref(v___x_3082_);
v___x_3111_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3112_ = l_Lean_MessageData_ofExpr(v___y_3103_);
if (v_isShared_3101_ == 0)
{
lean_ctor_set_tag(v___x_3100_, 7);
lean_ctor_set(v___x_3100_, 1, v___x_3112_);
lean_ctor_set(v___x_3100_, 0, v___x_3111_);
v___x_3114_ = v___x_3100_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3112_);
v___x_3114_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3118_; 
v___x_3115_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v_fst_3098_);
v___x_3118_ = v___x_3096_;
goto v_reusejp_3117_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_fst_3098_);
v___x_3118_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3117_;
}
v_reusejp_3117_:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3116_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_3119_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3120_;
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v___y_3103_);
lean_del_object(v___x_3100_);
lean_dec(v_fst_3098_);
lean_del_object(v___x_3096_);
lean_dec(v_a_3087_);
lean_dec_ref(v___x_3082_);
v_a_3123_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3106_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3106_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; 
lean_dec(v_a_3093_);
lean_dec(v_a_3087_);
lean_dec_ref(v___x_3082_);
lean_dec_ref(v_zs1_3068_);
v___x_3142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3143_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_3142_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
return v___x_3143_;
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec(v_a_3087_);
lean_dec_ref(v___x_3082_);
lean_dec_ref(v_zs1_3068_);
v_a_3144_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3092_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3092_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
}
else
{
lean_dec_ref(v___x_3082_);
lean_dec_ref(v_zs1_3068_);
return v___x_3086_;
}
}
else
{
lean_dec_ref(v___x_3082_);
lean_dec_ref(v_zs1_3068_);
return v___x_3083_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3152_, lean_object* v_a_3153_, lean_object* v___x_3154_, lean_object* v_zs1_3155_, lean_object* v_snd_3156_, lean_object* v___x_3157_, lean_object* v___x_3158_, lean_object* v___x_3159_, lean_object* v_alts_3160_, lean_object* v_zs2_3161_, lean_object* v___ctorRet2_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
uint8_t v___x_15212__boxed_3168_; uint8_t v___x_15213__boxed_3169_; uint8_t v___x_15214__boxed_3170_; lean_object* v_res_3171_; 
v___x_15212__boxed_3168_ = lean_unbox(v___x_3157_);
v___x_15213__boxed_3169_ = lean_unbox(v___x_3158_);
v___x_15214__boxed_3170_ = lean_unbox(v___x_3159_);
v_res_3171_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3152_, v_a_3153_, v___x_3154_, v_zs1_3155_, v_snd_3156_, v___x_15212__boxed_3168_, v___x_15213__boxed_3169_, v___x_15214__boxed_3170_, v_alts_3160_, v_zs2_3161_, v___ctorRet2_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec_ref(v___ctorRet2_3162_);
lean_dec_ref(v_zs2_3161_);
lean_dec_ref(v_alts_3160_);
lean_dec_ref(v_snd_3156_);
lean_dec(v___x_3154_);
lean_dec_ref(v_a_3153_);
lean_dec_ref(v___x_3152_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3172_, lean_object* v_a_3173_, lean_object* v___x_3174_, lean_object* v_snd_3175_, uint8_t v___x_3176_, uint8_t v___x_3177_, uint8_t v___x_3178_, lean_object* v_alts_3179_, lean_object* v_a_3180_, lean_object* v_zs1_3181_, lean_object* v___ctorRet1_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___f_3191_; lean_object* v___x_3192_; 
v___x_3188_ = lean_box(v___x_3176_);
v___x_3189_ = lean_box(v___x_3177_);
v___x_3190_ = lean_box(v___x_3178_);
v___f_3191_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3191_, 0, v___x_3172_);
lean_closure_set(v___f_3191_, 1, v_a_3173_);
lean_closure_set(v___f_3191_, 2, v___x_3174_);
lean_closure_set(v___f_3191_, 3, v_zs1_3181_);
lean_closure_set(v___f_3191_, 4, v_snd_3175_);
lean_closure_set(v___f_3191_, 5, v___x_3188_);
lean_closure_set(v___f_3191_, 6, v___x_3189_);
lean_closure_set(v___f_3191_, 7, v___x_3190_);
lean_closure_set(v___f_3191_, 8, v_alts_3179_);
v___x_3192_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3180_, v___f_3191_, v___x_3177_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3193_, lean_object* v_a_3194_, lean_object* v___x_3195_, lean_object* v_snd_3196_, lean_object* v___x_3197_, lean_object* v___x_3198_, lean_object* v___x_3199_, lean_object* v_alts_3200_, lean_object* v_a_3201_, lean_object* v_zs1_3202_, lean_object* v___ctorRet1_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
uint8_t v___x_15411__boxed_3209_; uint8_t v___x_15412__boxed_3210_; uint8_t v___x_15413__boxed_3211_; lean_object* v_res_3212_; 
v___x_15411__boxed_3209_ = lean_unbox(v___x_3197_);
v___x_15412__boxed_3210_ = lean_unbox(v___x_3198_);
v___x_15413__boxed_3211_ = lean_unbox(v___x_3199_);
v_res_3212_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3193_, v_a_3194_, v___x_3195_, v_snd_3196_, v___x_15411__boxed_3209_, v___x_15412__boxed_3210_, v___x_15413__boxed_3211_, v_alts_3200_, v_a_3201_, v_zs1_3202_, v___ctorRet1_3203_, v___y_3204_, v___y_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec_ref(v___ctorRet1_3203_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3213_, lean_object* v_params_3214_, lean_object* v_a_3215_, lean_object* v_snd_3216_, lean_object* v_alts_3217_, size_t v_sz_3218_, size_t v_i_3219_, lean_object* v_bs_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_){
_start:
{
uint8_t v___x_3226_; 
v___x_3226_ = lean_usize_dec_lt(v_i_3219_, v_sz_3218_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; 
lean_dec_ref(v_alts_3217_);
lean_dec_ref(v_snd_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_tail_3213_);
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_bs_3220_);
return v___x_3227_;
}
else
{
lean_object* v___x_3228_; uint8_t v___x_3229_; uint8_t v___x_3230_; lean_object* v_v_3231_; lean_object* v___x_3232_; lean_object* v_bs_x27_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3228_ = l_Lean_instInhabitedExpr;
v___x_3229_ = 0;
v___x_3230_ = 1;
v_v_3231_ = lean_array_uget(v_bs_3220_, v_i_3219_);
v___x_3232_ = lean_unsigned_to_nat(0u);
v_bs_x27_3233_ = lean_array_uset(v_bs_3220_, v_i_3219_, v___x_3232_);
v___x_3234_ = lean_usize_to_nat(v_i_3219_);
lean_inc(v_tail_3213_);
v___x_3235_ = l_Lean_mkConst(v_v_3231_, v_tail_3213_);
v___x_3236_ = l_Lean_mkAppN(v___x_3235_, v_params_3214_);
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3223_);
lean_inc(v___y_3222_);
lean_inc_ref(v___y_3221_);
v___x_3237_ = lean_infer_type(v___x_3236_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v_a_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___f_3242_; lean_object* v___x_3243_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc_n(v_a_3238_, 2);
lean_dec_ref_known(v___x_3237_, 1);
v___x_3239_ = lean_box(v___x_3226_);
v___x_3240_ = lean_box(v___x_3229_);
v___x_3241_ = lean_box(v___x_3230_);
lean_inc_ref(v_alts_3217_);
lean_inc_ref(v_snd_3216_);
lean_inc_ref(v_a_3215_);
v___f_3242_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3242_, 0, v___x_3228_);
lean_closure_set(v___f_3242_, 1, v_a_3215_);
lean_closure_set(v___f_3242_, 2, v___x_3234_);
lean_closure_set(v___f_3242_, 3, v_snd_3216_);
lean_closure_set(v___f_3242_, 4, v___x_3239_);
lean_closure_set(v___f_3242_, 5, v___x_3240_);
lean_closure_set(v___f_3242_, 6, v___x_3241_);
lean_closure_set(v___f_3242_, 7, v_alts_3217_);
lean_closure_set(v___f_3242_, 8, v_a_3238_);
v___x_3243_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3238_, v___f_3242_, v___x_3229_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; size_t v___x_3245_; size_t v___x_3246_; lean_object* v___x_3247_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref_known(v___x_3243_, 1);
v___x_3245_ = ((size_t)1ULL);
v___x_3246_ = lean_usize_add(v_i_3219_, v___x_3245_);
v___x_3247_ = lean_array_uset(v_bs_x27_3233_, v_i_3219_, v_a_3244_);
v_i_3219_ = v___x_3246_;
v_bs_3220_ = v___x_3247_;
goto _start;
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec_ref(v_bs_x27_3233_);
lean_dec_ref(v_alts_3217_);
lean_dec_ref(v_snd_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_tail_3213_);
v_a_3249_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3243_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3243_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
else
{
lean_object* v_a_3257_; lean_object* v___x_3259_; uint8_t v_isShared_3260_; uint8_t v_isSharedCheck_3264_; 
lean_dec(v___x_3234_);
lean_dec_ref(v_bs_x27_3233_);
lean_dec_ref(v_alts_3217_);
lean_dec_ref(v_snd_3216_);
lean_dec_ref(v_a_3215_);
lean_dec(v_tail_3213_);
v_a_3257_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3259_ = v___x_3237_;
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
else
{
lean_inc(v_a_3257_);
lean_dec(v___x_3237_);
v___x_3259_ = lean_box(0);
v_isShared_3260_ = v_isSharedCheck_3264_;
goto v_resetjp_3258_;
}
v_resetjp_3258_:
{
lean_object* v___x_3262_; 
if (v_isShared_3260_ == 0)
{
v___x_3262_ = v___x_3259_;
goto v_reusejp_3261_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_a_3257_);
v___x_3262_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3261_;
}
v_reusejp_3261_:
{
return v___x_3262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3265_, lean_object* v_params_3266_, lean_object* v_a_3267_, lean_object* v_snd_3268_, lean_object* v_alts_3269_, lean_object* v_sz_3270_, lean_object* v_i_3271_, lean_object* v_bs_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
size_t v_sz_boxed_3278_; size_t v_i_boxed_3279_; lean_object* v_res_3280_; 
v_sz_boxed_3278_ = lean_unbox_usize(v_sz_3270_);
lean_dec(v_sz_3270_);
v_i_boxed_3279_ = lean_unbox_usize(v_i_3271_);
lean_dec(v_i_3271_);
v_res_3280_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3265_, v_params_3266_, v_a_3267_, v_snd_3268_, v_alts_3269_, v_sz_boxed_3278_, v_i_boxed_3279_, v_bs_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec_ref(v_params_3266_);
return v_res_3280_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_unsigned_to_nat(16u);
v___x_3283_ = lean_mk_array(v___x_3282_, v___x_3281_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3284_, lean_object* v___x_3285_, uint8_t v___x_3286_, uint8_t v___x_3287_, uint8_t v___x_3288_, lean_object* v_ism1_x27_3289_, lean_object* v_is_3290_, lean_object* v___x_3291_, lean_object* v___x_3292_, lean_object* v___x_3293_, lean_object* v___x_3294_, lean_object* v_params_3295_, lean_object* v___x_3296_, lean_object* v___x_3297_, lean_object* v_heq_3298_, lean_object* v_val_3299_, lean_object* v_tail_3300_, lean_object* v_alts_3301_, size_t v_sz_3302_, size_t v___x_3303_, lean_object* v___x_3304_, lean_object* v___x_3305_, lean_object* v_declName_3306_, lean_object* v_levelParams_3307_, lean_object* v_numIndices_3308_, lean_object* v___x_3309_, lean_object* v___x_3310_, lean_object* v_numParams_3311_, lean_object* v_snd_3312_, lean_object* v_ism2_x27_3313_, lean_object* v_x_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___f_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v___x_3320_ = lean_box(v___x_3286_);
v___x_3321_ = lean_box(v___x_3287_);
v___x_3322_ = lean_box(v___x_3288_);
lean_inc_ref(v___x_3291_);
lean_inc_ref_n(v_is_3290_, 2);
lean_inc_ref(v_ism1_x27_3289_);
lean_inc_ref(v_motive_3284_);
v___f_3323_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3323_, 0, v_motive_3284_);
lean_closure_set(v___f_3323_, 1, v___x_3285_);
lean_closure_set(v___f_3323_, 2, v___x_3320_);
lean_closure_set(v___f_3323_, 3, v___x_3321_);
lean_closure_set(v___f_3323_, 4, v___x_3322_);
lean_closure_set(v___f_3323_, 5, v_ism1_x27_3289_);
lean_closure_set(v___f_3323_, 6, v_ism2_x27_3313_);
lean_closure_set(v___f_3323_, 7, v_is_3290_);
lean_closure_set(v___f_3323_, 8, v___x_3291_);
lean_inc_ref(v___x_3292_);
v___x_3324_ = lean_array_push(v_is_3290_, v___x_3292_);
v___x_3325_ = l_Lean_Meta_withNewEqs___redArg(v___x_3324_, v_ism1_x27_3289_, v___f_3323_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v_a_3326_; lean_object* v_fst_3327_; lean_object* v_snd_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3429_; 
v_a_3326_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_a_3326_);
lean_dec_ref_known(v___x_3325_, 1);
v_fst_3327_ = lean_ctor_get(v_a_3326_, 0);
v_snd_3328_ = lean_ctor_get(v_a_3326_, 1);
v_isSharedCheck_3429_ = !lean_is_exclusive(v_a_3326_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3330_ = v_a_3326_;
v_isShared_3331_ = v_isSharedCheck_3429_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_snd_3328_);
lean_inc(v_fst_3327_);
lean_dec(v_a_3326_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3429_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3332_ = l_Lean_mkConst(v___x_3293_, v___x_3294_);
v___x_3333_ = l_Lean_mkAppN(v___x_3332_, v_params_3295_);
v___x_3334_ = l_Lean_Expr_app___override(v___x_3333_, v_fst_3327_);
lean_inc_ref(v_is_3290_);
v___x_3335_ = l_Array_append___redArg(v_is_3290_, v___x_3296_);
v___x_3336_ = l_Array_append___redArg(v___x_3335_, v_is_3290_);
v___x_3337_ = l_Array_append___redArg(v___x_3336_, v___x_3297_);
v___x_3338_ = l_Lean_mkAppN(v___x_3334_, v___x_3337_);
lean_dec_ref(v___x_3337_);
lean_inc_ref(v_heq_3298_);
v___x_3339_ = l_Lean_Expr_app___override(v___x_3338_, v_heq_3298_);
v___x_3340_ = l_Lean_InductiveVal_numCtors(v_val_3299_);
lean_inc_ref(v___x_3339_);
v___x_3341_ = l_Lean_Meta_inferArgumentTypesN(v___x_3340_, v___x_3339_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3341_) == 0)
{
lean_object* v_a_3342_; lean_object* v___x_3343_; 
v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_a_3342_);
lean_dec_ref_known(v___x_3341_, 1);
lean_inc_ref(v_alts_3301_);
lean_inc(v_snd_3328_);
v___x_3343_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3300_, v_params_3295_, v_a_3342_, v_snd_3328_, v_alts_3301_, v_sz_3302_, v___x_3303_, v___x_3304_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3343_, 1);
v___x_3345_ = l_Lean_mkAppN(v___x_3339_, v_a_3344_);
lean_dec(v_a_3344_);
v___x_3346_ = l_Lean_mkAppN(v___x_3345_, v_snd_3328_);
lean_dec(v_snd_3328_);
lean_inc_ref(v___x_3305_);
v___x_3347_ = lean_array_push(v___x_3305_, v_motive_3284_);
v___x_3348_ = l_Array_append___redArg(v_params_3295_, v___x_3347_);
lean_dec_ref(v___x_3347_);
v___x_3349_ = l_Array_append___redArg(v___x_3348_, v_is_3290_);
lean_dec_ref(v_is_3290_);
v___x_3350_ = lean_unsigned_to_nat(2u);
v___x_3351_ = lean_mk_empty_array_with_capacity(v___x_3350_);
v___x_3352_ = lean_array_push(v___x_3351_, v___x_3292_);
v___x_3353_ = lean_array_push(v___x_3352_, v___x_3291_);
v___x_3354_ = l_Array_append___redArg(v___x_3349_, v___x_3353_);
lean_dec_ref(v___x_3353_);
v___x_3355_ = lean_array_push(v___x_3305_, v_heq_3298_);
v___x_3356_ = l_Array_append___redArg(v___x_3354_, v___x_3355_);
lean_dec_ref(v___x_3355_);
v___x_3357_ = l_Array_append___redArg(v___x_3356_, v_alts_3301_);
lean_dec_ref(v_alts_3301_);
v___x_3358_ = l_Lean_Meta_mkLambdaFVars(v___x_3357_, v___x_3346_, v___x_3286_, v___x_3287_, v___x_3286_, v___x_3287_, v___x_3288_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec_ref(v___x_3357_);
if (lean_obj_tag(v___x_3358_) == 0)
{
lean_object* v_a_3359_; lean_object* v___x_3360_; 
v_a_3359_ = lean_ctor_get(v___x_3358_, 0);
lean_inc_n(v_a_3359_, 2);
lean_dec_ref_known(v___x_3358_, 1);
lean_inc(v___y_3318_);
lean_inc_ref(v___y_3317_);
lean_inc(v___y_3316_);
lean_inc_ref(v___y_3315_);
v___x_3360_ = lean_infer_type(v_a_3359_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3360_) == 0)
{
lean_object* v_a_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3396_; 
v_a_3361_ = lean_ctor_get(v___x_3360_, 0);
lean_inc(v_a_3361_);
lean_dec_ref_known(v___x_3360_, 1);
v___x_3362_ = lean_box(1);
lean_inc(v_declName_3306_);
v___x_3363_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3306_, v_levelParams_3307_, v_a_3361_, v_a_3359_, v___x_3362_, v___y_3318_);
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3396_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3396_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set_tag(v___x_3366_, 1);
v___x_3369_ = v___x_3366_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___f_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3381_; 
v___x_3370_ = lean_box(v___x_3286_);
lean_inc_ref(v___x_3369_);
v___f_3371_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3371_, 0, v___x_3369_);
lean_closure_set(v___f_3371_, 1, v___x_3370_);
v___x_3372_ = lean_nat_add(v_numIndices_3308_, v___x_3309_);
lean_inc(v___x_3310_);
v___x_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3310_);
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_mk_empty_array_with_capacity(v___x_3309_);
v___x_3376_ = lean_array_push(v___x_3375_, v___x_3374_);
v___x_3377_ = lean_array_push(v___x_3376_, v___x_3374_);
v___x_3378_ = lean_array_push(v___x_3377_, v___x_3374_);
v___x_3379_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 1, v___x_3379_);
lean_ctor_set(v___x_3330_, 0, v___x_3310_);
v___x_3381_ = v___x_3330_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3310_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
lean_object* v___x_3382_; uint8_t v___y_3384_; uint8_t v___x_3393_; 
v___x_3382_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3382_, 0, v_numParams_3311_);
lean_ctor_set(v___x_3382_, 1, v___x_3372_);
lean_ctor_set(v___x_3382_, 2, v_snd_3312_);
lean_ctor_set(v___x_3382_, 3, v___x_3373_);
lean_ctor_set(v___x_3382_, 4, v___x_3378_);
lean_ctor_set(v___x_3382_, 5, v___x_3381_);
v___x_3393_ = l_Lean_isPrivateName(v_declName_3306_);
if (v___x_3393_ == 0)
{
v___y_3384_ = v___x_3287_;
goto v___jp_3383_;
}
else
{
v___y_3384_ = v___x_3286_;
goto v___jp_3383_;
}
v___jp_3383_:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3371_, v___y_3384_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec_ref_known(v___x_3385_, 1);
v___x_3386_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3306_);
v___x_3387_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(v___x_3386_, v_declName_3306_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v___x_3388_; uint8_t v___x_3389_; lean_object* v___x_3390_; 
lean_dec_ref_known(v___x_3387_, 1);
lean_inc_n(v_declName_3306_, 2);
v___x_3388_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3306_, v___x_3382_, v___y_3316_, v___y_3318_);
lean_dec_ref(v___x_3388_);
v___x_3389_ = 0;
v___x_3390_ = l_Lean_Meta_setInlineAttribute(v_declName_3306_, v___x_3389_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v___x_3391_; 
lean_dec_ref_known(v___x_3390_, 1);
v___x_3391_ = l_Lean_enableRealizationsForConst(v_declName_3306_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v___x_3392_; 
lean_dec_ref_known(v___x_3391_, 1);
v___x_3392_ = l_Lean_compileDecl(v___x_3369_, v___x_3287_, v___y_3317_, v___y_3318_);
return v___x_3392_;
}
else
{
lean_dec_ref(v___x_3369_);
return v___x_3391_;
}
}
else
{
lean_dec_ref(v___x_3369_);
lean_dec(v_declName_3306_);
return v___x_3390_;
}
}
else
{
lean_dec_ref_known(v___x_3382_, 6);
lean_dec_ref(v___x_3369_);
lean_dec(v_declName_3306_);
return v___x_3387_;
}
}
else
{
lean_dec_ref_known(v___x_3382_, 6);
lean_dec_ref(v___x_3369_);
lean_dec(v_declName_3306_);
return v___x_3385_;
}
}
}
}
}
}
else
{
lean_object* v_a_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
lean_dec(v_a_3359_);
lean_del_object(v___x_3330_);
lean_dec_ref(v_snd_3312_);
lean_dec(v_numParams_3311_);
lean_dec(v___x_3310_);
lean_dec(v_levelParams_3307_);
lean_dec(v_declName_3306_);
v_a_3397_ = lean_ctor_get(v___x_3360_, 0);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3360_);
if (v_isSharedCheck_3404_ == 0)
{
v___x_3399_ = v___x_3360_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_inc(v_a_3397_);
lean_dec(v___x_3360_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3397_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
}
else
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3412_; 
lean_del_object(v___x_3330_);
lean_dec_ref(v_snd_3312_);
lean_dec(v_numParams_3311_);
lean_dec(v___x_3310_);
lean_dec(v_levelParams_3307_);
lean_dec(v_declName_3306_);
v_a_3405_ = lean_ctor_get(v___x_3358_, 0);
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3412_ == 0)
{
v___x_3407_ = v___x_3358_;
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3358_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3412_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3410_; 
if (v_isShared_3408_ == 0)
{
v___x_3410_ = v___x_3407_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v_a_3405_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec_ref(v___x_3339_);
lean_del_object(v___x_3330_);
lean_dec(v_snd_3328_);
lean_dec_ref(v_snd_3312_);
lean_dec(v_numParams_3311_);
lean_dec(v___x_3310_);
lean_dec(v_levelParams_3307_);
lean_dec(v_declName_3306_);
lean_dec_ref(v___x_3305_);
lean_dec_ref(v_alts_3301_);
lean_dec_ref(v_heq_3298_);
lean_dec_ref(v_params_3295_);
lean_dec_ref(v___x_3292_);
lean_dec_ref(v___x_3291_);
lean_dec_ref(v_is_3290_);
lean_dec_ref(v_motive_3284_);
v_a_3413_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3343_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3343_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
else
{
lean_object* v_a_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3428_; 
lean_dec_ref(v___x_3339_);
lean_del_object(v___x_3330_);
lean_dec(v_snd_3328_);
lean_dec_ref(v_snd_3312_);
lean_dec(v_numParams_3311_);
lean_dec(v___x_3310_);
lean_dec(v_levelParams_3307_);
lean_dec(v_declName_3306_);
lean_dec_ref(v___x_3305_);
lean_dec_ref(v___x_3304_);
lean_dec_ref(v_alts_3301_);
lean_dec(v_tail_3300_);
lean_dec_ref(v_heq_3298_);
lean_dec_ref(v_params_3295_);
lean_dec_ref(v___x_3292_);
lean_dec_ref(v___x_3291_);
lean_dec_ref(v_is_3290_);
lean_dec_ref(v_motive_3284_);
v_a_3421_ = lean_ctor_get(v___x_3341_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3423_ = v___x_3341_;
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_a_3421_);
lean_dec(v___x_3341_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3428_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
lean_object* v___x_3426_; 
if (v_isShared_3424_ == 0)
{
v___x_3426_ = v___x_3423_;
goto v_reusejp_3425_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_a_3421_);
v___x_3426_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3425_;
}
v_reusejp_3425_:
{
return v___x_3426_;
}
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v_snd_3312_);
lean_dec(v_numParams_3311_);
lean_dec(v___x_3310_);
lean_dec(v_levelParams_3307_);
lean_dec(v_declName_3306_);
lean_dec_ref(v___x_3305_);
lean_dec_ref(v___x_3304_);
lean_dec_ref(v_alts_3301_);
lean_dec(v_tail_3300_);
lean_dec_ref(v_heq_3298_);
lean_dec_ref(v_params_3295_);
lean_dec(v___x_3294_);
lean_dec(v___x_3293_);
lean_dec_ref(v___x_3292_);
lean_dec_ref(v___x_3291_);
lean_dec_ref(v_is_3290_);
lean_dec_ref(v_motive_3284_);
v_a_3430_ = lean_ctor_get(v___x_3325_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3325_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3325_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3325_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3438_ = _args[0];
lean_object* v___x_3439_ = _args[1];
lean_object* v___x_3440_ = _args[2];
lean_object* v___x_3441_ = _args[3];
lean_object* v___x_3442_ = _args[4];
lean_object* v_ism1_x27_3443_ = _args[5];
lean_object* v_is_3444_ = _args[6];
lean_object* v___x_3445_ = _args[7];
lean_object* v___x_3446_ = _args[8];
lean_object* v___x_3447_ = _args[9];
lean_object* v___x_3448_ = _args[10];
lean_object* v_params_3449_ = _args[11];
lean_object* v___x_3450_ = _args[12];
lean_object* v___x_3451_ = _args[13];
lean_object* v_heq_3452_ = _args[14];
lean_object* v_val_3453_ = _args[15];
lean_object* v_tail_3454_ = _args[16];
lean_object* v_alts_3455_ = _args[17];
lean_object* v_sz_3456_ = _args[18];
lean_object* v___x_3457_ = _args[19];
lean_object* v___x_3458_ = _args[20];
lean_object* v___x_3459_ = _args[21];
lean_object* v_declName_3460_ = _args[22];
lean_object* v_levelParams_3461_ = _args[23];
lean_object* v_numIndices_3462_ = _args[24];
lean_object* v___x_3463_ = _args[25];
lean_object* v___x_3464_ = _args[26];
lean_object* v_numParams_3465_ = _args[27];
lean_object* v_snd_3466_ = _args[28];
lean_object* v_ism2_x27_3467_ = _args[29];
lean_object* v_x_3468_ = _args[30];
lean_object* v___y_3469_ = _args[31];
lean_object* v___y_3470_ = _args[32];
lean_object* v___y_3471_ = _args[33];
lean_object* v___y_3472_ = _args[34];
lean_object* v___y_3473_ = _args[35];
_start:
{
uint8_t v___x_15561__boxed_3474_; uint8_t v___x_15562__boxed_3475_; uint8_t v___x_15563__boxed_3476_; size_t v_sz_boxed_3477_; size_t v___x_15572__boxed_3478_; lean_object* v_res_3479_; 
v___x_15561__boxed_3474_ = lean_unbox(v___x_3440_);
v___x_15562__boxed_3475_ = lean_unbox(v___x_3441_);
v___x_15563__boxed_3476_ = lean_unbox(v___x_3442_);
v_sz_boxed_3477_ = lean_unbox_usize(v_sz_3456_);
lean_dec(v_sz_3456_);
v___x_15572__boxed_3478_ = lean_unbox_usize(v___x_3457_);
lean_dec(v___x_3457_);
v_res_3479_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3438_, v___x_3439_, v___x_15561__boxed_3474_, v___x_15562__boxed_3475_, v___x_15563__boxed_3476_, v_ism1_x27_3443_, v_is_3444_, v___x_3445_, v___x_3446_, v___x_3447_, v___x_3448_, v_params_3449_, v___x_3450_, v___x_3451_, v_heq_3452_, v_val_3453_, v_tail_3454_, v_alts_3455_, v_sz_boxed_3477_, v___x_15572__boxed_3478_, v___x_3458_, v___x_3459_, v_declName_3460_, v_levelParams_3461_, v_numIndices_3462_, v___x_3463_, v___x_3464_, v_numParams_3465_, v_snd_3466_, v_ism2_x27_3467_, v_x_3468_, v___y_3469_, v___y_3470_, v___y_3471_, v___y_3472_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec_ref(v_x_3468_);
lean_dec(v___x_3463_);
lean_dec(v_numIndices_3462_);
lean_dec_ref(v_val_3453_);
lean_dec_ref(v___x_3451_);
lean_dec_ref(v___x_3450_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3480_, lean_object* v___x_3481_, uint8_t v___x_3482_, uint8_t v___x_3483_, uint8_t v___x_3484_, lean_object* v_is_3485_, lean_object* v___x_3486_, lean_object* v___x_3487_, lean_object* v___x_3488_, lean_object* v___x_3489_, lean_object* v_params_3490_, lean_object* v___x_3491_, lean_object* v___x_3492_, lean_object* v_heq_3493_, lean_object* v_val_3494_, lean_object* v_tail_3495_, lean_object* v_alts_3496_, size_t v_sz_3497_, size_t v___x_3498_, lean_object* v___x_3499_, lean_object* v___x_3500_, lean_object* v_declName_3501_, lean_object* v_levelParams_3502_, lean_object* v_numIndices_3503_, lean_object* v___x_3504_, lean_object* v___x_3505_, lean_object* v_numParams_3506_, lean_object* v_snd_3507_, lean_object* v___x_3508_, lean_object* v___x_3509_, lean_object* v_ism1_x27_3510_, lean_object* v_x_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___f_3522_; lean_object* v___x_3523_; 
v___x_3517_ = lean_box(v___x_3482_);
v___x_3518_ = lean_box(v___x_3483_);
v___x_3519_ = lean_box(v___x_3484_);
v___x_3520_ = lean_box_usize(v_sz_3497_);
v___x_3521_ = lean_box_usize(v___x_3498_);
v___f_3522_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3522_, 0, v_motive_3480_);
lean_closure_set(v___f_3522_, 1, v___x_3481_);
lean_closure_set(v___f_3522_, 2, v___x_3517_);
lean_closure_set(v___f_3522_, 3, v___x_3518_);
lean_closure_set(v___f_3522_, 4, v___x_3519_);
lean_closure_set(v___f_3522_, 5, v_ism1_x27_3510_);
lean_closure_set(v___f_3522_, 6, v_is_3485_);
lean_closure_set(v___f_3522_, 7, v___x_3486_);
lean_closure_set(v___f_3522_, 8, v___x_3487_);
lean_closure_set(v___f_3522_, 9, v___x_3488_);
lean_closure_set(v___f_3522_, 10, v___x_3489_);
lean_closure_set(v___f_3522_, 11, v_params_3490_);
lean_closure_set(v___f_3522_, 12, v___x_3491_);
lean_closure_set(v___f_3522_, 13, v___x_3492_);
lean_closure_set(v___f_3522_, 14, v_heq_3493_);
lean_closure_set(v___f_3522_, 15, v_val_3494_);
lean_closure_set(v___f_3522_, 16, v_tail_3495_);
lean_closure_set(v___f_3522_, 17, v_alts_3496_);
lean_closure_set(v___f_3522_, 18, v___x_3520_);
lean_closure_set(v___f_3522_, 19, v___x_3521_);
lean_closure_set(v___f_3522_, 20, v___x_3499_);
lean_closure_set(v___f_3522_, 21, v___x_3500_);
lean_closure_set(v___f_3522_, 22, v_declName_3501_);
lean_closure_set(v___f_3522_, 23, v_levelParams_3502_);
lean_closure_set(v___f_3522_, 24, v_numIndices_3503_);
lean_closure_set(v___f_3522_, 25, v___x_3504_);
lean_closure_set(v___f_3522_, 26, v___x_3505_);
lean_closure_set(v___f_3522_, 27, v_numParams_3506_);
lean_closure_set(v___f_3522_, 28, v_snd_3507_);
v___x_3523_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3508_, v___x_3509_, v___f_3522_, v___x_3482_, v___x_3482_, v___y_3512_, v___y_3513_, v___y_3514_, v___y_3515_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3524_ = _args[0];
lean_object* v___x_3525_ = _args[1];
lean_object* v___x_3526_ = _args[2];
lean_object* v___x_3527_ = _args[3];
lean_object* v___x_3528_ = _args[4];
lean_object* v_is_3529_ = _args[5];
lean_object* v___x_3530_ = _args[6];
lean_object* v___x_3531_ = _args[7];
lean_object* v___x_3532_ = _args[8];
lean_object* v___x_3533_ = _args[9];
lean_object* v_params_3534_ = _args[10];
lean_object* v___x_3535_ = _args[11];
lean_object* v___x_3536_ = _args[12];
lean_object* v_heq_3537_ = _args[13];
lean_object* v_val_3538_ = _args[14];
lean_object* v_tail_3539_ = _args[15];
lean_object* v_alts_3540_ = _args[16];
lean_object* v_sz_3541_ = _args[17];
lean_object* v___x_3542_ = _args[18];
lean_object* v___x_3543_ = _args[19];
lean_object* v___x_3544_ = _args[20];
lean_object* v_declName_3545_ = _args[21];
lean_object* v_levelParams_3546_ = _args[22];
lean_object* v_numIndices_3547_ = _args[23];
lean_object* v___x_3548_ = _args[24];
lean_object* v___x_3549_ = _args[25];
lean_object* v_numParams_3550_ = _args[26];
lean_object* v_snd_3551_ = _args[27];
lean_object* v___x_3552_ = _args[28];
lean_object* v___x_3553_ = _args[29];
lean_object* v_ism1_x27_3554_ = _args[30];
lean_object* v_x_3555_ = _args[31];
lean_object* v___y_3556_ = _args[32];
lean_object* v___y_3557_ = _args[33];
lean_object* v___y_3558_ = _args[34];
lean_object* v___y_3559_ = _args[35];
lean_object* v___y_3560_ = _args[36];
_start:
{
uint8_t v___x_15883__boxed_3561_; uint8_t v___x_15884__boxed_3562_; uint8_t v___x_15885__boxed_3563_; size_t v_sz_boxed_3564_; size_t v___x_15894__boxed_3565_; lean_object* v_res_3566_; 
v___x_15883__boxed_3561_ = lean_unbox(v___x_3526_);
v___x_15884__boxed_3562_ = lean_unbox(v___x_3527_);
v___x_15885__boxed_3563_ = lean_unbox(v___x_3528_);
v_sz_boxed_3564_ = lean_unbox_usize(v_sz_3541_);
lean_dec(v_sz_3541_);
v___x_15894__boxed_3565_ = lean_unbox_usize(v___x_3542_);
lean_dec(v___x_3542_);
v_res_3566_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3524_, v___x_3525_, v___x_15883__boxed_3561_, v___x_15884__boxed_3562_, v___x_15885__boxed_3563_, v_is_3529_, v___x_3530_, v___x_3531_, v___x_3532_, v___x_3533_, v_params_3534_, v___x_3535_, v___x_3536_, v_heq_3537_, v_val_3538_, v_tail_3539_, v_alts_3540_, v_sz_boxed_3564_, v___x_15894__boxed_3565_, v___x_3543_, v___x_3544_, v_declName_3545_, v_levelParams_3546_, v_numIndices_3547_, v___x_3548_, v___x_3549_, v_numParams_3550_, v_snd_3551_, v___x_3552_, v___x_3553_, v_ism1_x27_3554_, v_x_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec(v___y_3557_);
lean_dec_ref(v___y_3556_);
lean_dec_ref(v_x_3555_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3567_, lean_object* v___x_3568_, lean_object* v_motive_3569_, lean_object* v___x_3570_, uint8_t v___x_3571_, uint8_t v___x_3572_, uint8_t v___x_3573_, lean_object* v_is_3574_, lean_object* v___x_3575_, lean_object* v___x_3576_, lean_object* v___x_3577_, lean_object* v___x_3578_, lean_object* v_params_3579_, lean_object* v___x_3580_, lean_object* v___x_3581_, lean_object* v_heq_3582_, lean_object* v_val_3583_, lean_object* v_tail_3584_, size_t v_sz_3585_, size_t v___x_3586_, lean_object* v___x_3587_, lean_object* v___x_3588_, lean_object* v_declName_3589_, lean_object* v_levelParams_3590_, lean_object* v___x_3591_, lean_object* v___x_3592_, lean_object* v_numParams_3593_, lean_object* v_snd_3594_, lean_object* v___x_3595_, lean_object* v_alts_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___f_3609_; lean_object* v___x_3610_; 
v___x_3602_ = lean_nat_add(v_numIndices_3567_, v___x_3568_);
v___x_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
v___x_3604_ = lean_box(v___x_3571_);
v___x_3605_ = lean_box(v___x_3572_);
v___x_3606_ = lean_box(v___x_3573_);
v___x_3607_ = lean_box_usize(v_sz_3585_);
v___x_3608_ = lean_box_usize(v___x_3586_);
lean_inc_ref(v___x_3603_);
lean_inc_ref(v___x_3595_);
v___f_3609_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3609_, 0, v_motive_3569_);
lean_closure_set(v___f_3609_, 1, v___x_3570_);
lean_closure_set(v___f_3609_, 2, v___x_3604_);
lean_closure_set(v___f_3609_, 3, v___x_3605_);
lean_closure_set(v___f_3609_, 4, v___x_3606_);
lean_closure_set(v___f_3609_, 5, v_is_3574_);
lean_closure_set(v___f_3609_, 6, v___x_3575_);
lean_closure_set(v___f_3609_, 7, v___x_3576_);
lean_closure_set(v___f_3609_, 8, v___x_3577_);
lean_closure_set(v___f_3609_, 9, v___x_3578_);
lean_closure_set(v___f_3609_, 10, v_params_3579_);
lean_closure_set(v___f_3609_, 11, v___x_3580_);
lean_closure_set(v___f_3609_, 12, v___x_3581_);
lean_closure_set(v___f_3609_, 13, v_heq_3582_);
lean_closure_set(v___f_3609_, 14, v_val_3583_);
lean_closure_set(v___f_3609_, 15, v_tail_3584_);
lean_closure_set(v___f_3609_, 16, v_alts_3596_);
lean_closure_set(v___f_3609_, 17, v___x_3607_);
lean_closure_set(v___f_3609_, 18, v___x_3608_);
lean_closure_set(v___f_3609_, 19, v___x_3587_);
lean_closure_set(v___f_3609_, 20, v___x_3588_);
lean_closure_set(v___f_3609_, 21, v_declName_3589_);
lean_closure_set(v___f_3609_, 22, v_levelParams_3590_);
lean_closure_set(v___f_3609_, 23, v_numIndices_3567_);
lean_closure_set(v___f_3609_, 24, v___x_3591_);
lean_closure_set(v___f_3609_, 25, v___x_3592_);
lean_closure_set(v___f_3609_, 26, v_numParams_3593_);
lean_closure_set(v___f_3609_, 27, v_snd_3594_);
lean_closure_set(v___f_3609_, 28, v___x_3595_);
lean_closure_set(v___f_3609_, 29, v___x_3603_);
v___x_3610_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3595_, v___x_3603_, v___f_3609_, v___x_3571_, v___x_3571_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3611_ = _args[0];
lean_object* v___x_3612_ = _args[1];
lean_object* v_motive_3613_ = _args[2];
lean_object* v___x_3614_ = _args[3];
lean_object* v___x_3615_ = _args[4];
lean_object* v___x_3616_ = _args[5];
lean_object* v___x_3617_ = _args[6];
lean_object* v_is_3618_ = _args[7];
lean_object* v___x_3619_ = _args[8];
lean_object* v___x_3620_ = _args[9];
lean_object* v___x_3621_ = _args[10];
lean_object* v___x_3622_ = _args[11];
lean_object* v_params_3623_ = _args[12];
lean_object* v___x_3624_ = _args[13];
lean_object* v___x_3625_ = _args[14];
lean_object* v_heq_3626_ = _args[15];
lean_object* v_val_3627_ = _args[16];
lean_object* v_tail_3628_ = _args[17];
lean_object* v_sz_3629_ = _args[18];
lean_object* v___x_3630_ = _args[19];
lean_object* v___x_3631_ = _args[20];
lean_object* v___x_3632_ = _args[21];
lean_object* v_declName_3633_ = _args[22];
lean_object* v_levelParams_3634_ = _args[23];
lean_object* v___x_3635_ = _args[24];
lean_object* v___x_3636_ = _args[25];
lean_object* v_numParams_3637_ = _args[26];
lean_object* v_snd_3638_ = _args[27];
lean_object* v___x_3639_ = _args[28];
lean_object* v_alts_3640_ = _args[29];
lean_object* v___y_3641_ = _args[30];
lean_object* v___y_3642_ = _args[31];
lean_object* v___y_3643_ = _args[32];
lean_object* v___y_3644_ = _args[33];
lean_object* v___y_3645_ = _args[34];
_start:
{
uint8_t v___x_15976__boxed_3646_; uint8_t v___x_15977__boxed_3647_; uint8_t v___x_15978__boxed_3648_; size_t v_sz_boxed_3649_; size_t v___x_15987__boxed_3650_; lean_object* v_res_3651_; 
v___x_15976__boxed_3646_ = lean_unbox(v___x_3615_);
v___x_15977__boxed_3647_ = lean_unbox(v___x_3616_);
v___x_15978__boxed_3648_ = lean_unbox(v___x_3617_);
v_sz_boxed_3649_ = lean_unbox_usize(v_sz_3629_);
lean_dec(v_sz_3629_);
v___x_15987__boxed_3650_ = lean_unbox_usize(v___x_3630_);
lean_dec(v___x_3630_);
v_res_3651_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3611_, v___x_3612_, v_motive_3613_, v___x_3614_, v___x_15976__boxed_3646_, v___x_15977__boxed_3647_, v___x_15978__boxed_3648_, v_is_3618_, v___x_3619_, v___x_3620_, v___x_3621_, v___x_3622_, v_params_3623_, v___x_3624_, v___x_3625_, v_heq_3626_, v_val_3627_, v_tail_3628_, v_sz_boxed_3649_, v___x_15987__boxed_3650_, v___x_3631_, v___x_3632_, v_declName_3633_, v_levelParams_3634_, v___x_3635_, v___x_3636_, v_numParams_3637_, v_snd_3638_, v___x_3639_, v_alts_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___x_3612_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3652_, lean_object* v_declInfos_3653_, lean_object* v_k_3654_, lean_object* v_kind_3655_, lean_object* v_x_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
uint8_t v_kind_boxed_3662_; lean_object* v_res_3663_; 
v_kind_boxed_3662_ = lean_unbox(v_kind_3655_);
v_res_3663_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3652_, v_declInfos_3653_, v_k_3654_, v_kind_boxed_3662_, v_x_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3664_, lean_object* v_k_3665_, uint8_t v_kind_3666_, lean_object* v_acc_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___x_3673_; lean_object* v_toApplicative_3674_; lean_object* v_toFunctor_3675_; lean_object* v_toSeq_3676_; lean_object* v_toSeqLeft_3677_; lean_object* v_toSeqRight_3678_; lean_object* v___f_3679_; lean_object* v___f_3680_; lean_object* v___f_3681_; lean_object* v___f_3682_; lean_object* v___x_3683_; lean_object* v___f_3684_; lean_object* v___f_3685_; lean_object* v___f_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v_toApplicative_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3748_; 
v___x_3673_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1);
v_toApplicative_3674_ = lean_ctor_get(v___x_3673_, 0);
v_toFunctor_3675_ = lean_ctor_get(v_toApplicative_3674_, 0);
v_toSeq_3676_ = lean_ctor_get(v_toApplicative_3674_, 2);
v_toSeqLeft_3677_ = lean_ctor_get(v_toApplicative_3674_, 3);
v_toSeqRight_3678_ = lean_ctor_get(v_toApplicative_3674_, 4);
v___f_3679_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2));
v___f_3680_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3));
lean_inc_ref_n(v_toFunctor_3675_, 2);
v___f_3681_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3681_, 0, v_toFunctor_3675_);
v___f_3682_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3682_, 0, v_toFunctor_3675_);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___f_3681_);
lean_ctor_set(v___x_3683_, 1, v___f_3682_);
lean_inc(v_toSeqRight_3678_);
v___f_3684_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3684_, 0, v_toSeqRight_3678_);
lean_inc(v_toSeqLeft_3677_);
v___f_3685_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3685_, 0, v_toSeqLeft_3677_);
lean_inc(v_toSeq_3676_);
v___f_3686_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3686_, 0, v_toSeq_3676_);
v___x_3687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3683_);
lean_ctor_set(v___x_3687_, 1, v___f_3679_);
lean_ctor_set(v___x_3687_, 2, v___f_3686_);
lean_ctor_set(v___x_3687_, 3, v___f_3685_);
lean_ctor_set(v___x_3687_, 4, v___f_3684_);
v___x_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
lean_ctor_set(v___x_3688_, 1, v___f_3680_);
v___x_3689_ = l_StateRefT_x27_instMonad___redArg(v___x_3688_);
v_toApplicative_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3748_ == 0)
{
lean_object* v_unused_3749_; 
v_unused_3749_ = lean_ctor_get(v___x_3689_, 1);
lean_dec(v_unused_3749_);
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3748_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_toApplicative_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3748_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v_toFunctor_3694_; lean_object* v_toSeq_3695_; lean_object* v_toSeqLeft_3696_; lean_object* v_toSeqRight_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3746_; 
v_toFunctor_3694_ = lean_ctor_get(v_toApplicative_3690_, 0);
v_toSeq_3695_ = lean_ctor_get(v_toApplicative_3690_, 2);
v_toSeqLeft_3696_ = lean_ctor_get(v_toApplicative_3690_, 3);
v_toSeqRight_3697_ = lean_ctor_get(v_toApplicative_3690_, 4);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_toApplicative_3690_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; 
v_unused_3747_ = lean_ctor_get(v_toApplicative_3690_, 1);
lean_dec(v_unused_3747_);
v___x_3699_ = v_toApplicative_3690_;
v_isShared_3700_ = v_isSharedCheck_3746_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_toSeqRight_3697_);
lean_inc(v_toSeqLeft_3696_);
lean_inc(v_toSeq_3695_);
lean_inc(v_toFunctor_3694_);
lean_dec(v_toApplicative_3690_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3746_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___f_3701_; lean_object* v___f_3702_; lean_object* v___f_3703_; lean_object* v___f_3704_; lean_object* v___x_3705_; lean_object* v___f_3706_; lean_object* v___f_3707_; lean_object* v___f_3708_; lean_object* v___x_3710_; 
v___f_3701_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4));
v___f_3702_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5));
lean_inc_ref(v_toFunctor_3694_);
v___f_3703_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3703_, 0, v_toFunctor_3694_);
v___f_3704_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3704_, 0, v_toFunctor_3694_);
v___x_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3705_, 0, v___f_3703_);
lean_ctor_set(v___x_3705_, 1, v___f_3704_);
v___f_3706_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3706_, 0, v_toSeqRight_3697_);
v___f_3707_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3707_, 0, v_toSeqLeft_3696_);
v___f_3708_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3708_, 0, v_toSeq_3695_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 4, v___f_3706_);
lean_ctor_set(v___x_3699_, 3, v___f_3707_);
lean_ctor_set(v___x_3699_, 2, v___f_3708_);
lean_ctor_set(v___x_3699_, 1, v___f_3701_);
lean_ctor_set(v___x_3699_, 0, v___x_3705_);
v___x_3710_ = v___x_3699_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3705_);
lean_ctor_set(v_reuseFailAlloc_3745_, 1, v___f_3701_);
lean_ctor_set(v_reuseFailAlloc_3745_, 2, v___f_3708_);
lean_ctor_set(v_reuseFailAlloc_3745_, 3, v___f_3707_);
lean_ctor_set(v_reuseFailAlloc_3745_, 4, v___f_3706_);
v___x_3710_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
lean_object* v___x_3712_; 
if (v_isShared_3693_ == 0)
{
lean_ctor_set(v___x_3692_, 1, v___f_3702_);
lean_ctor_set(v___x_3692_, 0, v___x_3710_);
v___x_3712_ = v___x_3692_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3710_);
lean_ctor_set(v_reuseFailAlloc_3744_, 1, v___f_3702_);
v___x_3712_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
lean_object* v___x_3713_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3713_ = lean_array_get_size(v_acc_3667_);
v___x_3714_ = lean_array_get_size(v_declInfos_3664_);
v___x_3715_ = lean_nat_dec_lt(v___x_3713_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; 
lean_dec_ref(v___x_3712_);
lean_dec_ref(v_declInfos_3664_);
lean_inc(v___y_3671_);
lean_inc_ref(v___y_3670_);
lean_inc(v___y_3669_);
lean_inc_ref(v___y_3668_);
v___x_3716_ = lean_apply_6(v_k_3665_, v_acc_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, lean_box(0));
return v___x_3716_;
}
else
{
lean_object* v___x_3717_; uint8_t v___x_3718_; lean_object* v___x_3719_; lean_object* v___f_3720_; lean_object* v___f_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v_snd_3726_; lean_object* v_fst_3727_; lean_object* v_fst_3728_; lean_object* v_snd_3729_; lean_object* v___x_3730_; lean_object* v___f_3731_; lean_object* v___x_3732_; 
v___x_3717_ = lean_box(0);
v___x_3718_ = 0;
v___x_3719_ = l_Lean_instInhabitedExpr;
v___f_3720_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3720_, 0, v___x_3712_);
lean_closure_set(v___f_3720_, 1, v___x_3719_);
v___f_3721_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3721_, 0, v___f_3720_);
v___x_3722_ = lean_box(v___x_3718_);
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
lean_ctor_set(v___x_3723_, 1, v___f_3721_);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3717_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = lean_array_get(v___x_3724_, v_declInfos_3664_, v___x_3713_);
lean_dec_ref_known(v___x_3724_, 2);
v_snd_3726_ = lean_ctor_get(v___x_3725_, 1);
lean_inc(v_snd_3726_);
v_fst_3727_ = lean_ctor_get(v___x_3725_, 0);
lean_inc(v_fst_3727_);
lean_dec(v___x_3725_);
v_fst_3728_ = lean_ctor_get(v_snd_3726_, 0);
lean_inc(v_fst_3728_);
v_snd_3729_ = lean_ctor_get(v_snd_3726_, 1);
lean_inc(v_snd_3729_);
lean_dec(v_snd_3726_);
v___x_3730_ = lean_box(v_kind_3666_);
lean_inc_ref(v_acc_3667_);
v___f_3731_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3731_, 0, v_acc_3667_);
lean_closure_set(v___f_3731_, 1, v_declInfos_3664_);
lean_closure_set(v___f_3731_, 2, v_k_3665_);
lean_closure_set(v___f_3731_, 3, v___x_3730_);
lean_inc(v___y_3671_);
lean_inc_ref(v___y_3670_);
lean_inc(v___y_3669_);
lean_inc_ref(v___y_3668_);
v___x_3732_ = lean_apply_6(v_snd_3729_, v_acc_3667_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_, lean_box(0));
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; uint8_t v___x_3734_; lean_object* v___x_3735_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___x_3732_, 1);
v___x_3734_ = lean_unbox(v_fst_3728_);
lean_dec(v_fst_3728_);
v___x_3735_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3727_, v___x_3734_, v_a_3733_, v___f_3731_, v_kind_3666_, v___y_3668_, v___y_3669_, v___y_3670_, v___y_3671_);
return v___x_3735_;
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec_ref(v___f_3731_);
lean_dec(v_fst_3728_);
lean_dec(v_fst_3727_);
v_a_3736_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3732_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3732_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3750_, lean_object* v_declInfos_3751_, lean_object* v_k_3752_, uint8_t v_kind_3753_, lean_object* v_x_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3760_ = lean_array_push(v_acc_3750_, v_x_3754_);
v___x_3761_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3751_, v_k_3752_, v_kind_3753_, v___x_3760_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
return v___x_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3762_, lean_object* v_k_3763_, lean_object* v_kind_3764_, lean_object* v_acc_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
uint8_t v_kind_boxed_3771_; lean_object* v_res_3772_; 
v_kind_boxed_3771_ = lean_unbox(v_kind_3764_);
v_res_3772_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3762_, v_k_3763_, v_kind_boxed_3771_, v_acc_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3773_, lean_object* v_k_3774_, uint8_t v_kind_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; 
v___x_3781_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0));
v___x_3782_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3773_, v_k_3774_, v_kind_3775_, v___x_3781_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
return v___x_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3783_, lean_object* v_k_3784_, lean_object* v_kind_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_){
_start:
{
uint8_t v_kind_boxed_3791_; lean_object* v_res_3792_; 
v_kind_boxed_3791_ = lean_unbox(v_kind_3785_);
v_res_3792_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3783_, v_k_3784_, v_kind_boxed_3791_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
lean_dec(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec(v___y_3787_);
lean_dec_ref(v___y_3786_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3793_, lean_object* v_k_3794_, uint8_t v_kind_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
size_t v_sz_3801_; size_t v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_sz_3801_ = lean_array_size(v_declInfos_3793_);
v___x_3802_ = ((size_t)0ULL);
v___x_3803_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(v_sz_3801_, v___x_3802_, v_declInfos_3793_);
v___x_3804_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3803_, v_k_3794_, v_kind_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3805_, lean_object* v_k_3806_, lean_object* v_kind_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
uint8_t v_kind_boxed_3813_; lean_object* v_res_3814_; 
v_kind_boxed_3813_ = lean_unbox(v_kind_3807_);
v_res_3814_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3805_, v_k_3806_, v_kind_boxed_3813_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3815_, lean_object* v_k_3816_, uint8_t v_kind_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
size_t v_sz_3823_; size_t v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v_sz_3823_ = lean_array_size(v_declInfos_3815_);
v___x_3824_ = ((size_t)0ULL);
v___x_3825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3823_, v___x_3824_, v_declInfos_3815_);
v___x_3826_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3825_, v_k_3816_, v_kind_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
return v___x_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3827_, lean_object* v_k_3828_, lean_object* v_kind_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
uint8_t v_kind_boxed_3835_; lean_object* v_res_3836_; 
v_kind_boxed_3835_ = lean_unbox(v_kind_3829_);
v_res_3836_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3827_, v_k_3828_, v_kind_boxed_3835_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
return v_res_3836_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = lean_box(0);
v___x_3840_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3841_ = l_Lean_mkConst(v___x_3840_, v___x_3839_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3842_, lean_object* v_v_3843_, lean_object* v___x_3844_, lean_object* v___x_3845_, lean_object* v___x_3846_, lean_object* v_motive_3847_, uint8_t v___x_3848_, uint8_t v___x_3849_, uint8_t v___x_3850_, lean_object* v_zs12_3851_, lean_object* v_is_3852_, lean_object* v_fields1_3853_, lean_object* v_fields2_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v_e_3870_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
lean_inc_ref(v___x_3846_);
v___x_3880_ = l_Lean_mkAppN(v___x_3846_, v_fields1_3853_);
v___x_3881_ = l_Lean_mkAppN(v___x_3846_, v_fields2_3854_);
lean_inc(v___x_3844_);
v___x_3882_ = l_Lean_mkNatLit(v___x_3844_);
v___x_3883_ = l_Lean_Meta_mkEqRefl(v___x_3882_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
lean_inc(v_a_3884_);
lean_dec_ref_known(v___x_3883_, 1);
v___x_3885_ = lean_unsigned_to_nat(3u);
v___x_3886_ = lean_mk_empty_array_with_capacity(v___x_3885_);
v___x_3887_ = lean_array_push(v___x_3886_, v___x_3880_);
v___x_3888_ = lean_array_push(v___x_3887_, v___x_3881_);
v___x_3889_ = lean_array_push(v___x_3888_, v_a_3884_);
v___x_3890_ = l_Array_append___redArg(v_is_3852_, v___x_3889_);
lean_dec_ref(v___x_3889_);
v___x_3891_ = l_Lean_mkAppN(v_motive_3847_, v___x_3890_);
lean_dec_ref(v___x_3890_);
v___x_3892_ = l_Lean_Meta_mkForallFVars(v_zs12_3851_, v___x_3891_, v___x_3848_, v___x_3849_, v___x_3849_, v___x_3850_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3894_; uint8_t v___x_3895_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc(v_a_3893_);
lean_dec_ref_known(v___x_3892_, 1);
v___x_3894_ = lean_array_get_size(v_zs12_3851_);
v___x_3895_ = lean_nat_dec_eq(v___x_3894_, v___x_3842_);
if (v___x_3895_ == 0)
{
v_e_3870_ = v_a_3893_;
goto v___jp_3869_;
}
else
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3897_ = l_Lean_mkArrow(v___x_3896_, v_a_3893_, v___y_3857_, v___y_3858_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v_e_3870_ = v_a_3898_;
goto v___jp_3869_;
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3906_; 
lean_dec(v___x_3844_);
lean_dec(v_v_3843_);
lean_dec(v___x_3842_);
v_a_3899_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3906_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3901_ = v___x_3897_;
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3897_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3906_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3904_; 
if (v_isShared_3902_ == 0)
{
v___x_3904_ = v___x_3901_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
v___x_3904_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
return v___x_3904_;
}
}
}
}
}
else
{
lean_object* v_a_3907_; lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3914_; 
lean_dec(v___x_3844_);
lean_dec(v_v_3843_);
lean_dec(v___x_3842_);
v_a_3907_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3909_ = v___x_3892_;
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
else
{
lean_inc(v_a_3907_);
lean_dec(v___x_3892_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3914_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3912_; 
if (v_isShared_3910_ == 0)
{
v___x_3912_ = v___x_3909_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3907_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v___x_3881_);
lean_dec_ref(v___x_3880_);
lean_dec_ref(v_is_3852_);
lean_dec_ref(v_motive_3847_);
lean_dec(v___x_3844_);
lean_dec(v_v_3843_);
lean_dec(v___x_3842_);
v_a_3915_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3883_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3883_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
v___jp_3860_:
{
lean_object* v___x_3863_; uint8_t v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3863_ = lean_array_get_size(v_zs12_3851_);
v___x_3864_ = lean_nat_dec_eq(v___x_3863_, v___x_3842_);
v___x_3865_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3865_, 0, v___x_3863_);
lean_ctor_set(v___x_3865_, 1, v___x_3842_);
lean_ctor_set_uint8(v___x_3865_, sizeof(void*)*2, v___x_3864_);
v___x_3866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3866_, 0, v___y_3862_);
lean_ctor_set(v___x_3866_, 1, v___y_3861_);
v___x_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3867_, 0, v___x_3866_);
lean_ctor_set(v___x_3867_, 1, v___x_3865_);
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
return v___x_3868_;
}
v___jp_3869_:
{
if (lean_obj_tag(v_v_3843_) == 1)
{
lean_object* v_str_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; 
lean_dec(v___x_3844_);
v_str_3871_ = lean_ctor_get(v_v_3843_, 1);
lean_inc_ref(v_str_3871_);
lean_dec_ref_known(v_v_3843_, 2);
v___x_3872_ = lean_box(0);
v___x_3873_ = l_Lean_Name_str___override(v___x_3872_, v_str_3871_);
v___y_3861_ = v_e_3870_;
v___y_3862_ = v___x_3873_;
goto v___jp_3860_;
}
else
{
lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_dec(v_v_3843_);
v___x_3874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3875_ = lean_nat_add(v___x_3844_, v___x_3845_);
lean_dec(v___x_3844_);
v___x_3876_ = l_Nat_reprFast(v___x_3875_);
v___x_3877_ = lean_string_append(v___x_3874_, v___x_3876_);
lean_dec_ref(v___x_3876_);
v___x_3878_ = lean_box(0);
v___x_3879_ = l_Lean_Name_str___override(v___x_3878_, v___x_3877_);
v___y_3861_ = v_e_3870_;
v___y_3862_ = v___x_3879_;
goto v___jp_3860_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3923_ = _args[0];
lean_object* v_v_3924_ = _args[1];
lean_object* v___x_3925_ = _args[2];
lean_object* v___x_3926_ = _args[3];
lean_object* v___x_3927_ = _args[4];
lean_object* v_motive_3928_ = _args[5];
lean_object* v___x_3929_ = _args[6];
lean_object* v___x_3930_ = _args[7];
lean_object* v___x_3931_ = _args[8];
lean_object* v_zs12_3932_ = _args[9];
lean_object* v_is_3933_ = _args[10];
lean_object* v_fields1_3934_ = _args[11];
lean_object* v_fields2_3935_ = _args[12];
lean_object* v___y_3936_ = _args[13];
lean_object* v___y_3937_ = _args[14];
lean_object* v___y_3938_ = _args[15];
lean_object* v___y_3939_ = _args[16];
lean_object* v___y_3940_ = _args[17];
_start:
{
uint8_t v___x_16323__boxed_3941_; uint8_t v___x_16324__boxed_3942_; uint8_t v___x_16325__boxed_3943_; lean_object* v_res_3944_; 
v___x_16323__boxed_3941_ = lean_unbox(v___x_3929_);
v___x_16324__boxed_3942_ = lean_unbox(v___x_3930_);
v___x_16325__boxed_3943_ = lean_unbox(v___x_3931_);
v_res_3944_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3923_, v_v_3924_, v___x_3925_, v___x_3926_, v___x_3927_, v_motive_3928_, v___x_16323__boxed_3941_, v___x_16324__boxed_3942_, v___x_16325__boxed_3943_, v_zs12_3932_, v_is_3933_, v_fields1_3934_, v_fields2_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec_ref(v_fields2_3935_);
lean_dec_ref(v_fields1_3934_);
lean_dec_ref(v_zs12_3932_);
lean_dec(v___x_3926_);
return v_res_3944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3945_, lean_object* v_params_3946_, lean_object* v_motive_3947_, size_t v_sz_3948_, size_t v_i_3949_, lean_object* v_bs_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
uint8_t v___x_3956_; 
v___x_3956_ = lean_usize_dec_lt(v_i_3949_, v_sz_3948_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; 
lean_dec_ref(v_motive_3947_);
lean_dec(v_tail_3945_);
v___x_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3957_, 0, v_bs_3950_);
return v___x_3957_;
}
else
{
lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; uint8_t v___x_3961_; lean_object* v_v_3962_; lean_object* v_bs_x27_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___f_3970_; lean_object* v___x_3971_; 
v___x_3958_ = lean_unsigned_to_nat(0u);
v___x_3959_ = lean_unsigned_to_nat(1u);
v___x_3960_ = 0;
v___x_3961_ = 1;
v_v_3962_ = lean_array_uget(v_bs_3950_, v_i_3949_);
v_bs_x27_3963_ = lean_array_uset(v_bs_3950_, v_i_3949_, v___x_3958_);
v___x_3964_ = lean_usize_to_nat(v_i_3949_);
lean_inc(v_tail_3945_);
lean_inc(v_v_3962_);
v___x_3965_ = l_Lean_mkConst(v_v_3962_, v_tail_3945_);
v___x_3966_ = l_Lean_mkAppN(v___x_3965_, v_params_3946_);
v___x_3967_ = lean_box(v___x_3960_);
v___x_3968_ = lean_box(v___x_3956_);
v___x_3969_ = lean_box(v___x_3961_);
lean_inc_ref(v_motive_3947_);
lean_inc_ref(v___x_3966_);
v___f_3970_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_3970_, 0, v___x_3958_);
lean_closure_set(v___f_3970_, 1, v_v_3962_);
lean_closure_set(v___f_3970_, 2, v___x_3964_);
lean_closure_set(v___f_3970_, 3, v___x_3959_);
lean_closure_set(v___f_3970_, 4, v___x_3966_);
lean_closure_set(v___f_3970_, 5, v_motive_3947_);
lean_closure_set(v___f_3970_, 6, v___x_3967_);
lean_closure_set(v___f_3970_, 7, v___x_3968_);
lean_closure_set(v___f_3970_, 8, v___x_3969_);
v___x_3971_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3966_, v___f_3970_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; size_t v___x_3973_; size_t v___x_3974_; lean_object* v___x_3975_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
lean_inc(v_a_3972_);
lean_dec_ref_known(v___x_3971_, 1);
v___x_3973_ = ((size_t)1ULL);
v___x_3974_ = lean_usize_add(v_i_3949_, v___x_3973_);
v___x_3975_ = lean_array_uset(v_bs_x27_3963_, v_i_3949_, v_a_3972_);
v_i_3949_ = v___x_3974_;
v_bs_3950_ = v___x_3975_;
goto _start;
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec_ref(v_bs_x27_3963_);
lean_dec_ref(v_motive_3947_);
lean_dec(v_tail_3945_);
v_a_3977_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3971_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3971_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_3985_, lean_object* v_params_3986_, lean_object* v_motive_3987_, lean_object* v_sz_3988_, lean_object* v_i_3989_, lean_object* v_bs_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
size_t v_sz_boxed_3996_; size_t v_i_boxed_3997_; lean_object* v_res_3998_; 
v_sz_boxed_3996_ = lean_unbox_usize(v_sz_3988_);
lean_dec(v_sz_3988_);
v_i_boxed_3997_ = lean_unbox_usize(v_i_3989_);
lean_dec(v_i_3989_);
v_res_3998_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_3985_, v_params_3986_, v_motive_3987_, v_sz_boxed_3996_, v_i_boxed_3997_, v_bs_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3993_);
lean_dec(v___y_3992_);
lean_dec_ref(v___y_3991_);
lean_dec_ref(v_params_3986_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_4001_, lean_object* v_tail_4002_, lean_object* v_params_4003_, lean_object* v_numIndices_4004_, lean_object* v___x_4005_, lean_object* v___x_4006_, uint8_t v___x_4007_, uint8_t v___x_4008_, uint8_t v___x_4009_, lean_object* v_is_4010_, lean_object* v___x_4011_, lean_object* v___x_4012_, lean_object* v___x_4013_, lean_object* v___x_4014_, lean_object* v___x_4015_, lean_object* v___x_4016_, lean_object* v_heq_4017_, lean_object* v_val_4018_, lean_object* v___x_4019_, lean_object* v_declName_4020_, lean_object* v_levelParams_4021_, lean_object* v___x_4022_, lean_object* v___x_4023_, lean_object* v_numParams_4024_, lean_object* v___x_4025_, lean_object* v_motive_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; size_t v_sz_4033_; size_t v___x_4034_; lean_object* v___x_4035_; 
v___x_4032_ = lean_array_mk(v_ctors_4001_);
v_sz_4033_ = lean_array_size(v___x_4032_);
v___x_4034_ = ((size_t)0ULL);
lean_inc_ref(v___x_4032_);
lean_inc_ref(v_motive_4026_);
lean_inc(v_tail_4002_);
v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4002_, v_params_4003_, v_motive_4026_, v_sz_4033_, v___x_4034_, v___x_4032_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4037_; lean_object* v_fst_4038_; lean_object* v_snd_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___f_4045_; uint8_t v___x_4046_; lean_object* v___x_4047_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref_known(v___x_4035_, 1);
v___x_4037_ = l_Array_unzip___redArg(v_a_4036_);
lean_dec(v_a_4036_);
v_fst_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_fst_4038_);
v_snd_4039_ = lean_ctor_get(v___x_4037_, 1);
lean_inc(v_snd_4039_);
lean_dec_ref(v___x_4037_);
v___x_4040_ = lean_box(v___x_4007_);
v___x_4041_ = lean_box(v___x_4008_);
v___x_4042_ = lean_box(v___x_4009_);
v___x_4043_ = lean_box_usize(v_sz_4033_);
v___x_4044_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4045_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4045_, 0, v_numIndices_4004_);
lean_closure_set(v___f_4045_, 1, v___x_4005_);
lean_closure_set(v___f_4045_, 2, v_motive_4026_);
lean_closure_set(v___f_4045_, 3, v___x_4006_);
lean_closure_set(v___f_4045_, 4, v___x_4040_);
lean_closure_set(v___f_4045_, 5, v___x_4041_);
lean_closure_set(v___f_4045_, 6, v___x_4042_);
lean_closure_set(v___f_4045_, 7, v_is_4010_);
lean_closure_set(v___f_4045_, 8, v___x_4011_);
lean_closure_set(v___f_4045_, 9, v___x_4012_);
lean_closure_set(v___f_4045_, 10, v___x_4013_);
lean_closure_set(v___f_4045_, 11, v___x_4014_);
lean_closure_set(v___f_4045_, 12, v_params_4003_);
lean_closure_set(v___f_4045_, 13, v___x_4015_);
lean_closure_set(v___f_4045_, 14, v___x_4016_);
lean_closure_set(v___f_4045_, 15, v_heq_4017_);
lean_closure_set(v___f_4045_, 16, v_val_4018_);
lean_closure_set(v___f_4045_, 17, v_tail_4002_);
lean_closure_set(v___f_4045_, 18, v___x_4043_);
lean_closure_set(v___f_4045_, 19, v___x_4044_);
lean_closure_set(v___f_4045_, 20, v___x_4032_);
lean_closure_set(v___f_4045_, 21, v___x_4019_);
lean_closure_set(v___f_4045_, 22, v_declName_4020_);
lean_closure_set(v___f_4045_, 23, v_levelParams_4021_);
lean_closure_set(v___f_4045_, 24, v___x_4022_);
lean_closure_set(v___f_4045_, 25, v___x_4023_);
lean_closure_set(v___f_4045_, 26, v_numParams_4024_);
lean_closure_set(v___f_4045_, 27, v_snd_4039_);
lean_closure_set(v___f_4045_, 28, v___x_4025_);
v___x_4046_ = 0;
v___x_4047_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_4038_, v___f_4045_, v___x_4046_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
return v___x_4047_;
}
else
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec_ref(v___x_4032_);
lean_dec_ref(v_motive_4026_);
lean_dec_ref(v___x_4025_);
lean_dec(v_numParams_4024_);
lean_dec(v___x_4023_);
lean_dec(v___x_4022_);
lean_dec(v_levelParams_4021_);
lean_dec(v_declName_4020_);
lean_dec_ref(v___x_4019_);
lean_dec_ref(v_val_4018_);
lean_dec_ref(v_heq_4017_);
lean_dec_ref(v___x_4016_);
lean_dec_ref(v___x_4015_);
lean_dec(v___x_4014_);
lean_dec(v___x_4013_);
lean_dec_ref(v___x_4012_);
lean_dec_ref(v___x_4011_);
lean_dec_ref(v_is_4010_);
lean_dec_ref(v___x_4006_);
lean_dec(v___x_4005_);
lean_dec(v_numIndices_4004_);
lean_dec_ref(v_params_4003_);
lean_dec(v_tail_4002_);
v_a_4048_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4035_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4035_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4056_ = _args[0];
lean_object* v_tail_4057_ = _args[1];
lean_object* v_params_4058_ = _args[2];
lean_object* v_numIndices_4059_ = _args[3];
lean_object* v___x_4060_ = _args[4];
lean_object* v___x_4061_ = _args[5];
lean_object* v___x_4062_ = _args[6];
lean_object* v___x_4063_ = _args[7];
lean_object* v___x_4064_ = _args[8];
lean_object* v_is_4065_ = _args[9];
lean_object* v___x_4066_ = _args[10];
lean_object* v___x_4067_ = _args[11];
lean_object* v___x_4068_ = _args[12];
lean_object* v___x_4069_ = _args[13];
lean_object* v___x_4070_ = _args[14];
lean_object* v___x_4071_ = _args[15];
lean_object* v_heq_4072_ = _args[16];
lean_object* v_val_4073_ = _args[17];
lean_object* v___x_4074_ = _args[18];
lean_object* v_declName_4075_ = _args[19];
lean_object* v_levelParams_4076_ = _args[20];
lean_object* v___x_4077_ = _args[21];
lean_object* v___x_4078_ = _args[22];
lean_object* v_numParams_4079_ = _args[23];
lean_object* v___x_4080_ = _args[24];
lean_object* v_motive_4081_ = _args[25];
lean_object* v___y_4082_ = _args[26];
lean_object* v___y_4083_ = _args[27];
lean_object* v___y_4084_ = _args[28];
lean_object* v___y_4085_ = _args[29];
lean_object* v___y_4086_ = _args[30];
_start:
{
uint8_t v___x_16560__boxed_4087_; uint8_t v___x_16561__boxed_4088_; uint8_t v___x_16562__boxed_4089_; lean_object* v_res_4090_; 
v___x_16560__boxed_4087_ = lean_unbox(v___x_4062_);
v___x_16561__boxed_4088_ = lean_unbox(v___x_4063_);
v___x_16562__boxed_4089_ = lean_unbox(v___x_4064_);
v_res_4090_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4056_, v_tail_4057_, v_params_4058_, v_numIndices_4059_, v___x_4060_, v___x_4061_, v___x_16560__boxed_4087_, v___x_16561__boxed_4088_, v___x_16562__boxed_4089_, v_is_4065_, v___x_4066_, v___x_4067_, v___x_4068_, v___x_4069_, v___x_4070_, v___x_4071_, v_heq_4072_, v_val_4073_, v___x_4074_, v_declName_4075_, v_levelParams_4076_, v___x_4077_, v___x_4078_, v_numParams_4079_, v___x_4080_, v_motive_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4091_, lean_object* v___x_4092_, lean_object* v_is_4093_, lean_object* v_head_4094_, lean_object* v_ctors_4095_, lean_object* v_tail_4096_, lean_object* v_params_4097_, lean_object* v_numIndices_4098_, lean_object* v___x_4099_, lean_object* v___x_4100_, lean_object* v___x_4101_, lean_object* v___x_4102_, lean_object* v___x_4103_, lean_object* v_val_4104_, lean_object* v___x_4105_, lean_object* v_declName_4106_, lean_object* v_levelParams_4107_, lean_object* v___x_4108_, lean_object* v_numParams_4109_, lean_object* v___x_4110_, lean_object* v_heq_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; uint8_t v___x_4124_; uint8_t v___x_4125_; uint8_t v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___f_4130_; lean_object* v___x_4131_; 
v___x_4117_ = lean_unsigned_to_nat(3u);
v___x_4118_ = lean_mk_empty_array_with_capacity(v___x_4117_);
lean_inc_ref(v___x_4091_);
v___x_4119_ = lean_array_push(v___x_4118_, v___x_4091_);
lean_inc_ref(v___x_4092_);
v___x_4120_ = lean_array_push(v___x_4119_, v___x_4092_);
lean_inc_ref(v_heq_4111_);
v___x_4121_ = lean_array_push(v___x_4120_, v_heq_4111_);
lean_inc_ref(v_is_4093_);
v___x_4122_ = l_Array_append___redArg(v_is_4093_, v___x_4121_);
lean_dec_ref(v___x_4121_);
v___x_4123_ = l_Lean_mkSort(v_head_4094_);
v___x_4124_ = 0;
v___x_4125_ = 1;
v___x_4126_ = 1;
v___x_4127_ = lean_box(v___x_4124_);
v___x_4128_ = lean_box(v___x_4125_);
v___x_4129_ = lean_box(v___x_4126_);
lean_inc_ref(v___x_4122_);
v___f_4130_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4130_, 0, v_ctors_4095_);
lean_closure_set(v___f_4130_, 1, v_tail_4096_);
lean_closure_set(v___f_4130_, 2, v_params_4097_);
lean_closure_set(v___f_4130_, 3, v_numIndices_4098_);
lean_closure_set(v___f_4130_, 4, v___x_4099_);
lean_closure_set(v___f_4130_, 5, v___x_4122_);
lean_closure_set(v___f_4130_, 6, v___x_4127_);
lean_closure_set(v___f_4130_, 7, v___x_4128_);
lean_closure_set(v___f_4130_, 8, v___x_4129_);
lean_closure_set(v___f_4130_, 9, v_is_4093_);
lean_closure_set(v___f_4130_, 10, v___x_4092_);
lean_closure_set(v___f_4130_, 11, v___x_4091_);
lean_closure_set(v___f_4130_, 12, v___x_4100_);
lean_closure_set(v___f_4130_, 13, v___x_4101_);
lean_closure_set(v___f_4130_, 14, v___x_4102_);
lean_closure_set(v___f_4130_, 15, v___x_4103_);
lean_closure_set(v___f_4130_, 16, v_heq_4111_);
lean_closure_set(v___f_4130_, 17, v_val_4104_);
lean_closure_set(v___f_4130_, 18, v___x_4105_);
lean_closure_set(v___f_4130_, 19, v_declName_4106_);
lean_closure_set(v___f_4130_, 20, v_levelParams_4107_);
lean_closure_set(v___f_4130_, 21, v___x_4117_);
lean_closure_set(v___f_4130_, 22, v___x_4108_);
lean_closure_set(v___f_4130_, 23, v_numParams_4109_);
lean_closure_set(v___f_4130_, 24, v___x_4110_);
v___x_4131_ = l_Lean_Meta_mkForallFVars(v___x_4122_, v___x_4123_, v___x_4124_, v___x_4125_, v___x_4125_, v___x_4126_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
lean_dec_ref(v___x_4122_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; lean_object* v___x_4135_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4131_, 1);
v___x_4133_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4134_ = 0;
v___x_4135_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4133_, v___x_4126_, v_a_4132_, v___f_4130_, v___x_4134_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
return v___x_4135_;
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
lean_dec_ref(v___f_4130_);
v_a_4136_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___x_4131_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___x_4131_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
return v___x_4141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4144_ = _args[0];
lean_object* v___x_4145_ = _args[1];
lean_object* v_is_4146_ = _args[2];
lean_object* v_head_4147_ = _args[3];
lean_object* v_ctors_4148_ = _args[4];
lean_object* v_tail_4149_ = _args[5];
lean_object* v_params_4150_ = _args[6];
lean_object* v_numIndices_4151_ = _args[7];
lean_object* v___x_4152_ = _args[8];
lean_object* v___x_4153_ = _args[9];
lean_object* v___x_4154_ = _args[10];
lean_object* v___x_4155_ = _args[11];
lean_object* v___x_4156_ = _args[12];
lean_object* v_val_4157_ = _args[13];
lean_object* v___x_4158_ = _args[14];
lean_object* v_declName_4159_ = _args[15];
lean_object* v_levelParams_4160_ = _args[16];
lean_object* v___x_4161_ = _args[17];
lean_object* v_numParams_4162_ = _args[18];
lean_object* v___x_4163_ = _args[19];
lean_object* v_heq_4164_ = _args[20];
lean_object* v___y_4165_ = _args[21];
lean_object* v___y_4166_ = _args[22];
lean_object* v___y_4167_ = _args[23];
lean_object* v___y_4168_ = _args[24];
lean_object* v___y_4169_ = _args[25];
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4144_, v___x_4145_, v_is_4146_, v_head_4147_, v_ctors_4148_, v_tail_4149_, v_params_4150_, v_numIndices_4151_, v___x_4152_, v___x_4153_, v___x_4154_, v___x_4155_, v___x_4156_, v_val_4157_, v___x_4158_, v_declName_4159_, v_levelParams_4160_, v___x_4161_, v_numParams_4162_, v___x_4163_, v_heq_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4171_, lean_object* v_x1_4172_, lean_object* v_indName_4173_, lean_object* v_tail_4174_, lean_object* v_params_4175_, lean_object* v_is_4176_, lean_object* v___x_4177_, lean_object* v_head_4178_, lean_object* v_ctors_4179_, lean_object* v_numIndices_4180_, lean_object* v___x_4181_, lean_object* v___x_4182_, lean_object* v_val_4183_, lean_object* v_declName_4184_, lean_object* v_levelParams_4185_, lean_object* v_numParams_4186_, lean_object* v___x_4187_, lean_object* v_x2_4188_, lean_object* v_x_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___f_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4195_ = lean_unsigned_to_nat(0u);
v___x_4196_ = lean_array_get_borrowed(v___x_4171_, v_x1_4172_, v___x_4195_);
v___x_4197_ = lean_array_get_borrowed(v___x_4171_, v_x2_4188_, v___x_4195_);
v___x_4198_ = l_Lean_mkCtorIdxName(v_indName_4173_);
lean_inc(v_tail_4174_);
v___x_4199_ = l_Lean_mkConst(v___x_4198_, v_tail_4174_);
lean_inc_ref(v_params_4175_);
v___x_4200_ = l_Array_append___redArg(v_params_4175_, v_is_4176_);
v___x_4201_ = lean_mk_empty_array_with_capacity(v___x_4177_);
lean_inc_n(v___x_4196_, 2);
lean_inc_ref_n(v___x_4201_, 2);
v___x_4202_ = lean_array_push(v___x_4201_, v___x_4196_);
lean_inc_ref(v___x_4200_);
v___x_4203_ = l_Array_append___redArg(v___x_4200_, v___x_4202_);
lean_inc_ref(v___x_4199_);
v___x_4204_ = l_Lean_mkAppN(v___x_4199_, v___x_4203_);
lean_dec_ref(v___x_4203_);
lean_inc_n(v___x_4197_, 2);
v___x_4205_ = lean_array_push(v___x_4201_, v___x_4197_);
lean_inc_ref(v___x_4205_);
v___f_4206_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4206_, 0, v___x_4196_);
lean_closure_set(v___f_4206_, 1, v___x_4197_);
lean_closure_set(v___f_4206_, 2, v_is_4176_);
lean_closure_set(v___f_4206_, 3, v_head_4178_);
lean_closure_set(v___f_4206_, 4, v_ctors_4179_);
lean_closure_set(v___f_4206_, 5, v_tail_4174_);
lean_closure_set(v___f_4206_, 6, v_params_4175_);
lean_closure_set(v___f_4206_, 7, v_numIndices_4180_);
lean_closure_set(v___f_4206_, 8, v___x_4177_);
lean_closure_set(v___f_4206_, 9, v___x_4181_);
lean_closure_set(v___f_4206_, 10, v___x_4182_);
lean_closure_set(v___f_4206_, 11, v___x_4202_);
lean_closure_set(v___f_4206_, 12, v___x_4205_);
lean_closure_set(v___f_4206_, 13, v_val_4183_);
lean_closure_set(v___f_4206_, 14, v___x_4201_);
lean_closure_set(v___f_4206_, 15, v_declName_4184_);
lean_closure_set(v___f_4206_, 16, v_levelParams_4185_);
lean_closure_set(v___f_4206_, 17, v___x_4195_);
lean_closure_set(v___f_4206_, 18, v_numParams_4186_);
lean_closure_set(v___f_4206_, 19, v___x_4187_);
v___x_4207_ = l_Array_append___redArg(v___x_4200_, v___x_4205_);
lean_dec_ref(v___x_4205_);
v___x_4208_ = l_Lean_mkAppN(v___x_4199_, v___x_4207_);
lean_dec_ref(v___x_4207_);
v___x_4209_ = l_Lean_Meta_mkEq(v___x_4204_, v___x_4208_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v___x_4209_, 1);
v___x_4211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4212_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4211_, v_a_4210_, v___f_4206_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
return v___x_4212_;
}
else
{
lean_object* v_a_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4220_; 
lean_dec_ref(v___f_4206_);
v_a_4213_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4220_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4220_ == 0)
{
v___x_4215_ = v___x_4209_;
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_a_4213_);
lean_dec(v___x_4209_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4220_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4218_; 
if (v_isShared_4216_ == 0)
{
v___x_4218_ = v___x_4215_;
goto v_reusejp_4217_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
v___x_4218_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4217_;
}
v_reusejp_4217_:
{
return v___x_4218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4221_ = _args[0];
lean_object* v_x1_4222_ = _args[1];
lean_object* v_indName_4223_ = _args[2];
lean_object* v_tail_4224_ = _args[3];
lean_object* v_params_4225_ = _args[4];
lean_object* v_is_4226_ = _args[5];
lean_object* v___x_4227_ = _args[6];
lean_object* v_head_4228_ = _args[7];
lean_object* v_ctors_4229_ = _args[8];
lean_object* v_numIndices_4230_ = _args[9];
lean_object* v___x_4231_ = _args[10];
lean_object* v___x_4232_ = _args[11];
lean_object* v_val_4233_ = _args[12];
lean_object* v_declName_4234_ = _args[13];
lean_object* v_levelParams_4235_ = _args[14];
lean_object* v_numParams_4236_ = _args[15];
lean_object* v___x_4237_ = _args[16];
lean_object* v_x2_4238_ = _args[17];
lean_object* v_x_4239_ = _args[18];
lean_object* v___y_4240_ = _args[19];
lean_object* v___y_4241_ = _args[20];
lean_object* v___y_4242_ = _args[21];
lean_object* v___y_4243_ = _args[22];
lean_object* v___y_4244_ = _args[23];
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4221_, v_x1_4222_, v_indName_4223_, v_tail_4224_, v_params_4225_, v_is_4226_, v___x_4227_, v_head_4228_, v_ctors_4229_, v_numIndices_4230_, v___x_4231_, v___x_4232_, v_val_4233_, v_declName_4234_, v_levelParams_4235_, v_numParams_4236_, v___x_4237_, v_x2_4238_, v_x_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec_ref(v_x_4239_);
lean_dec_ref(v_x2_4238_);
lean_dec_ref(v_x1_4222_);
lean_dec_ref(v___x_4221_);
return v_res_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4246_, lean_object* v_indName_4247_, lean_object* v_tail_4248_, lean_object* v_params_4249_, lean_object* v_is_4250_, lean_object* v___x_4251_, lean_object* v_head_4252_, lean_object* v_ctors_4253_, lean_object* v_numIndices_4254_, lean_object* v___x_4255_, lean_object* v___x_4256_, lean_object* v_val_4257_, lean_object* v_declName_4258_, lean_object* v_levelParams_4259_, lean_object* v_numParams_4260_, lean_object* v___x_4261_, lean_object* v_t_4262_, lean_object* v___x_4263_, lean_object* v_x1_4264_, lean_object* v_x_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___f_4271_; uint8_t v___x_4272_; lean_object* v___x_4273_; 
v___f_4271_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4271_, 0, v___x_4246_);
lean_closure_set(v___f_4271_, 1, v_x1_4264_);
lean_closure_set(v___f_4271_, 2, v_indName_4247_);
lean_closure_set(v___f_4271_, 3, v_tail_4248_);
lean_closure_set(v___f_4271_, 4, v_params_4249_);
lean_closure_set(v___f_4271_, 5, v_is_4250_);
lean_closure_set(v___f_4271_, 6, v___x_4251_);
lean_closure_set(v___f_4271_, 7, v_head_4252_);
lean_closure_set(v___f_4271_, 8, v_ctors_4253_);
lean_closure_set(v___f_4271_, 9, v_numIndices_4254_);
lean_closure_set(v___f_4271_, 10, v___x_4255_);
lean_closure_set(v___f_4271_, 11, v___x_4256_);
lean_closure_set(v___f_4271_, 12, v_val_4257_);
lean_closure_set(v___f_4271_, 13, v_declName_4258_);
lean_closure_set(v___f_4271_, 14, v_levelParams_4259_);
lean_closure_set(v___f_4271_, 15, v_numParams_4260_);
lean_closure_set(v___f_4271_, 16, v___x_4261_);
v___x_4272_ = 0;
v___x_4273_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4262_, v___x_4263_, v___f_4271_, v___x_4272_, v___x_4272_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4274_ = _args[0];
lean_object* v_indName_4275_ = _args[1];
lean_object* v_tail_4276_ = _args[2];
lean_object* v_params_4277_ = _args[3];
lean_object* v_is_4278_ = _args[4];
lean_object* v___x_4279_ = _args[5];
lean_object* v_head_4280_ = _args[6];
lean_object* v_ctors_4281_ = _args[7];
lean_object* v_numIndices_4282_ = _args[8];
lean_object* v___x_4283_ = _args[9];
lean_object* v___x_4284_ = _args[10];
lean_object* v_val_4285_ = _args[11];
lean_object* v_declName_4286_ = _args[12];
lean_object* v_levelParams_4287_ = _args[13];
lean_object* v_numParams_4288_ = _args[14];
lean_object* v___x_4289_ = _args[15];
lean_object* v_t_4290_ = _args[16];
lean_object* v___x_4291_ = _args[17];
lean_object* v_x1_4292_ = _args[18];
lean_object* v_x_4293_ = _args[19];
lean_object* v___y_4294_ = _args[20];
lean_object* v___y_4295_ = _args[21];
lean_object* v___y_4296_ = _args[22];
lean_object* v___y_4297_ = _args[23];
lean_object* v___y_4298_ = _args[24];
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4274_, v_indName_4275_, v_tail_4276_, v_params_4277_, v_is_4278_, v___x_4279_, v_head_4280_, v_ctors_4281_, v_numIndices_4282_, v___x_4283_, v___x_4284_, v_val_4285_, v_declName_4286_, v_levelParams_4287_, v_numParams_4288_, v___x_4289_, v_t_4290_, v___x_4291_, v_x1_4292_, v_x_4293_, v___y_4294_, v___y_4295_, v___y_4296_, v___y_4297_);
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4296_);
lean_dec(v___y_4295_);
lean_dec_ref(v___y_4294_);
lean_dec_ref(v_x_4293_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4300_, lean_object* v_indName_4301_, lean_object* v_tail_4302_, lean_object* v_params_4303_, lean_object* v_head_4304_, lean_object* v_ctors_4305_, lean_object* v_numIndices_4306_, lean_object* v___x_4307_, lean_object* v___x_4308_, lean_object* v_val_4309_, lean_object* v_declName_4310_, lean_object* v_levelParams_4311_, lean_object* v_numParams_4312_, lean_object* v___x_4313_, lean_object* v_is_4314_, lean_object* v_t_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___f_4323_; uint8_t v___x_4324_; lean_object* v___x_4325_; 
v___x_4321_ = lean_unsigned_to_nat(1u);
v___x_4322_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4315_);
v___f_4323_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4323_, 0, v___x_4300_);
lean_closure_set(v___f_4323_, 1, v_indName_4301_);
lean_closure_set(v___f_4323_, 2, v_tail_4302_);
lean_closure_set(v___f_4323_, 3, v_params_4303_);
lean_closure_set(v___f_4323_, 4, v_is_4314_);
lean_closure_set(v___f_4323_, 5, v___x_4321_);
lean_closure_set(v___f_4323_, 6, v_head_4304_);
lean_closure_set(v___f_4323_, 7, v_ctors_4305_);
lean_closure_set(v___f_4323_, 8, v_numIndices_4306_);
lean_closure_set(v___f_4323_, 9, v___x_4307_);
lean_closure_set(v___f_4323_, 10, v___x_4308_);
lean_closure_set(v___f_4323_, 11, v_val_4309_);
lean_closure_set(v___f_4323_, 12, v_declName_4310_);
lean_closure_set(v___f_4323_, 13, v_levelParams_4311_);
lean_closure_set(v___f_4323_, 14, v_numParams_4312_);
lean_closure_set(v___f_4323_, 15, v___x_4313_);
lean_closure_set(v___f_4323_, 16, v_t_4315_);
lean_closure_set(v___f_4323_, 17, v___x_4322_);
v___x_4324_ = 0;
v___x_4325_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4315_, v___x_4322_, v___f_4323_, v___x_4324_, v___x_4324_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4326_ = _args[0];
lean_object* v_indName_4327_ = _args[1];
lean_object* v_tail_4328_ = _args[2];
lean_object* v_params_4329_ = _args[3];
lean_object* v_head_4330_ = _args[4];
lean_object* v_ctors_4331_ = _args[5];
lean_object* v_numIndices_4332_ = _args[6];
lean_object* v___x_4333_ = _args[7];
lean_object* v___x_4334_ = _args[8];
lean_object* v_val_4335_ = _args[9];
lean_object* v_declName_4336_ = _args[10];
lean_object* v_levelParams_4337_ = _args[11];
lean_object* v_numParams_4338_ = _args[12];
lean_object* v___x_4339_ = _args[13];
lean_object* v_is_4340_ = _args[14];
lean_object* v_t_4341_ = _args[15];
lean_object* v___y_4342_ = _args[16];
lean_object* v___y_4343_ = _args[17];
lean_object* v___y_4344_ = _args[18];
lean_object* v___y_4345_ = _args[19];
lean_object* v___y_4346_ = _args[20];
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4326_, v_indName_4327_, v_tail_4328_, v_params_4329_, v_head_4330_, v_ctors_4331_, v_numIndices_4332_, v___x_4333_, v___x_4334_, v_val_4335_, v_declName_4336_, v_levelParams_4337_, v_numParams_4338_, v___x_4339_, v_is_4340_, v_t_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4348_, lean_object* v_indName_4349_, lean_object* v_tail_4350_, lean_object* v_head_4351_, lean_object* v_ctors_4352_, lean_object* v_numIndices_4353_, lean_object* v___x_4354_, lean_object* v___x_4355_, lean_object* v_val_4356_, lean_object* v_declName_4357_, lean_object* v_levelParams_4358_, lean_object* v_numParams_4359_, lean_object* v_params_4360_, lean_object* v_t_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v___x_4367_; lean_object* v___f_4368_; lean_object* v___x_4369_; uint8_t v___x_4370_; lean_object* v___x_4371_; 
v___x_4367_ = l_Lean_Expr_bindingBody_x21(v_t_4361_);
lean_inc_ref(v___x_4367_);
lean_inc(v_numIndices_4353_);
v___f_4368_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4368_, 0, v___x_4348_);
lean_closure_set(v___f_4368_, 1, v_indName_4349_);
lean_closure_set(v___f_4368_, 2, v_tail_4350_);
lean_closure_set(v___f_4368_, 3, v_params_4360_);
lean_closure_set(v___f_4368_, 4, v_head_4351_);
lean_closure_set(v___f_4368_, 5, v_ctors_4352_);
lean_closure_set(v___f_4368_, 6, v_numIndices_4353_);
lean_closure_set(v___f_4368_, 7, v___x_4354_);
lean_closure_set(v___f_4368_, 8, v___x_4355_);
lean_closure_set(v___f_4368_, 9, v_val_4356_);
lean_closure_set(v___f_4368_, 10, v_declName_4357_);
lean_closure_set(v___f_4368_, 11, v_levelParams_4358_);
lean_closure_set(v___f_4368_, 12, v_numParams_4359_);
lean_closure_set(v___f_4368_, 13, v___x_4367_);
v___x_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4369_, 0, v_numIndices_4353_);
v___x_4370_ = 0;
v___x_4371_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4367_, v___x_4369_, v___f_4368_, v___x_4370_, v___x_4370_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
return v___x_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4372_ = _args[0];
lean_object* v_indName_4373_ = _args[1];
lean_object* v_tail_4374_ = _args[2];
lean_object* v_head_4375_ = _args[3];
lean_object* v_ctors_4376_ = _args[4];
lean_object* v_numIndices_4377_ = _args[5];
lean_object* v___x_4378_ = _args[6];
lean_object* v___x_4379_ = _args[7];
lean_object* v_val_4380_ = _args[8];
lean_object* v_declName_4381_ = _args[9];
lean_object* v_levelParams_4382_ = _args[10];
lean_object* v_numParams_4383_ = _args[11];
lean_object* v_params_4384_ = _args[12];
lean_object* v_t_4385_ = _args[13];
lean_object* v___y_4386_ = _args[14];
lean_object* v___y_4387_ = _args[15];
lean_object* v___y_4388_ = _args[16];
lean_object* v___y_4389_ = _args[17];
lean_object* v___y_4390_ = _args[18];
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4372_, v_indName_4373_, v_tail_4374_, v_head_4375_, v_ctors_4376_, v_numIndices_4377_, v___x_4378_, v___x_4379_, v_val_4380_, v_declName_4381_, v_levelParams_4382_, v_numParams_4383_, v_params_4384_, v_t_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec_ref(v_t_4385_);
return v_res_4391_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4396_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4397_ = lean_unsigned_to_nat(58u);
v___x_4398_ = lean_unsigned_to_nat(142u);
v___x_4399_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4400_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4401_ = l_mkPanicMessageWithDecl(v___x_4400_, v___x_4399_, v___x_4398_, v___x_4397_, v___x_4396_);
return v___x_4401_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4402_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4403_ = lean_unsigned_to_nat(60u);
v___x_4404_ = lean_unsigned_to_nat(136u);
v___x_4405_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4406_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4407_ = l_mkPanicMessageWithDecl(v___x_4406_, v___x_4405_, v___x_4404_, v___x_4403_, v___x_4402_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4408_, lean_object* v_indName_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v___x_4415_; lean_object* v___x_4416_; 
v___x_4415_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_4409_);
v___x_4416_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v_a_4417_; 
v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
lean_inc(v_a_4417_);
lean_dec_ref_known(v___x_4416_, 1);
if (lean_obj_tag(v_a_4417_) == 5)
{
lean_object* v_val_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v_val_4418_ = lean_ctor_get(v_a_4417_, 0);
lean_inc_ref(v_val_4418_);
lean_dec_ref_known(v_a_4417_, 1);
v___x_4419_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4408_);
v___x_4420_ = l_Lean_Name_append(v_declName_4408_, v___x_4419_);
lean_inc(v_indName_4409_);
lean_inc(v___x_4420_);
v___x_4421_ = l_Lean_mkCasesOnSameCtorHet(v___x_4420_, v_indName_4409_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4453_; 
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4421_);
if (v_isSharedCheck_4453_ == 0)
{
lean_object* v_unused_4454_; 
v_unused_4454_ = lean_ctor_get(v___x_4421_, 0);
lean_dec(v_unused_4454_);
v___x_4423_ = v___x_4421_;
v_isShared_4424_ = v_isSharedCheck_4453_;
goto v_resetjp_4422_;
}
else
{
lean_dec(v___x_4421_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4453_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
lean_inc(v_indName_4409_);
v___x_4425_ = l_Lean_mkCasesOnName(v_indName_4409_);
v___x_4426_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4425_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v_levelParams_4428_; lean_object* v_type_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
lean_dec_ref_known(v___x_4426_, 1);
v_levelParams_4428_ = lean_ctor_get(v_a_4427_, 1);
lean_inc_n(v_levelParams_4428_, 2);
v_type_4429_ = lean_ctor_get(v_a_4427_, 2);
lean_inc_ref(v_type_4429_);
lean_dec(v_a_4427_);
v___x_4430_ = lean_box(0);
v___x_4431_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4428_, v___x_4430_);
if (lean_obj_tag(v___x_4431_) == 1)
{
lean_object* v_head_4432_; lean_object* v_tail_4433_; lean_object* v_numParams_4434_; lean_object* v_numIndices_4435_; lean_object* v_ctors_4436_; lean_object* v___f_4437_; lean_object* v___x_4439_; 
v_head_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_head_4432_);
v_tail_4433_ = lean_ctor_get(v___x_4431_, 1);
lean_inc(v_tail_4433_);
v_numParams_4434_ = lean_ctor_get(v_val_4418_, 1);
lean_inc_n(v_numParams_4434_, 2);
v_numIndices_4435_ = lean_ctor_get(v_val_4418_, 2);
lean_inc(v_numIndices_4435_);
v_ctors_4436_ = lean_ctor_get(v_val_4418_, 4);
lean_inc(v_ctors_4436_);
v___f_4437_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4437_, 0, v___x_4415_);
lean_closure_set(v___f_4437_, 1, v_indName_4409_);
lean_closure_set(v___f_4437_, 2, v_tail_4433_);
lean_closure_set(v___f_4437_, 3, v_head_4432_);
lean_closure_set(v___f_4437_, 4, v_ctors_4436_);
lean_closure_set(v___f_4437_, 5, v_numIndices_4435_);
lean_closure_set(v___f_4437_, 6, v___x_4420_);
lean_closure_set(v___f_4437_, 7, v___x_4431_);
lean_closure_set(v___f_4437_, 8, v_val_4418_);
lean_closure_set(v___f_4437_, 9, v_declName_4408_);
lean_closure_set(v___f_4437_, 10, v_levelParams_4428_);
lean_closure_set(v___f_4437_, 11, v_numParams_4434_);
if (v_isShared_4424_ == 0)
{
lean_ctor_set_tag(v___x_4423_, 1);
lean_ctor_set(v___x_4423_, 0, v_numParams_4434_);
v___x_4439_ = v___x_4423_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_numParams_4434_);
v___x_4439_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
uint8_t v___x_4440_; lean_object* v___x_4441_; 
v___x_4440_ = 0;
v___x_4441_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4429_, v___x_4439_, v___f_4437_, v___x_4440_, v___x_4440_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
return v___x_4441_;
}
}
else
{
lean_object* v___x_4443_; lean_object* v___x_4444_; 
lean_dec(v___x_4431_);
lean_dec_ref(v_type_4429_);
lean_dec(v_levelParams_4428_);
lean_del_object(v___x_4423_);
lean_dec(v___x_4420_);
lean_dec_ref(v_val_4418_);
lean_dec(v_indName_4409_);
lean_dec(v_declName_4408_);
v___x_4443_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4444_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_4443_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
return v___x_4444_;
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_del_object(v___x_4423_);
lean_dec(v___x_4420_);
lean_dec_ref(v_val_4418_);
lean_dec(v_indName_4409_);
lean_dec(v_declName_4408_);
v_a_4445_ = lean_ctor_get(v___x_4426_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4426_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4426_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4426_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
}
}
else
{
lean_dec(v___x_4420_);
lean_dec_ref(v_val_4418_);
lean_dec(v_indName_4409_);
lean_dec(v_declName_4408_);
return v___x_4421_;
}
}
else
{
lean_object* v___x_4455_; lean_object* v___x_4456_; 
lean_dec(v_a_4417_);
lean_dec(v_indName_4409_);
lean_dec(v_declName_4408_);
v___x_4455_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4456_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_4455_, v_a_4410_, v_a_4411_, v_a_4412_, v_a_4413_);
return v___x_4456_;
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_dec(v_indName_4409_);
lean_dec(v_declName_4408_);
v_a_4457_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4416_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4416_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4465_, lean_object* v_indName_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Lean_mkCasesOnSameCtor(v_declName_4465_, v_indName_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
lean_dec(v_a_4470_);
lean_dec_ref(v_a_4469_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4473_, lean_object* v_params_4474_, lean_object* v_motive_4475_, lean_object* v_as_4476_, size_t v_sz_4477_, size_t v_i_4478_, lean_object* v_bs_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v___x_4485_; 
v___x_4485_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4473_, v_params_4474_, v_motive_4475_, v_sz_4477_, v_i_4478_, v_bs_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
return v___x_4485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4486_, lean_object* v_params_4487_, lean_object* v_motive_4488_, lean_object* v_as_4489_, lean_object* v_sz_4490_, lean_object* v_i_4491_, lean_object* v_bs_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_){
_start:
{
size_t v_sz_boxed_4498_; size_t v_i_boxed_4499_; lean_object* v_res_4500_; 
v_sz_boxed_4498_ = lean_unbox_usize(v_sz_4490_);
lean_dec(v_sz_4490_);
v_i_boxed_4499_ = lean_unbox_usize(v_i_4491_);
lean_dec(v_i_4491_);
v_res_4500_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4486_, v_params_4487_, v_motive_4488_, v_as_4489_, v_sz_boxed_4498_, v_i_boxed_4499_, v_bs_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_);
lean_dec(v___y_4496_);
lean_dec_ref(v___y_4495_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec_ref(v_as_4489_);
lean_dec_ref(v_params_4487_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4501_, lean_object* v_params_4502_, lean_object* v_a_4503_, lean_object* v_snd_4504_, lean_object* v_alts_4505_, lean_object* v_as_4506_, size_t v_sz_4507_, size_t v_i_4508_, lean_object* v_bs_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4501_, v_params_4502_, v_a_4503_, v_snd_4504_, v_alts_4505_, v_sz_4507_, v_i_4508_, v_bs_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4516_, lean_object* v_params_4517_, lean_object* v_a_4518_, lean_object* v_snd_4519_, lean_object* v_alts_4520_, lean_object* v_as_4521_, lean_object* v_sz_4522_, lean_object* v_i_4523_, lean_object* v_bs_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
size_t v_sz_boxed_4530_; size_t v_i_boxed_4531_; lean_object* v_res_4532_; 
v_sz_boxed_4530_ = lean_unbox_usize(v_sz_4522_);
lean_dec(v_sz_4522_);
v_i_boxed_4531_ = lean_unbox_usize(v_i_4523_);
lean_dec(v_i_4523_);
v_res_4532_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4516_, v_params_4517_, v_a_4518_, v_snd_4519_, v_alts_4520_, v_as_4521_, v_sz_boxed_4530_, v_i_boxed_4531_, v_bs_4524_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
lean_dec(v___y_4528_);
lean_dec_ref(v___y_4527_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec_ref(v_as_4521_);
lean_dec_ref(v_params_4517_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_4533_, lean_object* v_info_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v___x_4540_; 
v___x_4540_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_4533_, v_info_4534_, v___y_4536_, v___y_4538_);
return v___x_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_4541_, lean_object* v_info_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v_res_4548_; 
v_res_4548_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_4541_, v_info_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
lean_dec(v___y_4546_);
lean_dec_ref(v___y_4545_);
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4543_);
return v_res_4548_;
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
