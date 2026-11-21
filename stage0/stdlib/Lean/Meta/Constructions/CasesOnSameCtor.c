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
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__27;
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
lean_object* v___f_286_; lean_object* v___x_16831__overap_287_; lean_object* v___x_288_; 
v___f_286_ = ((lean_object*)(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15___closed__0));
v___x_16831__overap_287_ = lean_panic_fn_borrowed(v___f_286_, v_msg_280_);
lean_inc(v___y_284_);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
v___x_288_ = lean_apply_5(v___x_16831__overap_287_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, lean_box(0));
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
uint8_t v___x_21882__boxed_392_; uint8_t v___x_21883__boxed_393_; uint8_t v___x_21884__boxed_394_; lean_object* v_res_395_; 
v___x_21882__boxed_392_ = lean_unbox(v___x_373_);
v___x_21883__boxed_393_ = lean_unbox(v___x_374_);
v___x_21884__boxed_394_ = lean_unbox(v___x_375_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(v___x_370_, v_ism2_371_, v_motive_372_, v___x_21882__boxed_392_, v___x_21883__boxed_393_, v___x_21884__boxed_394_, v_a_376_, v___f_377_, v_zs1_378_, v_val_379_, v___x_380_, v_indName_381_, v_v_382_, v___x_383_, v_params_384_, v___x_385_, v_h_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
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
uint8_t v___x_21994__boxed_428_; uint8_t v___x_21995__boxed_429_; uint8_t v___x_21996__boxed_430_; lean_object* v_res_431_; 
v___x_21994__boxed_428_ = lean_unbox(v___x_418_);
v___x_21995__boxed_429_ = lean_unbox(v___x_419_);
v___x_21996__boxed_430_ = lean_unbox(v___x_420_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(v___x_414_, v_alts_415_, v___x_416_, v_zs1_417_, v___x_21994__boxed_428_, v___x_21995__boxed_429_, v___x_21996__boxed_430_, v_zs2_421_, v_x_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
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
uint8_t v___x_22055__boxed_526_; uint8_t v___x_22056__boxed_527_; uint8_t v___x_22057__boxed_528_; lean_object* v_res_529_; 
v___x_22055__boxed_526_ = lean_unbox(v___x_502_);
v___x_22056__boxed_527_ = lean_unbox(v___x_503_);
v___x_22057__boxed_528_ = lean_unbox(v___x_504_);
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(v___x_499_, v_alts_500_, v___x_501_, v___x_22055__boxed_526_, v___x_22056__boxed_527_, v___x_22057__boxed_528_, v___x_505_, v___x_506_, v___x_507_, v_ism2_508_, v_motive_509_, v_a_510_, v_val_511_, v_indName_512_, v_v_513_, v___x_514_, v_params_515_, v___x_516_, v___x_517_, v___x_518_, v_zs1_519_, v_ctorRet1_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
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
uint8_t v___x_22297__boxed_701_; uint8_t v___x_22298__boxed_702_; uint8_t v___x_22299__boxed_703_; lean_object* v_res_704_; 
v___x_22297__boxed_701_ = lean_unbox(v___x_679_);
v___x_22298__boxed_702_ = lean_unbox(v___x_680_);
v___x_22299__boxed_703_ = lean_unbox(v___x_681_);
v_res_704_ = l_Lean_mkCasesOnSameCtorHet___lam__0(v_motive_675_, v___x_676_, v_a_677_, v_ism1_678_, v___x_22297__boxed_701_, v___x_22298__boxed_702_, v___x_22299__boxed_703_, v_name_682_, v___x_683_, v_params_684_, v___x_685_, v_tail_686_, v_alts_687_, v_numParams_688_, v_ism2_689_, v_val_690_, v_indName_691_, v___x_692_, v___x_693_, v___x_694_, v_heq_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
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
uint8_t v___x_22420__boxed_767_; uint8_t v___x_22421__boxed_768_; uint8_t v___x_22422__boxed_769_; lean_object* v_res_770_; 
v___x_22420__boxed_767_ = lean_unbox(v___x_751_);
v___x_22421__boxed_768_ = lean_unbox(v___x_752_);
v___x_22422__boxed_769_ = lean_unbox(v___x_753_);
v_res_770_ = l_Lean_mkCasesOnSameCtorHet___lam__1(v_indName_744_, v_tail_745_, v_params_746_, v_ism1_747_, v_ism2_748_, v_motive_749_, v___x_750_, v___x_22420__boxed_767_, v___x_22421__boxed_768_, v___x_22422__boxed_769_, v_name_754_, v___x_755_, v___x_756_, v_numParams_757_, v_val_758_, v___x_759_, v___x_760_, v_alts_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
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
lean_object* v___x_21539__overap_822_; lean_object* v___x_823_; 
v___x_21539__overap_822_ = l_instInhabitedOfMonad___redArg(v___x_814_, v___x_815_);
lean_inc(v___y_820_);
lean_inc_ref(v___y_819_);
lean_inc(v___y_818_);
lean_inc_ref(v___y_817_);
v___x_823_ = lean_apply_5(v___x_21539__overap_822_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, lean_box(0));
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
uint8_t v___x_22859__boxed_1138_; uint8_t v___x_22860__boxed_1139_; uint8_t v___x_22861__boxed_1140_; lean_object* v_res_1141_; 
v___x_22859__boxed_1138_ = lean_unbox(v___x_1126_);
v___x_22860__boxed_1139_ = lean_unbox(v___x_1127_);
v___x_22861__boxed_1140_ = lean_unbox(v___x_1128_);
v_res_1141_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(v___x_1119_, v_dummy_1120_, v___x_1121_, v___x_1122_, v___x_1123_, v_motive_1124_, v_zs1_1125_, v___x_22859__boxed_1138_, v___x_22860__boxed_1139_, v___x_22861__boxed_1140_, v_v_1129_, v___x_1130_, v_zs2_1131_, v_ctorRet2_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
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
uint8_t v___x_23000__boxed_1201_; uint8_t v___x_23001__boxed_1202_; uint8_t v___x_23002__boxed_1203_; lean_object* v_res_1204_; 
v___x_23000__boxed_1201_ = lean_unbox(v___x_1188_);
v___x_23001__boxed_1202_ = lean_unbox(v___x_1189_);
v___x_23002__boxed_1203_ = lean_unbox(v___x_1190_);
v_res_1204_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(v___x_1184_, v___x_1185_, v___x_1186_, v_motive_1187_, v___x_23000__boxed_1201_, v___x_23001__boxed_1202_, v___x_23002__boxed_1203_, v_v_1191_, v___x_1192_, v_a_1193_, v_zs1_1194_, v_ctorRet1_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
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
uint8_t v___x_23180__boxed_1334_; uint8_t v___x_23181__boxed_1335_; uint8_t v___x_23182__boxed_1336_; lean_object* v_res_1337_; 
v___x_23180__boxed_1334_ = lean_unbox(v___x_1319_);
v___x_23181__boxed_1335_ = lean_unbox(v___x_1320_);
v___x_23182__boxed_1336_ = lean_unbox(v___x_1321_);
v_res_1337_ = l_Lean_mkCasesOnSameCtorHet___lam__2(v_ctors_1312_, v_indName_1313_, v_tail_1314_, v_params_1315_, v_ism1_1316_, v_ism2_1317_, v___x_1318_, v___x_23180__boxed_1334_, v___x_23181__boxed_1335_, v___x_23182__boxed_1336_, v_name_1322_, v___x_1323_, v_numParams_1324_, v_val_1325_, v___x_1326_, v___x_1327_, v_motive_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_);
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
uint8_t v___x_23468__boxed_1563_; lean_object* v_res_1564_; 
v___x_23468__boxed_1563_ = lean_unbox(v___x_1557_);
v_res_1564_ = l_Lean_mkCasesOnSameCtorHet___lam__7(v_a_1554_, v_declName_1555_, v_levelParams_1556_, v___x_23468__boxed_1563_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__21(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__20));
v___x_1695_ = l_Lean_stringToMessageData(v___x_1694_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__23(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__22));
v___x_1698_ = l_Lean_stringToMessageData(v___x_1697_);
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__25(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__24));
v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__27(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__26));
v___x_1704_ = l_Lean_stringToMessageData(v___x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(lean_object* v_msg_1705_, lean_object* v_declHint_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v_env_1711_; uint8_t v___x_1712_; 
v___x_1709_ = lean_box(0);
v___x_1710_ = lean_st_ref_get(v___y_1707_);
v_env_1711_ = lean_ctor_get(v___x_1710_, 0);
lean_inc_ref(v_env_1711_);
lean_dec(v___x_1710_);
v___x_1712_ = l_Lean_Name_isAnonymous(v_declHint_1706_);
if (v___x_1712_ == 0)
{
uint8_t v_isExporting_1713_; 
v_isExporting_1713_ = lean_ctor_get_uint8(v_env_1711_, sizeof(void*)*13);
if (v_isExporting_1713_ == 0)
{
lean_object* v___x_1714_; 
lean_dec_ref(v_env_1711_);
lean_dec(v_declHint_1706_);
v___x_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_msg_1705_);
return v___x_1714_;
}
else
{
lean_object* v___x_1715_; uint8_t v___x_1716_; 
lean_inc_ref(v_env_1711_);
v___x_1715_ = l_Lean_Environment_setExporting(v_env_1711_, v___x_1712_);
lean_inc(v_declHint_1706_);
lean_inc_ref(v___x_1715_);
v___x_1716_ = l_Lean_Environment_contains(v___x_1715_, v_declHint_1706_, v_isExporting_1713_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; 
lean_dec_ref(v___x_1715_);
lean_dec_ref(v_env_1711_);
lean_dec(v_declHint_1706_);
v___x_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_msg_1705_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v_c_1723_; lean_object* v___x_1724_; 
v___x_1718_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__2);
v___x_1719_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__5);
v___x_1720_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1715_);
v___x_1721_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1715_);
lean_ctor_set(v___x_1721_, 1, v___x_1718_);
lean_ctor_set(v___x_1721_, 2, v___x_1719_);
lean_ctor_set(v___x_1721_, 3, v___x_1720_);
lean_inc(v_declHint_1706_);
v___x_1722_ = l_Lean_MessageData_ofConstName(v_declHint_1706_, v___x_1712_);
v_c_1723_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1723_, 0, v___x_1721_);
lean_ctor_set(v_c_1723_, 1, v___x_1722_);
v___x_1724_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1715_, v_declHint_1706_);
lean_dec_ref(v___x_1715_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec_ref(v_env_1711_);
lean_dec(v_declHint_1706_);
v___x_1725_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7);
v___x_1726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v_c_1723_);
v___x_1727_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__9);
v___x_1728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1726_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_MessageData_note(v___x_1728_);
v___x_1730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1730_, 0, v_msg_1705_);
lean_ctor_set(v___x_1730_, 1, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
else
{
lean_object* v_val_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1785_; 
v_val_1732_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1734_ = v___x_1724_;
v_isShared_1735_ = v_isSharedCheck_1785_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_val_1732_);
lean_dec(v___x_1724_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1785_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v_modules_1737_; lean_object* v_moduleNames_1738_; lean_object* v_mod_1739_; uint8_t v___x_1754_; 
v___x_1736_ = l_Lean_Environment_header(v_env_1711_);
lean_dec_ref(v_env_1711_);
v_modules_1737_ = lean_ctor_get(v___x_1736_, 3);
lean_inc_ref(v_modules_1737_);
v_moduleNames_1738_ = lean_ctor_get(v___x_1736_, 4);
lean_inc_ref(v_moduleNames_1738_);
lean_dec_ref(v___x_1736_);
v_mod_1739_ = lean_array_get(v___x_1709_, v_moduleNames_1738_, v_val_1732_);
lean_dec_ref(v_moduleNames_1738_);
v___x_1754_ = l_Lean_isPrivateName(v_declHint_1706_);
lean_dec(v_declHint_1706_);
if (v___x_1754_ == 0)
{
lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = lean_array_get_size(v_modules_1737_);
v___x_1756_ = lean_nat_dec_lt(v_val_1732_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_dec_ref(v_modules_1737_);
lean_dec(v_val_1732_);
goto v___jp_1740_;
}
else
{
lean_object* v___x_1757_; lean_object* v_toImport_1758_; uint8_t v_isExported_1759_; 
v___x_1757_ = lean_array_fget(v_modules_1737_, v_val_1732_);
lean_dec(v_val_1732_);
lean_dec_ref(v_modules_1737_);
v_toImport_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc_ref(v_toImport_1758_);
lean_dec(v___x_1757_);
v_isExported_1759_ = lean_ctor_get_uint8(v_toImport_1758_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1758_);
if (v_isExported_1759_ == 0)
{
goto v___jp_1740_;
}
else
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_del_object(v___x_1734_);
v___x_1760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__17);
v___x_1761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v_c_1723_);
v___x_1762_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__19);
v___x_1763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1761_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
v___x_1764_ = l_Lean_MessageData_ofName(v_mod_1739_);
lean_inc_ref(v___x_1764_);
v___x_1765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1763_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
v___x_1766_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__21);
v___x_1767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
v___x_1768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v___x_1764_);
v___x_1769_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__23);
v___x_1770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = l_Lean_MessageData_note(v___x_1770_);
v___x_1772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_msg_1705_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
return v___x_1773_;
}
}
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec_ref(v_modules_1737_);
lean_del_object(v___x_1734_);
lean_dec(v_val_1732_);
v___x_1774_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__7);
v___x_1775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
lean_ctor_set(v___x_1775_, 1, v_c_1723_);
v___x_1776_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__25);
v___x_1777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1777_, 0, v___x_1775_);
lean_ctor_set(v___x_1777_, 1, v___x_1776_);
v___x_1778_ = l_Lean_MessageData_ofName(v_mod_1739_);
v___x_1779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1777_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v___x_1780_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__27);
v___x_1781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1779_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
v___x_1782_ = l_Lean_MessageData_note(v___x_1781_);
v___x_1783_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1783_, 0, v_msg_1705_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
return v___x_1784_;
}
v___jp_1740_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__11);
v___x_1742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v_c_1723_);
v___x_1743_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__13);
v___x_1744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1742_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = l_Lean_MessageData_ofName(v_mod_1739_);
v___x_1746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v___x_1747_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__15);
v___x_1748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1746_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
v___x_1749_ = l_Lean_MessageData_note(v___x_1748_);
v___x_1750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1750_, 0, v_msg_1705_);
lean_ctor_set(v___x_1750_, 1, v___x_1749_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set_tag(v___x_1734_, 0);
lean_ctor_set(v___x_1734_, 0, v___x_1750_);
v___x_1752_ = v___x_1734_;
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
lean_object* v___x_1786_; 
lean_dec_ref(v_env_1711_);
lean_dec(v_declHint_1706_);
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_msg_1705_);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___boxed(lean_object* v_msg_1787_, lean_object* v_declHint_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(v_msg_1787_, v_declHint_1788_, v___y_1789_);
lean_dec(v___y_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(lean_object* v_msg_1792_, lean_object* v_declHint_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1809_; 
v___x_1799_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(v_msg_1792_, v_declHint_1793_, v___y_1797_);
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1809_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1809_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1804_ = l_Lean_unknownIdentifierMessageTag;
v___x_1805_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v_a_1800_);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1805_);
v___x_1807_ = v___x_1802_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24___boxed(lean_object* v_msg_1810_, lean_object* v_declHint_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(v_msg_1810_, v_declHint_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(lean_object* v_ref_1818_, lean_object* v_msg_1819_, lean_object* v_declHint_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; lean_object* v_a_1827_; lean_object* v___x_1828_; 
v___x_1826_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24(v_msg_1819_, v_declHint_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
lean_inc(v_a_1827_);
lean_dec_ref(v___x_1826_);
v___x_1828_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(v_ref_1818_, v_a_1827_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg___boxed(lean_object* v_ref_1829_, lean_object* v_msg_1830_, lean_object* v_declHint_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(v_ref_1829_, v_msg_1830_, v_declHint_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
lean_dec(v___y_1835_);
lean_dec_ref(v___y_1834_);
lean_dec(v___y_1833_);
lean_dec_ref(v___y_1832_);
lean_dec(v_ref_1829_);
return v_res_1837_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__0));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__2));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(lean_object* v_ref_1844_, lean_object* v_constName_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1851_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__1);
v___x_1852_ = 0;
lean_inc(v_constName_1845_);
v___x_1853_ = l_Lean_MessageData_ofConstName(v_constName_1845_, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1851_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3);
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(v_ref_1844_, v___x_1856_, v_constName_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___boxed(lean_object* v_ref_1858_, lean_object* v_constName_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(v_ref_1858_, v_constName_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v_ref_1858_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(lean_object* v_constName_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
lean_object* v_ref_1872_; lean_object* v___x_1873_; 
v_ref_1872_ = lean_ctor_get(v___y_1869_, 2);
v___x_1873_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(v_ref_1872_, v_constName_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(lean_object* v_constName_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; lean_object* v_env_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; 
v___x_1887_ = lean_st_ref_get(v___y_1885_);
v_env_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc_ref(v_env_1888_);
lean_dec(v___x_1887_);
v___x_1889_ = 0;
lean_inc(v_constName_1881_);
v___x_1890_ = l_Lean_Environment_findConstVal_x3f(v_env_1888_, v_constName_1881_, v___x_1889_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v___x_1891_;
}
else
{
lean_object* v_val_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v_constName_1881_);
v_val_1892_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1890_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_val_1892_);
lean_dec(v___x_1890_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
lean_ctor_set_tag(v___x_1894_, 0);
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_val_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(lean_object* v_constName_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v_constName_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec(v___y_1902_);
lean_dec_ref(v___y_1901_);
return v_res_1906_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(lean_object* v___dummy_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg();
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(lean_object* v___y_1913_, uint8_t v_isExporting_1914_, lean_object* v___x_1915_, lean_object* v___y_1916_, lean_object* v___x_1917_, lean_object* v_a_x3f_1918_){
_start:
{
lean_object* v___x_1920_; lean_object* v_env_1921_; lean_object* v_nextMacroScope_1922_; lean_object* v_ngen_1923_; lean_object* v_auxDeclNGen_1924_; lean_object* v_traceState_1925_; lean_object* v_recordedDeps_1926_; lean_object* v_messages_1927_; lean_object* v_infoState_1928_; lean_object* v_snapshotTasks_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1954_; 
v___x_1920_ = lean_st_ref_take(v___y_1913_);
v_env_1921_ = lean_ctor_get(v___x_1920_, 0);
v_nextMacroScope_1922_ = lean_ctor_get(v___x_1920_, 1);
v_ngen_1923_ = lean_ctor_get(v___x_1920_, 2);
v_auxDeclNGen_1924_ = lean_ctor_get(v___x_1920_, 3);
v_traceState_1925_ = lean_ctor_get(v___x_1920_, 4);
v_recordedDeps_1926_ = lean_ctor_get(v___x_1920_, 6);
v_messages_1927_ = lean_ctor_get(v___x_1920_, 7);
v_infoState_1928_ = lean_ctor_get(v___x_1920_, 8);
v_snapshotTasks_1929_ = lean_ctor_get(v___x_1920_, 9);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1954_ == 0)
{
lean_object* v_unused_1955_; 
v_unused_1955_ = lean_ctor_get(v___x_1920_, 5);
lean_dec(v_unused_1955_);
v___x_1931_ = v___x_1920_;
v_isShared_1932_ = v_isSharedCheck_1954_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_snapshotTasks_1929_);
lean_inc(v_infoState_1928_);
lean_inc(v_messages_1927_);
lean_inc(v_recordedDeps_1926_);
lean_inc(v_traceState_1925_);
lean_inc(v_auxDeclNGen_1924_);
lean_inc(v_ngen_1923_);
lean_inc(v_nextMacroScope_1922_);
lean_inc(v_env_1921_);
lean_dec(v___x_1920_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1954_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1933_ = l_Lean_Environment_setExporting(v_env_1921_, v_isExporting_1914_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 5, v___x_1915_);
lean_ctor_set(v___x_1931_, 0, v___x_1933_);
v___x_1935_ = v___x_1931_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_nextMacroScope_1922_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v_ngen_1923_);
lean_ctor_set(v_reuseFailAlloc_1953_, 3, v_auxDeclNGen_1924_);
lean_ctor_set(v_reuseFailAlloc_1953_, 4, v_traceState_1925_);
lean_ctor_set(v_reuseFailAlloc_1953_, 5, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1953_, 6, v_recordedDeps_1926_);
lean_ctor_set(v_reuseFailAlloc_1953_, 7, v_messages_1927_);
lean_ctor_set(v_reuseFailAlloc_1953_, 8, v_infoState_1928_);
lean_ctor_set(v_reuseFailAlloc_1953_, 9, v_snapshotTasks_1929_);
v___x_1935_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v_mctx_1938_; lean_object* v_zetaDeltaFVarIds_1939_; lean_object* v_postponed_1940_; lean_object* v_diag_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1951_; 
v___x_1936_ = lean_st_ref_put(v___y_1913_, v___x_1935_);
v___x_1937_ = lean_st_ref_take(v___y_1916_);
v_mctx_1938_ = lean_ctor_get(v___x_1937_, 0);
v_zetaDeltaFVarIds_1939_ = lean_ctor_get(v___x_1937_, 2);
v_postponed_1940_ = lean_ctor_get(v___x_1937_, 3);
v_diag_1941_ = lean_ctor_get(v___x_1937_, 4);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v___x_1937_, 1);
lean_dec(v_unused_1952_);
v___x_1943_ = v___x_1937_;
v_isShared_1944_ = v_isSharedCheck_1951_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_diag_1941_);
lean_inc(v_postponed_1940_);
lean_inc(v_zetaDeltaFVarIds_1939_);
lean_inc(v_mctx_1938_);
lean_dec(v___x_1937_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1951_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1945_; lean_object* v___x_1947_; 
v___x_1945_ = lean_box(0);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 1, v___x_1917_);
v___x_1947_ = v___x_1943_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_mctx_1938_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1950_, 2, v_zetaDeltaFVarIds_1939_);
lean_ctor_set(v_reuseFailAlloc_1950_, 3, v_postponed_1940_);
lean_ctor_set(v_reuseFailAlloc_1950_, 4, v_diag_1941_);
v___x_1947_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1948_ = lean_st_ref_put(v___y_1916_, v___x_1947_);
v___x_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1945_);
return v___x_1949_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(lean_object* v___y_1956_, lean_object* v_isExporting_1957_, lean_object* v___x_1958_, lean_object* v___y_1959_, lean_object* v___x_1960_, lean_object* v_a_x3f_1961_, lean_object* v___y_1962_){
_start:
{
uint8_t v_isExporting_boxed_1963_; lean_object* v_res_1964_; 
v_isExporting_boxed_1963_ = lean_unbox(v_isExporting_1957_);
v_res_1964_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_1956_, v_isExporting_boxed_1963_, v___x_1958_, v___y_1959_, v___x_1960_, v_a_x3f_1961_);
lean_dec(v_a_x3f_1961_);
lean_dec(v___y_1959_);
lean_dec(v___y_1956_);
return v_res_1964_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg___closed__0);
v___x_1966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg();
return v___x_1969_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3(void){
_start:
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
return v___x_1971_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__4(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = lean_unsigned_to_nat(0u);
v___x_1973_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1974_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
lean_ctor_set(v___x_1974_, 2, v___x_1972_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1975_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__4, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__4_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__4);
v___x_1976_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
v___x_1977_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
v___x_1978_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
v___x_1979_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v___x_1977_);
lean_ctor_set(v___x_1979_, 2, v___x_1976_);
lean_ctor_set(v___x_1979_, 3, v___x_1977_);
lean_ctor_set(v___x_1979_, 4, v___x_1977_);
lean_ctor_set(v___x_1979_, 5, v___x_1977_);
lean_ctor_set(v___x_1979_, 6, v___x_1975_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(lean_object* v_x_1980_, uint8_t v_isExporting_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v_env_1988_; lean_object* v___x_1989_; uint8_t v_isModule_1990_; 
v___x_1987_ = lean_st_ref_get(v___y_1985_);
v_env_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc_ref(v_env_1988_);
lean_dec(v___x_1987_);
v___x_1989_ = l_Lean_Environment_header(v_env_1988_);
v_isModule_1990_ = lean_ctor_get_uint8(v___x_1989_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1989_);
if (v_isModule_1990_ == 0)
{
lean_object* v___x_1991_; 
lean_dec_ref(v_env_1988_);
lean_inc(v___y_1985_);
lean_inc_ref(v___y_1984_);
lean_inc(v___y_1983_);
lean_inc_ref(v___y_1982_);
v___x_1991_ = lean_apply_5(v_x_1980_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, lean_box(0));
return v___x_1991_;
}
else
{
uint8_t v_isExporting_1992_; 
v_isExporting_1992_ = lean_ctor_get_uint8(v_env_1988_, sizeof(void*)*13);
lean_dec_ref(v_env_1988_);
if (v_isExporting_1981_ == 0)
{
if (v_isExporting_1992_ == 0)
{
lean_object* v___x_2059_; 
lean_inc(v___y_1985_);
lean_inc_ref(v___y_1984_);
lean_inc(v___y_1983_);
lean_inc_ref(v___y_1982_);
v___x_2059_ = lean_apply_5(v_x_1980_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, lean_box(0));
return v___x_2059_;
}
else
{
goto v___jp_1993_;
}
}
else
{
if (v_isExporting_1992_ == 0)
{
goto v___jp_1993_;
}
else
{
lean_object* v___x_2060_; 
lean_inc(v___y_1985_);
lean_inc_ref(v___y_1984_);
lean_inc(v___y_1983_);
lean_inc_ref(v___y_1982_);
v___x_2060_ = lean_apply_5(v_x_1980_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, lean_box(0));
return v___x_2060_;
}
}
v___jp_1993_:
{
lean_object* v___x_1994_; lean_object* v_env_1995_; lean_object* v_nextMacroScope_1996_; lean_object* v_ngen_1997_; lean_object* v_auxDeclNGen_1998_; lean_object* v_traceState_1999_; lean_object* v_recordedDeps_2000_; lean_object* v_messages_2001_; lean_object* v_infoState_2002_; lean_object* v_snapshotTasks_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2057_; 
v___x_1994_ = lean_st_ref_take(v___y_1985_);
v_env_1995_ = lean_ctor_get(v___x_1994_, 0);
v_nextMacroScope_1996_ = lean_ctor_get(v___x_1994_, 1);
v_ngen_1997_ = lean_ctor_get(v___x_1994_, 2);
v_auxDeclNGen_1998_ = lean_ctor_get(v___x_1994_, 3);
v_traceState_1999_ = lean_ctor_get(v___x_1994_, 4);
v_recordedDeps_2000_ = lean_ctor_get(v___x_1994_, 6);
v_messages_2001_ = lean_ctor_get(v___x_1994_, 7);
v_infoState_2002_ = lean_ctor_get(v___x_1994_, 8);
v_snapshotTasks_2003_ = lean_ctor_get(v___x_1994_, 9);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v___x_1994_, 5);
lean_dec(v_unused_2058_);
v___x_2005_ = v___x_1994_;
v_isShared_2006_ = v_isSharedCheck_2057_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snapshotTasks_2003_);
lean_inc(v_infoState_2002_);
lean_inc(v_messages_2001_);
lean_inc(v_recordedDeps_2000_);
lean_inc(v_traceState_1999_);
lean_inc(v_auxDeclNGen_1998_);
lean_inc(v_ngen_1997_);
lean_inc(v_nextMacroScope_1996_);
lean_inc(v_env_1995_);
lean_dec(v___x_1994_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2057_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2007_ = l_Lean_Environment_setExporting(v_env_1995_, v_isExporting_1981_);
v___x_2008_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 5, v___x_2008_);
lean_ctor_set(v___x_2005_, 0, v___x_2007_);
v___x_2010_ = v___x_2005_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_nextMacroScope_1996_);
lean_ctor_set(v_reuseFailAlloc_2056_, 2, v_ngen_1997_);
lean_ctor_set(v_reuseFailAlloc_2056_, 3, v_auxDeclNGen_1998_);
lean_ctor_set(v_reuseFailAlloc_2056_, 4, v_traceState_1999_);
lean_ctor_set(v_reuseFailAlloc_2056_, 5, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2056_, 6, v_recordedDeps_2000_);
lean_ctor_set(v_reuseFailAlloc_2056_, 7, v_messages_2001_);
lean_ctor_set(v_reuseFailAlloc_2056_, 8, v_infoState_2002_);
lean_ctor_set(v_reuseFailAlloc_2056_, 9, v_snapshotTasks_2003_);
v___x_2010_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v_mctx_2013_; lean_object* v_zetaDeltaFVarIds_2014_; lean_object* v_postponed_2015_; lean_object* v_diag_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2054_; 
v___x_2011_ = lean_st_ref_put(v___y_1985_, v___x_2010_);
v___x_2012_ = lean_st_ref_take(v___y_1983_);
v_mctx_2013_ = lean_ctor_get(v___x_2012_, 0);
v_zetaDeltaFVarIds_2014_ = lean_ctor_get(v___x_2012_, 2);
v_postponed_2015_ = lean_ctor_get(v___x_2012_, 3);
v_diag_2016_ = lean_ctor_get(v___x_2012_, 4);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v___x_2012_, 1);
lean_dec(v_unused_2055_);
v___x_2018_ = v___x_2012_;
v_isShared_2019_ = v_isSharedCheck_2054_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_diag_2016_);
lean_inc(v_postponed_2015_);
lean_inc(v_zetaDeltaFVarIds_2014_);
lean_inc(v_mctx_2013_);
lean_dec(v___x_2012_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2054_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 1, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_mctx_2013_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2053_, 2, v_zetaDeltaFVarIds_2014_);
lean_ctor_set(v_reuseFailAlloc_2053_, 3, v_postponed_2015_);
lean_ctor_set(v_reuseFailAlloc_2053_, 4, v_diag_2016_);
v___x_2022_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2023_; lean_object* v_r_2024_; 
v___x_2023_ = lean_st_ref_put(v___y_1983_, v___x_2022_);
lean_inc(v___y_1985_);
lean_inc_ref(v___y_1984_);
lean_inc(v___y_1983_);
lean_inc_ref(v___y_1982_);
v_r_2024_ = lean_apply_5(v_x_1980_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, lean_box(0));
if (lean_obj_tag(v_r_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2041_; 
v_a_2025_ = lean_ctor_get(v_r_2024_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_r_2024_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2027_ = v_r_2024_;
v_isShared_2028_ = v_isSharedCheck_2041_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v_r_2024_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2041_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
lean_inc(v_a_2025_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set_tag(v___x_2027_, 1);
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
v___x_2031_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_1985_, v_isExporting_1992_, v___x_2008_, v___y_1983_, v___x_2020_, v___x_2030_);
lean_dec_ref(v___x_2030_);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2038_ == 0)
{
lean_object* v_unused_2039_; 
v_unused_2039_ = lean_ctor_get(v___x_2031_, 0);
lean_dec(v_unused_2039_);
v___x_2033_ = v___x_2031_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v___x_2031_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v_a_2025_);
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2025_);
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
else
{
lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_a_2042_ = lean_ctor_get(v_r_2024_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v_r_2024_, 1);
v___x_2043_ = lean_box(0);
v___x_2044_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_1985_, v_isExporting_1992_, v___x_2008_, v___y_1983_, v___x_2020_, v___x_2043_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2044_, 0);
lean_dec(v_unused_2052_);
v___x_2046_ = v___x_2044_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_dec(v___x_2044_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set_tag(v___x_2046_, 1);
lean_ctor_set(v___x_2046_, 0, v_a_2042_);
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2042_);
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(lean_object* v_x_2061_, lean_object* v_isExporting_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
uint8_t v_isExporting_boxed_2068_; lean_object* v_res_2069_; 
v_isExporting_boxed_2068_ = lean_unbox(v_isExporting_2062_);
v_res_2069_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_2061_, v_isExporting_boxed_2068_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___lam__0(lean_object* v_addEntryFn_2070_, lean_object* v_decl_2071_, lean_object* v_s_2072_){
_start:
{
lean_object* v_importedEntries_2073_; lean_object* v_state_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2082_; 
v_importedEntries_2073_ = lean_ctor_get(v_s_2072_, 0);
v_state_2074_ = lean_ctor_get(v_s_2072_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_s_2072_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2076_ = v_s_2072_;
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_state_2074_);
lean_inc(v_importedEntries_2073_);
lean_dec(v_s_2072_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v_state_2078_; lean_object* v___x_2080_; 
v_state_2078_ = lean_apply_2(v_addEntryFn_2070_, v_state_2074_, v_decl_2071_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 1, v_state_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_importedEntries_2073_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v_state_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__0));
v___x_2085_ = l_Lean_stringToMessageData(v___x_2084_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__2));
v___x_2088_ = l_Lean_stringToMessageData(v___x_2087_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__4));
v___x_2091_ = l_Lean_stringToMessageData(v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(lean_object* v_attrName_2092_, lean_object* v_declName_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2099_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1);
v___x_2100_ = l_Lean_MessageData_ofName(v_attrName_2092_);
v___x_2101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2099_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3);
v___x_2103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2101_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = 0;
v___x_2105_ = l_Lean_MessageData_ofConstName(v_declName_2093_, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2103_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
v___x_2107_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__5);
v___x_2108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2106_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
v___x_2109_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_2108_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(lean_object* v_attrName_2110_, lean_object* v_declName_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_attrName_2110_, v_declName_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
lean_dec(v___y_2115_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
return v_res_2117_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__0));
v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__2));
v___x_2123_ = l_Lean_stringToMessageData(v___x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(lean_object* v_attrName_2124_, lean_object* v_declName_2125_, lean_object* v_asyncPrefix_x3f_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___y_2133_; 
if (lean_obj_tag(v_asyncPrefix_x3f_2126_) == 0)
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_MessageData_nil;
v___y_2133_ = v___x_2146_;
goto v___jp_2132_;
}
else
{
lean_object* v_val_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v_val_2147_ = lean_ctor_get(v_asyncPrefix_x3f_2126_, 0);
lean_inc(v_val_2147_);
lean_dec_ref_known(v_asyncPrefix_x3f_2126_, 1);
v___x_2148_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__3);
v___x_2149_ = l_Lean_MessageData_ofName(v_val_2147_);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg___closed__3);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2150_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___y_2133_ = v___x_2152_;
goto v___jp_2132_;
}
v___jp_2132_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2134_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__1);
v___x_2135_ = l_Lean_MessageData_ofName(v_attrName_2124_);
v___x_2136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2134_);
lean_ctor_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___closed__3);
v___x_2138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2136_);
lean_ctor_set(v___x_2138_, 1, v___x_2137_);
v___x_2139_ = 0;
v___x_2140_ = l_Lean_MessageData_ofConstName(v_declName_2125_, v___x_2139_);
v___x_2141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2138_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___closed__1);
v___x_2143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2141_);
lean_ctor_set(v___x_2143_, 1, v___x_2142_);
v___x_2144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2144_, 0, v___x_2143_);
lean_ctor_set(v___x_2144_, 1, v___y_2133_);
v___x_2145_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_2144_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_);
return v___x_2145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg___boxed(lean_object* v_attrName_2153_, lean_object* v_declName_2154_, lean_object* v_asyncPrefix_x3f_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(v_attrName_2153_, v_declName_2154_, v_asyncPrefix_x3f_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(lean_object* v_attr_2162_, lean_object* v_decl_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v___y_2170_; lean_object* v___y_2171_; lean_object* v___y_2172_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2176_; lean_object* v___y_2177_; lean_object* v___y_2178_; lean_object* v___y_2179_; lean_object* v___y_2180_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___x_2224_; lean_object* v_env_2225_; lean_object* v___y_2227_; lean_object* v___y_2228_; lean_object* v___y_2229_; lean_object* v___y_2230_; lean_object* v___x_2240_; 
v___x_2224_ = lean_st_ref_get(v___y_2167_);
v_env_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc_ref(v_env_2225_);
lean_dec(v___x_2224_);
v___x_2240_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2225_, v_decl_2163_);
if (lean_obj_tag(v___x_2240_) == 0)
{
v___y_2227_ = v___y_2164_;
v___y_2228_ = v___y_2165_;
v___y_2229_ = v___y_2166_;
v___y_2230_ = v___y_2167_;
goto v___jp_2226_;
}
else
{
lean_object* v_attr_2241_; lean_object* v_toAttributeImplCore_2242_; lean_object* v_name_2243_; lean_object* v___x_2244_; 
lean_dec_ref_known(v___x_2240_, 1);
lean_dec_ref(v_env_2225_);
v_attr_2241_ = lean_ctor_get(v_attr_2162_, 0);
lean_inc_ref(v_attr_2241_);
lean_dec_ref(v_attr_2162_);
v_toAttributeImplCore_2242_ = lean_ctor_get(v_attr_2241_, 0);
lean_inc_ref(v_toAttributeImplCore_2242_);
lean_dec_ref(v_attr_2241_);
v_name_2243_ = lean_ctor_get(v_toAttributeImplCore_2242_, 1);
lean_inc(v_name_2243_);
lean_dec_ref(v_toAttributeImplCore_2242_);
v___x_2244_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_name_2243_, v_decl_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
return v___x_2244_;
}
v___jp_2169_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v_mctx_2185_; lean_object* v_zetaDeltaFVarIds_2186_; lean_object* v_postponed_2187_; lean_object* v_diag_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2199_; 
v___x_2181_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
v___x_2182_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2182_, 0, v___y_2180_);
lean_ctor_set(v___x_2182_, 1, v___y_2175_);
lean_ctor_set(v___x_2182_, 2, v___y_2178_);
lean_ctor_set(v___x_2182_, 3, v___y_2171_);
lean_ctor_set(v___x_2182_, 4, v___y_2179_);
lean_ctor_set(v___x_2182_, 5, v___x_2181_);
lean_ctor_set(v___x_2182_, 6, v___y_2173_);
lean_ctor_set(v___x_2182_, 7, v___y_2172_);
lean_ctor_set(v___x_2182_, 8, v___y_2170_);
lean_ctor_set(v___x_2182_, 9, v___y_2177_);
v___x_2183_ = lean_st_ref_put(v___y_2174_, v___x_2182_);
v___x_2184_ = lean_st_ref_take(v___y_2176_);
v_mctx_2185_ = lean_ctor_get(v___x_2184_, 0);
v_zetaDeltaFVarIds_2186_ = lean_ctor_get(v___x_2184_, 2);
v_postponed_2187_ = lean_ctor_get(v___x_2184_, 3);
v_diag_2188_ = lean_ctor_get(v___x_2184_, 4);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2199_ == 0)
{
lean_object* v_unused_2200_; 
v_unused_2200_ = lean_ctor_get(v___x_2184_, 1);
lean_dec(v_unused_2200_);
v___x_2190_ = v___x_2184_;
v_isShared_2191_ = v_isSharedCheck_2199_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_diag_2188_);
lean_inc(v_postponed_2187_);
lean_inc(v_zetaDeltaFVarIds_2186_);
lean_inc(v_mctx_2185_);
lean_dec(v___x_2184_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2199_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2192_ = lean_box(0);
v___x_2193_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 1, v___x_2193_);
v___x_2195_ = v___x_2190_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_mctx_2185_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_zetaDeltaFVarIds_2186_);
lean_ctor_set(v_reuseFailAlloc_2198_, 3, v_postponed_2187_);
lean_ctor_set(v_reuseFailAlloc_2198_, 4, v_diag_2188_);
v___x_2195_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = lean_st_ref_put(v___y_2176_, v___x_2195_);
v___x_2197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2192_);
return v___x_2197_;
}
}
}
v___jp_2201_:
{
lean_object* v___x_2204_; lean_object* v_ext_2205_; lean_object* v_toEnvExtension_2206_; lean_object* v_env_2207_; lean_object* v_nextMacroScope_2208_; lean_object* v_ngen_2209_; lean_object* v_auxDeclNGen_2210_; lean_object* v_traceState_2211_; lean_object* v_recordedDeps_2212_; lean_object* v_messages_2213_; lean_object* v_infoState_2214_; lean_object* v_snapshotTasks_2215_; lean_object* v_addEntryFn_2216_; lean_object* v_asyncMode_2217_; uint8_t v_logWrites_2218_; lean_object* v___f_2219_; uint8_t v___x_2220_; 
v___x_2204_ = lean_st_ref_take(v___y_2203_);
v_ext_2205_ = lean_ctor_get(v_attr_2162_, 1);
lean_inc_ref(v_ext_2205_);
lean_dec_ref(v_attr_2162_);
v_toEnvExtension_2206_ = lean_ctor_get(v_ext_2205_, 0);
lean_inc_ref(v_toEnvExtension_2206_);
v_env_2207_ = lean_ctor_get(v___x_2204_, 0);
lean_inc_ref(v_env_2207_);
v_nextMacroScope_2208_ = lean_ctor_get(v___x_2204_, 1);
lean_inc(v_nextMacroScope_2208_);
v_ngen_2209_ = lean_ctor_get(v___x_2204_, 2);
lean_inc_ref(v_ngen_2209_);
v_auxDeclNGen_2210_ = lean_ctor_get(v___x_2204_, 3);
lean_inc_ref(v_auxDeclNGen_2210_);
v_traceState_2211_ = lean_ctor_get(v___x_2204_, 4);
lean_inc_ref(v_traceState_2211_);
v_recordedDeps_2212_ = lean_ctor_get(v___x_2204_, 6);
lean_inc_ref(v_recordedDeps_2212_);
v_messages_2213_ = lean_ctor_get(v___x_2204_, 7);
lean_inc_ref(v_messages_2213_);
v_infoState_2214_ = lean_ctor_get(v___x_2204_, 8);
lean_inc_ref(v_infoState_2214_);
v_snapshotTasks_2215_ = lean_ctor_get(v___x_2204_, 9);
lean_inc_ref(v_snapshotTasks_2215_);
lean_dec(v___x_2204_);
v_addEntryFn_2216_ = lean_ctor_get(v_ext_2205_, 3);
lean_inc(v_addEntryFn_2216_);
lean_dec_ref(v_ext_2205_);
v_asyncMode_2217_ = lean_ctor_get(v_toEnvExtension_2206_, 2);
lean_inc(v_asyncMode_2217_);
v_logWrites_2218_ = lean_ctor_get_uint8(v_toEnvExtension_2206_, sizeof(void*)*6);
lean_inc(v_decl_2163_);
v___f_2219_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___lam__0), 3, 2);
lean_closure_set(v___f_2219_, 0, v_addEntryFn_2216_);
lean_closure_set(v___f_2219_, 1, v_decl_2163_);
v___x_2220_ = 1;
if (v_logWrites_2218_ == 0)
{
lean_object* v___x_2221_; 
v___x_2221_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2206_, v_env_2207_, v___f_2219_, v_asyncMode_2217_, v_decl_2163_, v___x_2220_);
lean_dec(v_asyncMode_2217_);
v___y_2170_ = v_infoState_2214_;
v___y_2171_ = v_auxDeclNGen_2210_;
v___y_2172_ = v_messages_2213_;
v___y_2173_ = v_recordedDeps_2212_;
v___y_2174_ = v___y_2203_;
v___y_2175_ = v_nextMacroScope_2208_;
v___y_2176_ = v___y_2202_;
v___y_2177_ = v_snapshotTasks_2215_;
v___y_2178_ = v_ngen_2209_;
v___y_2179_ = v_traceState_2211_;
v___y_2180_ = v___x_2221_;
goto v___jp_2169_;
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_inc_ref(v_toEnvExtension_2206_);
v___x_2222_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2206_, v_env_2207_);
lean_dec_ref(v_env_2207_);
v___x_2223_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2206_, v___x_2222_, v___f_2219_, v_asyncMode_2217_, v_decl_2163_, v___x_2220_);
lean_dec(v_asyncMode_2217_);
v___y_2170_ = v_infoState_2214_;
v___y_2171_ = v_auxDeclNGen_2210_;
v___y_2172_ = v_messages_2213_;
v___y_2173_ = v_recordedDeps_2212_;
v___y_2174_ = v___y_2203_;
v___y_2175_ = v_nextMacroScope_2208_;
v___y_2176_ = v___y_2202_;
v___y_2177_ = v_snapshotTasks_2215_;
v___y_2178_ = v_ngen_2209_;
v___y_2179_ = v_traceState_2211_;
v___y_2180_ = v___x_2223_;
goto v___jp_2169_;
}
}
v___jp_2226_:
{
lean_object* v_ext_2231_; lean_object* v_toEnvExtension_2232_; lean_object* v_attr_2233_; lean_object* v_asyncMode_2234_; uint8_t v___x_2235_; 
v_ext_2231_ = lean_ctor_get(v_attr_2162_, 1);
v_toEnvExtension_2232_ = lean_ctor_get(v_ext_2231_, 0);
v_attr_2233_ = lean_ctor_get(v_attr_2162_, 0);
v_asyncMode_2234_ = lean_ctor_get(v_toEnvExtension_2232_, 2);
lean_inc(v_decl_2163_);
lean_inc_ref(v_env_2225_);
v___x_2235_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2225_, v_decl_2163_, v_asyncMode_2234_);
if (v___x_2235_ == 0)
{
lean_object* v_toAttributeImplCore_2236_; lean_object* v_name_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_inc_ref(v_attr_2233_);
lean_dec_ref(v_attr_2162_);
v_toAttributeImplCore_2236_ = lean_ctor_get(v_attr_2233_, 0);
lean_inc_ref(v_toAttributeImplCore_2236_);
lean_dec_ref(v_attr_2233_);
v_name_2237_ = lean_ctor_get(v_toAttributeImplCore_2236_, 1);
lean_inc(v_name_2237_);
lean_dec_ref(v_toAttributeImplCore_2236_);
v___x_2238_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2225_);
v___x_2239_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(v_name_2237_, v_decl_2163_, v___x_2238_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2239_;
}
else
{
lean_dec_ref(v_env_2225_);
v___y_2202_ = v___y_2228_;
v___y_2203_ = v___y_2230_;
goto v___jp_2201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(lean_object* v_attr_2245_, lean_object* v_decl_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(v_attr_2245_, v_decl_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(lean_object* v_constName_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; lean_object* v_env_2260_; uint8_t v___x_2261_; lean_object* v___x_2262_; 
v___x_2259_ = lean_st_ref_get(v___y_2257_);
v_env_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc_ref(v_env_2260_);
lean_dec(v___x_2259_);
v___x_2261_ = 0;
lean_inc(v_constName_2253_);
v___x_2262_ = l_Lean_Environment_find_x3f(v_env_2260_, v_constName_2253_, v___x_2261_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v___x_2263_; 
v___x_2263_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2263_;
}
else
{
lean_object* v_val_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2271_; 
lean_dec(v_constName_2253_);
v_val_2264_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2271_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2266_ = v___x_2262_;
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_val_2264_);
lean_dec(v___x_2262_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2271_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v___x_2269_; 
if (v_isShared_2267_ == 0)
{
lean_ctor_set_tag(v___x_2266_, 0);
v___x_2269_ = v___x_2266_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_val_2264_);
v___x_2269_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
return v___x_2269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(lean_object* v_constName_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_constName_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(lean_object* v_declName_2279_, uint8_t v_s_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; lean_object* v_env_2285_; lean_object* v_nextMacroScope_2286_; lean_object* v_ngen_2287_; lean_object* v_auxDeclNGen_2288_; lean_object* v_traceState_2289_; lean_object* v_recordedDeps_2290_; lean_object* v_messages_2291_; lean_object* v_infoState_2292_; lean_object* v_snapshotTasks_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2322_; 
v___x_2284_ = lean_st_ref_take(v___y_2282_);
v_env_2285_ = lean_ctor_get(v___x_2284_, 0);
v_nextMacroScope_2286_ = lean_ctor_get(v___x_2284_, 1);
v_ngen_2287_ = lean_ctor_get(v___x_2284_, 2);
v_auxDeclNGen_2288_ = lean_ctor_get(v___x_2284_, 3);
v_traceState_2289_ = lean_ctor_get(v___x_2284_, 4);
v_recordedDeps_2290_ = lean_ctor_get(v___x_2284_, 6);
v_messages_2291_ = lean_ctor_get(v___x_2284_, 7);
v_infoState_2292_ = lean_ctor_get(v___x_2284_, 8);
v_snapshotTasks_2293_ = lean_ctor_get(v___x_2284_, 9);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2284_, 5);
lean_dec(v_unused_2323_);
v___x_2295_ = v___x_2284_;
v_isShared_2296_ = v_isSharedCheck_2322_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_snapshotTasks_2293_);
lean_inc(v_infoState_2292_);
lean_inc(v_messages_2291_);
lean_inc(v_recordedDeps_2290_);
lean_inc(v_traceState_2289_);
lean_inc(v_auxDeclNGen_2288_);
lean_inc(v_ngen_2287_);
lean_inc(v_nextMacroScope_2286_);
lean_inc(v_env_2285_);
lean_dec(v___x_2284_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2322_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
uint8_t v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2297_ = 0;
v___x_2298_ = lean_box(0);
v___x_2299_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_2285_, v_declName_2279_, v_s_2280_, v___x_2297_, v___x_2298_);
v___x_2300_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 5, v___x_2300_);
lean_ctor_set(v___x_2295_, 0, v___x_2299_);
v___x_2302_ = v___x_2295_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2299_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_nextMacroScope_2286_);
lean_ctor_set(v_reuseFailAlloc_2321_, 2, v_ngen_2287_);
lean_ctor_set(v_reuseFailAlloc_2321_, 3, v_auxDeclNGen_2288_);
lean_ctor_set(v_reuseFailAlloc_2321_, 4, v_traceState_2289_);
lean_ctor_set(v_reuseFailAlloc_2321_, 5, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2321_, 6, v_recordedDeps_2290_);
lean_ctor_set(v_reuseFailAlloc_2321_, 7, v_messages_2291_);
lean_ctor_set(v_reuseFailAlloc_2321_, 8, v_infoState_2292_);
lean_ctor_set(v_reuseFailAlloc_2321_, 9, v_snapshotTasks_2293_);
v___x_2302_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v_mctx_2305_; lean_object* v_zetaDeltaFVarIds_2306_; lean_object* v_postponed_2307_; lean_object* v_diag_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2319_; 
v___x_2303_ = lean_st_ref_put(v___y_2282_, v___x_2302_);
v___x_2304_ = lean_st_ref_take(v___y_2281_);
v_mctx_2305_ = lean_ctor_get(v___x_2304_, 0);
v_zetaDeltaFVarIds_2306_ = lean_ctor_get(v___x_2304_, 2);
v_postponed_2307_ = lean_ctor_get(v___x_2304_, 3);
v_diag_2308_ = lean_ctor_get(v___x_2304_, 4);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v___x_2304_, 1);
lean_dec(v_unused_2320_);
v___x_2310_ = v___x_2304_;
v_isShared_2311_ = v_isSharedCheck_2319_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_diag_2308_);
lean_inc(v_postponed_2307_);
lean_inc(v_zetaDeltaFVarIds_2306_);
lean_inc(v_mctx_2305_);
lean_dec(v___x_2304_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2319_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
v___x_2312_ = lean_box(0);
v___x_2313_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 1, v___x_2313_);
v___x_2315_ = v___x_2310_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_mctx_2305_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v_zetaDeltaFVarIds_2306_);
lean_ctor_set(v_reuseFailAlloc_2318_, 3, v_postponed_2307_);
lean_ctor_set(v_reuseFailAlloc_2318_, 4, v_diag_2308_);
v___x_2315_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = lean_st_ref_put(v___y_2281_, v___x_2315_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2312_);
return v___x_2317_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg___boxed(lean_object* v_declName_2324_, lean_object* v_s_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
uint8_t v_s_boxed_2329_; lean_object* v_res_2330_; 
v_s_boxed_2329_ = lean_unbox(v_s_2325_);
v_res_2330_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(v_declName_2324_, v_s_boxed_2329_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec(v___y_2326_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(lean_object* v_declName_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
uint8_t v___x_2337_; lean_object* v___x_2338_; 
v___x_2337_ = 0;
v___x_2338_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(v_declName_2331_, v___x_2337_, v___y_2333_, v___y_2335_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(lean_object* v_declName_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_declName_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v___y_2341_);
lean_dec_ref(v___y_2340_);
return v_res_2345_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__3(void){
_start:
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2349_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_2350_ = lean_unsigned_to_nat(58u);
v___x_2351_ = lean_unsigned_to_nat(33u);
v___x_2352_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2353_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2354_ = l_mkPanicMessageWithDecl(v___x_2353_, v___x_2352_, v___x_2351_, v___x_2350_, v___x_2349_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtorHet___closed__5(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2356_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_2357_ = lean_unsigned_to_nat(60u);
v___x_2358_ = lean_unsigned_to_nat(30u);
v___x_2359_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__1));
v___x_2360_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_2361_ = l_mkPanicMessageWithDecl(v___x_2360_, v___x_2359_, v___x_2358_, v___x_2357_, v___x_2356_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet(lean_object* v_declName_2362_, lean_object* v_indName_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v___x_2369_; 
lean_inc(v_indName_2363_);
v___x_2369_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2369_, 1);
if (lean_obj_tag(v_a_2370_) == 5)
{
lean_object* v_val_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2561_; 
v_val_2371_ = lean_ctor_get(v_a_2370_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v_a_2370_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2373_ = v_a_2370_;
v_isShared_2374_ = v_isSharedCheck_2561_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_val_2371_);
lean_dec(v_a_2370_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2561_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_inc(v_indName_2363_);
v___x_2375_ = l_Lean_mkCasesOnName(v_indName_2363_);
lean_inc(v___x_2375_);
v___x_2376_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_2375_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v_name_2378_; lean_object* v_levelParams_2379_; lean_object* v_type_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
lean_inc(v_a_2377_);
lean_dec_ref_known(v___x_2376_, 1);
v_name_2378_ = lean_ctor_get(v_a_2377_, 0);
lean_inc(v_name_2378_);
v_levelParams_2379_ = lean_ctor_get(v_a_2377_, 1);
lean_inc_n(v_levelParams_2379_, 2);
v_type_2380_ = lean_ctor_get(v_a_2377_, 2);
lean_inc_ref(v_type_2380_);
lean_dec(v_a_2377_);
v___x_2381_ = lean_box(0);
v___x_2382_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_2379_, v___x_2381_);
if (lean_obj_tag(v___x_2382_) == 1)
{
lean_object* v_head_2383_; lean_object* v_tail_2384_; lean_object* v_numParams_2385_; lean_object* v_numIndices_2386_; lean_object* v_ctors_2387_; lean_object* v___f_2388_; lean_object* v___x_2390_; 
v_head_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_head_2383_);
v_tail_2384_ = lean_ctor_get(v___x_2382_, 1);
lean_inc(v_tail_2384_);
v_numParams_2385_ = lean_ctor_get(v_val_2371_, 1);
lean_inc_n(v_numParams_2385_, 2);
v_numIndices_2386_ = lean_ctor_get(v_val_2371_, 2);
lean_inc(v_numIndices_2386_);
v_ctors_2387_ = lean_ctor_get(v_val_2371_, 4);
lean_inc(v_ctors_2387_);
v___f_2388_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__6___boxed), 17, 10);
lean_closure_set(v___f_2388_, 0, v_numIndices_2386_);
lean_closure_set(v___f_2388_, 1, v_head_2383_);
lean_closure_set(v___f_2388_, 2, v_ctors_2387_);
lean_closure_set(v___f_2388_, 3, v_indName_2363_);
lean_closure_set(v___f_2388_, 4, v_tail_2384_);
lean_closure_set(v___f_2388_, 5, v_name_2378_);
lean_closure_set(v___f_2388_, 6, v___x_2382_);
lean_closure_set(v___f_2388_, 7, v_numParams_2385_);
lean_closure_set(v___f_2388_, 8, v_val_2371_);
lean_closure_set(v___f_2388_, 9, v___x_2375_);
if (v_isShared_2374_ == 0)
{
lean_ctor_set_tag(v___x_2373_, 1);
lean_ctor_set(v___x_2373_, 0, v_numParams_2385_);
v___x_2390_ = v___x_2373_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_numParams_2385_);
v___x_2390_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
uint8_t v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = 0;
v___x_2392_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_2380_, v___x_2390_, v___f_2388_, v___x_2391_, v___x_2391_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___x_2394_; lean_object* v___f_2395_; uint8_t v___y_2397_; uint8_t v___x_2540_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2394_ = lean_box(v___x_2391_);
lean_inc(v_declName_2362_);
v___f_2395_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtorHet___lam__7___boxed), 9, 4);
lean_closure_set(v___f_2395_, 0, v_a_2393_);
lean_closure_set(v___f_2395_, 1, v_declName_2362_);
lean_closure_set(v___f_2395_, 2, v_levelParams_2379_);
lean_closure_set(v___f_2395_, 3, v___x_2394_);
v___x_2540_ = l_Lean_isPrivateName(v_declName_2362_);
if (v___x_2540_ == 0)
{
uint8_t v___x_2541_; 
v___x_2541_ = 1;
v___y_2397_ = v___x_2541_;
goto v___jp_2396_;
}
else
{
v___y_2397_ = v___x_2391_;
goto v___jp_2396_;
}
v___jp_2396_:
{
lean_object* v___x_2398_; 
v___x_2398_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_2395_, v___y_2397_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v___x_2399_; lean_object* v_env_2400_; lean_object* v_nextMacroScope_2401_; lean_object* v_ngen_2402_; lean_object* v_auxDeclNGen_2403_; lean_object* v_traceState_2404_; lean_object* v_recordedDeps_2405_; lean_object* v_messages_2406_; lean_object* v_infoState_2407_; lean_object* v_snapshotTasks_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref_known(v___x_2398_, 1);
v___x_2399_ = lean_st_ref_take(v_a_2367_);
v_env_2400_ = lean_ctor_get(v___x_2399_, 0);
v_nextMacroScope_2401_ = lean_ctor_get(v___x_2399_, 1);
v_ngen_2402_ = lean_ctor_get(v___x_2399_, 2);
v_auxDeclNGen_2403_ = lean_ctor_get(v___x_2399_, 3);
v_traceState_2404_ = lean_ctor_get(v___x_2399_, 4);
v_recordedDeps_2405_ = lean_ctor_get(v___x_2399_, 6);
v_messages_2406_ = lean_ctor_get(v___x_2399_, 7);
v_infoState_2407_ = lean_ctor_get(v___x_2399_, 8);
v_snapshotTasks_2408_ = lean_ctor_get(v___x_2399_, 9);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; 
v_unused_2539_ = lean_ctor_get(v___x_2399_, 5);
lean_dec(v_unused_2539_);
v___x_2410_ = v___x_2399_;
v_isShared_2411_ = v_isSharedCheck_2538_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_snapshotTasks_2408_);
lean_inc(v_infoState_2407_);
lean_inc(v_messages_2406_);
lean_inc(v_recordedDeps_2405_);
lean_inc(v_traceState_2404_);
lean_inc(v_auxDeclNGen_2403_);
lean_inc(v_ngen_2402_);
lean_inc(v_nextMacroScope_2401_);
lean_inc(v_env_2400_);
lean_dec(v___x_2399_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2538_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2415_; 
lean_inc(v_declName_2362_);
v___x_2412_ = l_Lean_Meta_markMatcherLike(v_env_2400_, v_declName_2362_);
v___x_2413_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 5, v___x_2413_);
lean_ctor_set(v___x_2410_, 0, v___x_2412_);
v___x_2415_ = v___x_2410_;
goto v_reusejp_2414_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_nextMacroScope_2401_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_ngen_2402_);
lean_ctor_set(v_reuseFailAlloc_2537_, 3, v_auxDeclNGen_2403_);
lean_ctor_set(v_reuseFailAlloc_2537_, 4, v_traceState_2404_);
lean_ctor_set(v_reuseFailAlloc_2537_, 5, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2537_, 6, v_recordedDeps_2405_);
lean_ctor_set(v_reuseFailAlloc_2537_, 7, v_messages_2406_);
lean_ctor_set(v_reuseFailAlloc_2537_, 8, v_infoState_2407_);
lean_ctor_set(v_reuseFailAlloc_2537_, 9, v_snapshotTasks_2408_);
v___x_2415_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2414_;
}
v_reusejp_2414_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v_mctx_2418_; lean_object* v_zetaDeltaFVarIds_2419_; lean_object* v_postponed_2420_; lean_object* v_diag_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2535_; 
v___x_2416_ = lean_st_ref_put(v_a_2367_, v___x_2415_);
v___x_2417_ = lean_st_ref_take(v_a_2365_);
v_mctx_2418_ = lean_ctor_get(v___x_2417_, 0);
v_zetaDeltaFVarIds_2419_ = lean_ctor_get(v___x_2417_, 2);
v_postponed_2420_ = lean_ctor_get(v___x_2417_, 3);
v_diag_2421_ = lean_ctor_get(v___x_2417_, 4);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2535_ == 0)
{
lean_object* v_unused_2536_; 
v_unused_2536_ = lean_ctor_get(v___x_2417_, 1);
lean_dec(v_unused_2536_);
v___x_2423_ = v___x_2417_;
v_isShared_2424_ = v_isSharedCheck_2535_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_diag_2421_);
lean_inc(v_postponed_2420_);
lean_inc(v_zetaDeltaFVarIds_2419_);
lean_inc(v_mctx_2418_);
lean_dec(v___x_2417_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2535_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2425_; lean_object* v___x_2427_; 
v___x_2425_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5);
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 1, v___x_2425_);
v___x_2427_ = v___x_2423_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_mctx_2418_);
lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_zetaDeltaFVarIds_2419_);
lean_ctor_set(v_reuseFailAlloc_2534_, 3, v_postponed_2420_);
lean_ctor_set(v_reuseFailAlloc_2534_, 4, v_diag_2421_);
v___x_2427_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v_env_2430_; lean_object* v_nextMacroScope_2431_; lean_object* v_ngen_2432_; lean_object* v_auxDeclNGen_2433_; lean_object* v_traceState_2434_; lean_object* v_recordedDeps_2435_; lean_object* v_messages_2436_; lean_object* v_infoState_2437_; lean_object* v_snapshotTasks_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2532_; 
v___x_2428_ = lean_st_ref_put(v_a_2365_, v___x_2427_);
v___x_2429_ = lean_st_ref_take(v_a_2367_);
v_env_2430_ = lean_ctor_get(v___x_2429_, 0);
v_nextMacroScope_2431_ = lean_ctor_get(v___x_2429_, 1);
v_ngen_2432_ = lean_ctor_get(v___x_2429_, 2);
v_auxDeclNGen_2433_ = lean_ctor_get(v___x_2429_, 3);
v_traceState_2434_ = lean_ctor_get(v___x_2429_, 4);
v_recordedDeps_2435_ = lean_ctor_get(v___x_2429_, 6);
v_messages_2436_ = lean_ctor_get(v___x_2429_, 7);
v_infoState_2437_ = lean_ctor_get(v___x_2429_, 8);
v_snapshotTasks_2438_ = lean_ctor_get(v___x_2429_, 9);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; 
v_unused_2533_ = lean_ctor_get(v___x_2429_, 5);
lean_dec(v_unused_2533_);
v___x_2440_ = v___x_2429_;
v_isShared_2441_ = v_isSharedCheck_2532_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_snapshotTasks_2438_);
lean_inc(v_infoState_2437_);
lean_inc(v_messages_2436_);
lean_inc(v_recordedDeps_2435_);
lean_inc(v_traceState_2434_);
lean_inc(v_auxDeclNGen_2433_);
lean_inc(v_ngen_2432_);
lean_inc(v_nextMacroScope_2431_);
lean_inc(v_env_2430_);
lean_dec(v___x_2429_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2532_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2442_; lean_object* v___x_2444_; 
lean_inc(v_declName_2362_);
v___x_2442_ = l_Lean_markAuxRecursor(v_env_2430_, v_declName_2362_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 5, v___x_2413_);
lean_ctor_set(v___x_2440_, 0, v___x_2442_);
v___x_2444_ = v___x_2440_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_nextMacroScope_2431_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v_ngen_2432_);
lean_ctor_set(v_reuseFailAlloc_2531_, 3, v_auxDeclNGen_2433_);
lean_ctor_set(v_reuseFailAlloc_2531_, 4, v_traceState_2434_);
lean_ctor_set(v_reuseFailAlloc_2531_, 5, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2531_, 6, v_recordedDeps_2435_);
lean_ctor_set(v_reuseFailAlloc_2531_, 7, v_messages_2436_);
lean_ctor_set(v_reuseFailAlloc_2531_, 8, v_infoState_2437_);
lean_ctor_set(v_reuseFailAlloc_2531_, 9, v_snapshotTasks_2438_);
v___x_2444_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_mctx_2447_; lean_object* v_zetaDeltaFVarIds_2448_; lean_object* v_postponed_2449_; lean_object* v_diag_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2529_; 
v___x_2445_ = lean_st_ref_put(v_a_2367_, v___x_2444_);
v___x_2446_ = lean_st_ref_take(v_a_2365_);
v_mctx_2447_ = lean_ctor_get(v___x_2446_, 0);
v_zetaDeltaFVarIds_2448_ = lean_ctor_get(v___x_2446_, 2);
v_postponed_2449_ = lean_ctor_get(v___x_2446_, 3);
v_diag_2450_ = lean_ctor_get(v___x_2446_, 4);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2529_ == 0)
{
lean_object* v_unused_2530_; 
v_unused_2530_ = lean_ctor_get(v___x_2446_, 1);
lean_dec(v_unused_2530_);
v___x_2452_ = v___x_2446_;
v_isShared_2453_ = v_isSharedCheck_2529_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_diag_2450_);
lean_inc(v_postponed_2449_);
lean_inc(v_zetaDeltaFVarIds_2448_);
lean_inc(v_mctx_2447_);
lean_dec(v___x_2446_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2529_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2425_);
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_mctx_2447_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v_zetaDeltaFVarIds_2448_);
lean_ctor_set(v_reuseFailAlloc_2528_, 3, v_postponed_2449_);
lean_ctor_set(v_reuseFailAlloc_2528_, 4, v_diag_2450_);
v___x_2455_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v_env_2458_; lean_object* v_nextMacroScope_2459_; lean_object* v_ngen_2460_; lean_object* v_auxDeclNGen_2461_; lean_object* v_traceState_2462_; lean_object* v_recordedDeps_2463_; lean_object* v_messages_2464_; lean_object* v_infoState_2465_; lean_object* v_snapshotTasks_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2526_; 
v___x_2456_ = lean_st_ref_put(v_a_2365_, v___x_2455_);
v___x_2457_ = lean_st_ref_take(v_a_2367_);
v_env_2458_ = lean_ctor_get(v___x_2457_, 0);
v_nextMacroScope_2459_ = lean_ctor_get(v___x_2457_, 1);
v_ngen_2460_ = lean_ctor_get(v___x_2457_, 2);
v_auxDeclNGen_2461_ = lean_ctor_get(v___x_2457_, 3);
v_traceState_2462_ = lean_ctor_get(v___x_2457_, 4);
v_recordedDeps_2463_ = lean_ctor_get(v___x_2457_, 6);
v_messages_2464_ = lean_ctor_get(v___x_2457_, 7);
v_infoState_2465_ = lean_ctor_get(v___x_2457_, 8);
v_snapshotTasks_2466_ = lean_ctor_get(v___x_2457_, 9);
v_isSharedCheck_2526_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2526_ == 0)
{
lean_object* v_unused_2527_; 
v_unused_2527_ = lean_ctor_get(v___x_2457_, 5);
lean_dec(v_unused_2527_);
v___x_2468_ = v___x_2457_;
v_isShared_2469_ = v_isSharedCheck_2526_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_snapshotTasks_2466_);
lean_inc(v_infoState_2465_);
lean_inc(v_messages_2464_);
lean_inc(v_recordedDeps_2463_);
lean_inc(v_traceState_2462_);
lean_inc(v_auxDeclNGen_2461_);
lean_inc(v_ngen_2460_);
lean_inc(v_nextMacroScope_2459_);
lean_inc(v_env_2458_);
lean_dec(v___x_2457_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2526_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_inc(v_declName_2362_);
v___x_2470_ = l_Lean_Meta_addToCompletionBlackList(v_env_2458_, v_declName_2362_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 5, v___x_2413_);
lean_ctor_set(v___x_2468_, 0, v___x_2470_);
v___x_2472_ = v___x_2468_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_nextMacroScope_2459_);
lean_ctor_set(v_reuseFailAlloc_2525_, 2, v_ngen_2460_);
lean_ctor_set(v_reuseFailAlloc_2525_, 3, v_auxDeclNGen_2461_);
lean_ctor_set(v_reuseFailAlloc_2525_, 4, v_traceState_2462_);
lean_ctor_set(v_reuseFailAlloc_2525_, 5, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2525_, 6, v_recordedDeps_2463_);
lean_ctor_set(v_reuseFailAlloc_2525_, 7, v_messages_2464_);
lean_ctor_set(v_reuseFailAlloc_2525_, 8, v_infoState_2465_);
lean_ctor_set(v_reuseFailAlloc_2525_, 9, v_snapshotTasks_2466_);
v___x_2472_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v_mctx_2475_; lean_object* v_zetaDeltaFVarIds_2476_; lean_object* v_postponed_2477_; lean_object* v_diag_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2523_; 
v___x_2473_ = lean_st_ref_put(v_a_2367_, v___x_2472_);
v___x_2474_ = lean_st_ref_take(v_a_2365_);
v_mctx_2475_ = lean_ctor_get(v___x_2474_, 0);
v_zetaDeltaFVarIds_2476_ = lean_ctor_get(v___x_2474_, 2);
v_postponed_2477_ = lean_ctor_get(v___x_2474_, 3);
v_diag_2478_ = lean_ctor_get(v___x_2474_, 4);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2474_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v___x_2474_, 1);
lean_dec(v_unused_2524_);
v___x_2480_ = v___x_2474_;
v_isShared_2481_ = v_isSharedCheck_2523_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_diag_2478_);
lean_inc(v_postponed_2477_);
lean_inc(v_zetaDeltaFVarIds_2476_);
lean_inc(v_mctx_2475_);
lean_dec(v___x_2474_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2523_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v___x_2425_);
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_mctx_2475_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_zetaDeltaFVarIds_2476_);
lean_ctor_set(v_reuseFailAlloc_2522_, 3, v_postponed_2477_);
lean_ctor_set(v_reuseFailAlloc_2522_, 4, v_diag_2478_);
v___x_2483_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v_env_2486_; lean_object* v_nextMacroScope_2487_; lean_object* v_ngen_2488_; lean_object* v_auxDeclNGen_2489_; lean_object* v_traceState_2490_; lean_object* v_recordedDeps_2491_; lean_object* v_messages_2492_; lean_object* v_infoState_2493_; lean_object* v_snapshotTasks_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2520_; 
v___x_2484_ = lean_st_ref_put(v_a_2365_, v___x_2483_);
v___x_2485_ = lean_st_ref_take(v_a_2367_);
v_env_2486_ = lean_ctor_get(v___x_2485_, 0);
v_nextMacroScope_2487_ = lean_ctor_get(v___x_2485_, 1);
v_ngen_2488_ = lean_ctor_get(v___x_2485_, 2);
v_auxDeclNGen_2489_ = lean_ctor_get(v___x_2485_, 3);
v_traceState_2490_ = lean_ctor_get(v___x_2485_, 4);
v_recordedDeps_2491_ = lean_ctor_get(v___x_2485_, 6);
v_messages_2492_ = lean_ctor_get(v___x_2485_, 7);
v_infoState_2493_ = lean_ctor_get(v___x_2485_, 8);
v_snapshotTasks_2494_ = lean_ctor_get(v___x_2485_, 9);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; 
v_unused_2521_ = lean_ctor_get(v___x_2485_, 5);
lean_dec(v_unused_2521_);
v___x_2496_ = v___x_2485_;
v_isShared_2497_ = v_isSharedCheck_2520_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_snapshotTasks_2494_);
lean_inc(v_infoState_2493_);
lean_inc(v_messages_2492_);
lean_inc(v_recordedDeps_2491_);
lean_inc(v_traceState_2490_);
lean_inc(v_auxDeclNGen_2489_);
lean_inc(v_ngen_2488_);
lean_inc(v_nextMacroScope_2487_);
lean_inc(v_env_2486_);
lean_dec(v___x_2485_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2520_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2498_; lean_object* v___x_2500_; 
lean_inc(v_declName_2362_);
v___x_2498_ = l_Lean_addProtected(v_env_2486_, v_declName_2362_);
if (v_isShared_2497_ == 0)
{
lean_ctor_set(v___x_2496_, 5, v___x_2413_);
lean_ctor_set(v___x_2496_, 0, v___x_2498_);
v___x_2500_ = v___x_2496_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2498_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_nextMacroScope_2487_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v_ngen_2488_);
lean_ctor_set(v_reuseFailAlloc_2519_, 3, v_auxDeclNGen_2489_);
lean_ctor_set(v_reuseFailAlloc_2519_, 4, v_traceState_2490_);
lean_ctor_set(v_reuseFailAlloc_2519_, 5, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2519_, 6, v_recordedDeps_2491_);
lean_ctor_set(v_reuseFailAlloc_2519_, 7, v_messages_2492_);
lean_ctor_set(v_reuseFailAlloc_2519_, 8, v_infoState_2493_);
lean_ctor_set(v_reuseFailAlloc_2519_, 9, v_snapshotTasks_2494_);
v___x_2500_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_mctx_2503_; lean_object* v_zetaDeltaFVarIds_2504_; lean_object* v_postponed_2505_; lean_object* v_diag_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2517_; 
v___x_2501_ = lean_st_ref_put(v_a_2367_, v___x_2500_);
v___x_2502_ = lean_st_ref_take(v_a_2365_);
v_mctx_2503_ = lean_ctor_get(v___x_2502_, 0);
v_zetaDeltaFVarIds_2504_ = lean_ctor_get(v___x_2502_, 2);
v_postponed_2505_ = lean_ctor_get(v___x_2502_, 3);
v_diag_2506_ = lean_ctor_get(v___x_2502_, 4);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; 
v_unused_2518_ = lean_ctor_get(v___x_2502_, 1);
lean_dec(v_unused_2518_);
v___x_2508_ = v___x_2502_;
v_isShared_2509_ = v_isSharedCheck_2517_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_diag_2506_);
lean_inc(v_postponed_2505_);
lean_inc(v_zetaDeltaFVarIds_2504_);
lean_inc(v_mctx_2503_);
lean_dec(v___x_2502_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2517_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
lean_ctor_set(v___x_2508_, 1, v___x_2425_);
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_mctx_2503_);
lean_ctor_set(v_reuseFailAlloc_2516_, 1, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2516_, 2, v_zetaDeltaFVarIds_2504_);
lean_ctor_set(v_reuseFailAlloc_2516_, 3, v_postponed_2505_);
lean_ctor_set(v_reuseFailAlloc_2516_, 4, v_diag_2506_);
v___x_2511_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = lean_st_ref_put(v_a_2365_, v___x_2511_);
v___x_2513_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_2362_);
v___x_2514_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(v___x_2513_, v_declName_2362_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v___x_2515_; 
lean_dec_ref_known(v___x_2514_, 1);
v___x_2515_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14(v_declName_2362_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
return v___x_2515_;
}
else
{
lean_dec(v_declName_2362_);
return v___x_2514_;
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
lean_dec(v_declName_2362_);
return v___x_2398_;
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec(v_levelParams_2379_);
lean_dec(v_declName_2362_);
v_a_2542_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2392_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2392_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_dec(v___x_2382_);
lean_dec_ref(v_type_2380_);
lean_dec(v_levelParams_2379_);
lean_dec(v_name_2378_);
lean_dec(v___x_2375_);
lean_del_object(v___x_2373_);
lean_dec_ref(v_val_2371_);
lean_dec(v_indName_2363_);
lean_dec(v_declName_2362_);
v___x_2551_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__3, &l_Lean_mkCasesOnSameCtorHet___closed__3_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__3);
v___x_2552_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_2551_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
return v___x_2552_;
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v___x_2375_);
lean_del_object(v___x_2373_);
lean_dec_ref(v_val_2371_);
lean_dec(v_indName_2363_);
lean_dec(v_declName_2362_);
v_a_2553_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2376_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2376_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_dec(v_a_2370_);
lean_dec(v_indName_2363_);
lean_dec(v_declName_2362_);
v___x_2562_ = lean_obj_once(&l_Lean_mkCasesOnSameCtorHet___closed__5, &l_Lean_mkCasesOnSameCtorHet___closed__5_once, _init_l_Lean_mkCasesOnSameCtorHet___closed__5);
v___x_2563_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_2562_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
return v___x_2563_;
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec(v_indName_2363_);
lean_dec(v_declName_2362_);
v_a_2564_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2369_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2369_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtorHet___boxed(lean_object* v_declName_2572_, lean_object* v_indName_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_){
_start:
{
lean_object* v_res_2579_; 
v_res_2579_ = l_Lean_mkCasesOnSameCtorHet(v_declName_2572_, v_indName_2573_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_);
lean_dec(v_a_2577_);
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(lean_object* v_00_u03b1_2580_, lean_object* v_name_2581_, lean_object* v_type_2582_, lean_object* v_k_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v_name_2581_, v_type_2582_, v_k_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(lean_object* v_00_u03b1_2590_, lean_object* v_name_2591_, lean_object* v_type_2592_, lean_object* v_k_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(v_00_u03b1_2590_, v_name_2591_, v_type_2592_, v_k_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(lean_object* v_tail_2600_, lean_object* v_params_2601_, lean_object* v_alts_2602_, lean_object* v___x_2603_, lean_object* v_ism2_2604_, lean_object* v_motive_2605_, lean_object* v_val_2606_, lean_object* v_indName_2607_, lean_object* v___x_2608_, lean_object* v___x_2609_, lean_object* v___x_2610_, lean_object* v_as_2611_, size_t v_sz_2612_, size_t v_i_2613_, lean_object* v_bs_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_2600_, v_params_2601_, v_alts_2602_, v___x_2603_, v_ism2_2604_, v_motive_2605_, v_val_2606_, v_indName_2607_, v___x_2608_, v___x_2609_, v___x_2610_, v_sz_2612_, v_i_2613_, v_bs_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(lean_object** _args){
lean_object* v_tail_2621_ = _args[0];
lean_object* v_params_2622_ = _args[1];
lean_object* v_alts_2623_ = _args[2];
lean_object* v___x_2624_ = _args[3];
lean_object* v_ism2_2625_ = _args[4];
lean_object* v_motive_2626_ = _args[5];
lean_object* v_val_2627_ = _args[6];
lean_object* v_indName_2628_ = _args[7];
lean_object* v___x_2629_ = _args[8];
lean_object* v___x_2630_ = _args[9];
lean_object* v___x_2631_ = _args[10];
lean_object* v_as_2632_ = _args[11];
lean_object* v_sz_2633_ = _args[12];
lean_object* v_i_2634_ = _args[13];
lean_object* v_bs_2635_ = _args[14];
lean_object* v___y_2636_ = _args[15];
lean_object* v___y_2637_ = _args[16];
lean_object* v___y_2638_ = _args[17];
lean_object* v___y_2639_ = _args[18];
lean_object* v___y_2640_ = _args[19];
_start:
{
size_t v_sz_boxed_2641_; size_t v_i_boxed_2642_; lean_object* v_res_2643_; 
v_sz_boxed_2641_ = lean_unbox_usize(v_sz_2633_);
lean_dec(v_sz_2633_);
v_i_boxed_2642_ = lean_unbox_usize(v_i_2634_);
lean_dec(v_i_2634_);
v_res_2643_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(v_tail_2621_, v_params_2622_, v_alts_2623_, v___x_2624_, v_ism2_2625_, v_motive_2626_, v_val_2627_, v_indName_2628_, v___x_2629_, v___x_2630_, v___x_2631_, v_as_2632_, v_sz_boxed_2641_, v_i_boxed_2642_, v_bs_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec(v___y_2639_);
lean_dec_ref(v___y_2638_);
lean_dec(v___y_2637_);
lean_dec_ref(v___y_2636_);
lean_dec_ref(v_as_2632_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(lean_object* v_tail_2644_, lean_object* v_params_2645_, lean_object* v___x_2646_, lean_object* v_motive_2647_, lean_object* v_as_2648_, size_t v_sz_2649_, size_t v_i_2650_, lean_object* v_bs_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(v_tail_2644_, v_params_2645_, v___x_2646_, v_motive_2647_, v_sz_2649_, v_i_2650_, v_bs_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(lean_object* v_tail_2658_, lean_object* v_params_2659_, lean_object* v___x_2660_, lean_object* v_motive_2661_, lean_object* v_as_2662_, lean_object* v_sz_2663_, lean_object* v_i_2664_, lean_object* v_bs_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
size_t v_sz_boxed_2671_; size_t v_i_boxed_2672_; lean_object* v_res_2673_; 
v_sz_boxed_2671_ = lean_unbox_usize(v_sz_2663_);
lean_dec(v_sz_2663_);
v_i_boxed_2672_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_res_2673_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(v_tail_2658_, v_params_2659_, v___x_2660_, v_motive_2661_, v_as_2662_, v_sz_boxed_2671_, v_i_boxed_2672_, v_bs_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec_ref(v_as_2662_);
lean_dec_ref(v_params_2659_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(lean_object* v_00_u03b1_2674_, lean_object* v_x_2675_, uint8_t v_isExporting_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v_x_2675_, v_isExporting_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(lean_object* v_00_u03b1_2683_, lean_object* v_x_2684_, lean_object* v_isExporting_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v_isExporting_boxed_2691_; lean_object* v_res_2692_; 
v_isExporting_boxed_2691_ = lean_unbox(v_isExporting_2685_);
v_res_2692_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(v_00_u03b1_2683_, v_x_2684_, v_isExporting_boxed_2691_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(lean_object* v_00_u03b2_2693_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg(){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg___boxed(lean_object* v___dummy_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12___redArg();
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_mkCasesOnSameCtorHet_spec__12(lean_object* v_00_u03b2_2699_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(lean_object* v_00_u03b1_2701_, lean_object* v_constName_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2709_, lean_object* v_constName_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_2709_, v_constName_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17(lean_object* v_00_u03b1_2717_, lean_object* v_attrName_2718_, lean_object* v_declName_2719_, lean_object* v_asyncPrefix_x3f_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___redArg(v_attrName_2718_, v_declName_2719_, v_asyncPrefix_x3f_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17___boxed(lean_object* v_00_u03b1_2727_, lean_object* v_attrName_2728_, lean_object* v_declName_2729_, lean_object* v_asyncPrefix_x3f_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17(v_00_u03b1_2727_, v_attrName_2728_, v_declName_2729_, v_asyncPrefix_x3f_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(lean_object* v_00_u03b1_2737_, lean_object* v_attrName_2738_, lean_object* v_declName_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_attrName_2738_, v_declName_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(lean_object* v_00_u03b1_2746_, lean_object* v_attrName_2747_, lean_object* v_declName_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_00_u03b1_2746_, v_attrName_2747_, v_declName_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
lean_dec(v___y_2750_);
lean_dec_ref(v___y_2749_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20(lean_object* v_declName_2755_, uint8_t v_s_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___redArg(v_declName_2755_, v_s_2756_, v___y_2758_, v___y_2760_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20___boxed(lean_object* v_declName_2763_, lean_object* v_s_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
uint8_t v_s_boxed_2770_; lean_object* v_res_2771_; 
v_s_boxed_2770_ = lean_unbox(v_s_2764_);
v_res_2771_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__14_spec__20(v_declName_2763_, v_s_boxed_2770_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec_ref(v___y_2765_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6(lean_object* v_00_u03b1_2772_, lean_object* v_ref_2773_, lean_object* v_constName_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___redArg(v_ref_2773_, v_constName_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6___boxed(lean_object* v_00_u03b1_2781_, lean_object* v_ref_2782_, lean_object* v_constName_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6(v_00_u03b1_2781_, v_ref_2782_, v_constName_2783_, v___y_2784_, v___y_2785_, v___y_2786_, v___y_2787_);
lean_dec(v___y_2787_);
lean_dec_ref(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v___y_2784_);
lean_dec(v_ref_2782_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22(lean_object* v_00_u03b1_2790_, lean_object* v_msg_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v_msg_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___boxed(lean_object* v_00_u03b1_2798_, lean_object* v_msg_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22(v_00_u03b1_2798_, v_msg_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
return v_res_2805_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18(lean_object* v_00_u03b1_2806_, lean_object* v_ref_2807_, lean_object* v_msg_2808_, lean_object* v_declHint_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___redArg(v_ref_2807_, v_msg_2808_, v_declHint_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18___boxed(lean_object* v_00_u03b1_2816_, lean_object* v_ref_2817_, lean_object* v_msg_2818_, lean_object* v_declHint_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18(v_00_u03b1_2816_, v_ref_2817_, v_msg_2818_, v_declHint_2819_, v___y_2820_, v___y_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v_ref_2817_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29(lean_object* v_msg_2826_, lean_object* v_declHint_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___redArg(v_msg_2826_, v_declHint_2827_, v___y_2831_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29___boxed(lean_object* v_msg_2834_, lean_object* v_declHint_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__24_spec__29(v_msg_2834_, v_declHint_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25(lean_object* v_00_u03b1_2842_, lean_object* v_ref_2843_, lean_object* v_msg_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; 
v___x_2850_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___redArg(v_ref_2843_, v_msg_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25___boxed(lean_object* v_00_u03b1_2851_, lean_object* v_ref_2852_, lean_object* v_msg_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__6_spec__18_spec__25(v_00_u03b1_2851_, v_ref_2852_, v_msg_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v_ref_2852_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(lean_object* v_e_2860_, lean_object* v___y_2861_){
_start:
{
uint8_t v___x_2863_; 
v___x_2863_ = l_Lean_Expr_hasMVar(v_e_2860_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; 
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_e_2860_);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; lean_object* v_mctx_2866_; lean_object* v___x_2867_; lean_object* v_fst_2868_; lean_object* v_snd_2869_; lean_object* v___x_2870_; lean_object* v_cache_2871_; lean_object* v_zetaDeltaFVarIds_2872_; lean_object* v_postponed_2873_; lean_object* v_diag_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2883_; 
v___x_2865_ = lean_st_ref_get(v___y_2861_);
v_mctx_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc_ref(v_mctx_2866_);
lean_dec(v___x_2865_);
v___x_2867_ = l_Lean_instantiateMVarsCore(v_mctx_2866_, v_e_2860_);
v_fst_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_fst_2868_);
v_snd_2869_ = lean_ctor_get(v___x_2867_, 1);
lean_inc(v_snd_2869_);
lean_dec_ref(v___x_2867_);
v___x_2870_ = lean_st_ref_take(v___y_2861_);
v_cache_2871_ = lean_ctor_get(v___x_2870_, 1);
v_zetaDeltaFVarIds_2872_ = lean_ctor_get(v___x_2870_, 2);
v_postponed_2873_ = lean_ctor_get(v___x_2870_, 3);
v_diag_2874_ = lean_ctor_get(v___x_2870_, 4);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; 
v_unused_2884_ = lean_ctor_get(v___x_2870_, 0);
lean_dec(v_unused_2884_);
v___x_2876_ = v___x_2870_;
v_isShared_2877_ = v_isSharedCheck_2883_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_diag_2874_);
lean_inc(v_postponed_2873_);
lean_inc(v_zetaDeltaFVarIds_2872_);
lean_inc(v_cache_2871_);
lean_dec(v___x_2870_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2883_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
lean_ctor_set(v___x_2876_, 0, v_snd_2869_);
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_snd_2869_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_cache_2871_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_zetaDeltaFVarIds_2872_);
lean_ctor_set(v_reuseFailAlloc_2882_, 3, v_postponed_2873_);
lean_ctor_set(v_reuseFailAlloc_2882_, 4, v_diag_2874_);
v___x_2879_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
v___x_2880_ = lean_st_ref_put(v___y_2861_, v___x_2879_);
v___x_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2881_, 0, v_fst_2868_);
return v___x_2881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(lean_object* v_e_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2885_, v___y_2886_);
lean_dec(v___y_2886_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(lean_object* v_e_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_e_2889_, v___y_2891_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(lean_object* v_e_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(v_e_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0(lean_object* v_motive_2903_, lean_object* v___x_2904_, lean_object* v_newEqs1_2905_, uint8_t v___x_2906_, uint8_t v___x_2907_, uint8_t v___x_2908_, lean_object* v_ism1_x27_2909_, lean_object* v_ism2_x27_2910_, lean_object* v_newRefls1_2911_, lean_object* v_newEqs2_2912_, lean_object* v_newRefls2_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2919_ = l_Lean_mkAppN(v_motive_2903_, v___x_2904_);
v___x_2920_ = l_Array_append___redArg(v_newEqs1_2905_, v_newEqs2_2912_);
v___x_2921_ = l_Lean_Meta_mkForallFVars(v___x_2920_, v___x_2919_, v___x_2906_, v___x_2907_, v___x_2907_, v___x_2908_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec_ref(v___x_2920_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref_known(v___x_2921_, 1);
v___x_2923_ = l_Array_append___redArg(v_ism1_x27_2909_, v_ism2_x27_2910_);
v___x_2924_ = l_Lean_Meta_mkLambdaFVars(v___x_2923_, v_a_2922_, v___x_2906_, v___x_2907_, v___x_2906_, v___x_2907_, v___x_2908_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec_ref(v___x_2923_);
if (lean_obj_tag(v___x_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2934_; 
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2934_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2934_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2929_ = l_Array_append___redArg(v_newRefls1_2911_, v_newRefls2_2913_);
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v_a_2925_);
lean_ctor_set(v___x_2930_, 1, v___x_2929_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 0, v___x_2930_);
v___x_2932_ = v___x_2927_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2930_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec_ref(v_newRefls1_2911_);
v_a_2935_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2924_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2924_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v_newRefls1_2911_);
lean_dec_ref(v_ism1_x27_2909_);
v_a_2943_ = lean_ctor_get(v___x_2921_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2921_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2921_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2921_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__0___boxed(lean_object* v_motive_2951_, lean_object* v___x_2952_, lean_object* v_newEqs1_2953_, lean_object* v___x_2954_, lean_object* v___x_2955_, lean_object* v___x_2956_, lean_object* v_ism1_x27_2957_, lean_object* v_ism2_x27_2958_, lean_object* v_newRefls1_2959_, lean_object* v_newEqs2_2960_, lean_object* v_newRefls2_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
uint8_t v___x_14921__boxed_2967_; uint8_t v___x_14922__boxed_2968_; uint8_t v___x_14923__boxed_2969_; lean_object* v_res_2970_; 
v___x_14921__boxed_2967_ = lean_unbox(v___x_2954_);
v___x_14922__boxed_2968_ = lean_unbox(v___x_2955_);
v___x_14923__boxed_2969_ = lean_unbox(v___x_2956_);
v_res_2970_ = l_Lean_mkCasesOnSameCtor___lam__0(v_motive_2951_, v___x_2952_, v_newEqs1_2953_, v___x_14921__boxed_2967_, v___x_14922__boxed_2968_, v___x_14923__boxed_2969_, v_ism1_x27_2957_, v_ism2_x27_2958_, v_newRefls1_2959_, v_newEqs2_2960_, v_newRefls2_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec_ref(v_newRefls2_2961_);
lean_dec_ref(v_newEqs2_2960_);
lean_dec_ref(v_ism2_x27_2958_);
lean_dec_ref(v___x_2952_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1(lean_object* v_motive_2971_, lean_object* v___x_2972_, uint8_t v___x_2973_, uint8_t v___x_2974_, uint8_t v___x_2975_, lean_object* v_ism1_x27_2976_, lean_object* v_ism2_x27_2977_, lean_object* v_is_2978_, lean_object* v___x_2979_, lean_object* v_newEqs1_2980_, lean_object* v_newRefls1_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___f_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2987_ = lean_box(v___x_2973_);
v___x_2988_ = lean_box(v___x_2974_);
v___x_2989_ = lean_box(v___x_2975_);
lean_inc_ref(v_ism2_x27_2977_);
v___f_2990_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__0___boxed), 16, 9);
lean_closure_set(v___f_2990_, 0, v_motive_2971_);
lean_closure_set(v___f_2990_, 1, v___x_2972_);
lean_closure_set(v___f_2990_, 2, v_newEqs1_2980_);
lean_closure_set(v___f_2990_, 3, v___x_2987_);
lean_closure_set(v___f_2990_, 4, v___x_2988_);
lean_closure_set(v___f_2990_, 5, v___x_2989_);
lean_closure_set(v___f_2990_, 6, v_ism1_x27_2976_);
lean_closure_set(v___f_2990_, 7, v_ism2_x27_2977_);
lean_closure_set(v___f_2990_, 8, v_newRefls1_2981_);
v___x_2991_ = lean_array_push(v_is_2978_, v___x_2979_);
v___x_2992_ = l_Lean_Meta_withNewEqs___redArg(v___x_2991_, v_ism2_x27_2977_, v___f_2990_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__1___boxed(lean_object* v_motive_2993_, lean_object* v___x_2994_, lean_object* v___x_2995_, lean_object* v___x_2996_, lean_object* v___x_2997_, lean_object* v_ism1_x27_2998_, lean_object* v_ism2_x27_2999_, lean_object* v_is_3000_, lean_object* v___x_3001_, lean_object* v_newEqs1_3002_, lean_object* v_newRefls1_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_){
_start:
{
uint8_t v___x_15012__boxed_3009_; uint8_t v___x_15013__boxed_3010_; uint8_t v___x_15014__boxed_3011_; lean_object* v_res_3012_; 
v___x_15012__boxed_3009_ = lean_unbox(v___x_2995_);
v___x_15013__boxed_3010_ = lean_unbox(v___x_2996_);
v___x_15014__boxed_3011_ = lean_unbox(v___x_2997_);
v_res_3012_ = l_Lean_mkCasesOnSameCtor___lam__1(v_motive_2993_, v___x_2994_, v___x_15012__boxed_3009_, v___x_15013__boxed_3010_, v___x_15014__boxed_3011_, v_ism1_x27_2998_, v_ism2_x27_2999_, v_is_3000_, v___x_3001_, v_newEqs1_3002_, v_newRefls1_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_);
lean_dec(v___y_3007_);
lean_dec_ref(v___y_3006_);
lean_dec(v___y_3005_);
lean_dec_ref(v___y_3004_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2(lean_object* v___x_3013_, uint8_t v___x_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Lean_addDecl(v___x_3013_, v___x_3014_, v___y_3017_, v___y_3018_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__2___boxed(lean_object* v___x_3021_, lean_object* v___x_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
uint8_t v___x_15054__boxed_3028_; lean_object* v_res_3029_; 
v___x_15054__boxed_3028_ = lean_unbox(v___x_3022_);
v_res_3029_ = l_Lean_mkCasesOnSameCtor___lam__2(v___x_3021_, v___x_15054__boxed_3028_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(lean_object* v_matcherName_3030_, lean_object* v_info_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_){
_start:
{
lean_object* v___x_3035_; lean_object* v_env_3036_; lean_object* v_nextMacroScope_3037_; lean_object* v_ngen_3038_; lean_object* v_auxDeclNGen_3039_; lean_object* v_traceState_3040_; lean_object* v_recordedDeps_3041_; lean_object* v_messages_3042_; lean_object* v_infoState_3043_; lean_object* v_snapshotTasks_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3071_; 
v___x_3035_ = lean_st_ref_take(v___y_3033_);
v_env_3036_ = lean_ctor_get(v___x_3035_, 0);
v_nextMacroScope_3037_ = lean_ctor_get(v___x_3035_, 1);
v_ngen_3038_ = lean_ctor_get(v___x_3035_, 2);
v_auxDeclNGen_3039_ = lean_ctor_get(v___x_3035_, 3);
v_traceState_3040_ = lean_ctor_get(v___x_3035_, 4);
v_recordedDeps_3041_ = lean_ctor_get(v___x_3035_, 6);
v_messages_3042_ = lean_ctor_get(v___x_3035_, 7);
v_infoState_3043_ = lean_ctor_get(v___x_3035_, 8);
v_snapshotTasks_3044_ = lean_ctor_get(v___x_3035_, 9);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3071_ == 0)
{
lean_object* v_unused_3072_; 
v_unused_3072_ = lean_ctor_get(v___x_3035_, 5);
lean_dec(v_unused_3072_);
v___x_3046_ = v___x_3035_;
v_isShared_3047_ = v_isSharedCheck_3071_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_snapshotTasks_3044_);
lean_inc(v_infoState_3043_);
lean_inc(v_messages_3042_);
lean_inc(v_recordedDeps_3041_);
lean_inc(v_traceState_3040_);
lean_inc(v_auxDeclNGen_3039_);
lean_inc(v_ngen_3038_);
lean_inc(v_nextMacroScope_3037_);
lean_inc(v_env_3036_);
lean_dec(v___x_3035_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3071_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3051_; 
v___x_3048_ = l_Lean_Meta_Match_Extension_addMatcherInfo(v_env_3036_, v_matcherName_3030_, v_info_3031_);
v___x_3049_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
if (v_isShared_3047_ == 0)
{
lean_ctor_set(v___x_3046_, 5, v___x_3049_);
lean_ctor_set(v___x_3046_, 0, v___x_3048_);
v___x_3051_ = v___x_3046_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3070_, 1, v_nextMacroScope_3037_);
lean_ctor_set(v_reuseFailAlloc_3070_, 2, v_ngen_3038_);
lean_ctor_set(v_reuseFailAlloc_3070_, 3, v_auxDeclNGen_3039_);
lean_ctor_set(v_reuseFailAlloc_3070_, 4, v_traceState_3040_);
lean_ctor_set(v_reuseFailAlloc_3070_, 5, v___x_3049_);
lean_ctor_set(v_reuseFailAlloc_3070_, 6, v_recordedDeps_3041_);
lean_ctor_set(v_reuseFailAlloc_3070_, 7, v_messages_3042_);
lean_ctor_set(v_reuseFailAlloc_3070_, 8, v_infoState_3043_);
lean_ctor_set(v_reuseFailAlloc_3070_, 9, v_snapshotTasks_3044_);
v___x_3051_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v_mctx_3054_; lean_object* v_zetaDeltaFVarIds_3055_; lean_object* v_postponed_3056_; lean_object* v_diag_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3068_; 
v___x_3052_ = lean_st_ref_put(v___y_3033_, v___x_3051_);
v___x_3053_ = lean_st_ref_take(v___y_3032_);
v_mctx_3054_ = lean_ctor_get(v___x_3053_, 0);
v_zetaDeltaFVarIds_3055_ = lean_ctor_get(v___x_3053_, 2);
v_postponed_3056_ = lean_ctor_get(v___x_3053_, 3);
v_diag_3057_ = lean_ctor_get(v___x_3053_, 4);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3068_ == 0)
{
lean_object* v_unused_3069_; 
v_unused_3069_ = lean_ctor_get(v___x_3053_, 1);
lean_dec(v_unused_3069_);
v___x_3059_ = v___x_3053_;
v_isShared_3060_ = v_isSharedCheck_3068_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_diag_3057_);
lean_inc(v_postponed_3056_);
lean_inc(v_zetaDeltaFVarIds_3055_);
lean_inc(v_mctx_3054_);
lean_dec(v___x_3053_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3068_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3061_ = lean_box(0);
v___x_3062_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5, &l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5_once, _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__5);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 1, v___x_3062_);
v___x_3064_ = v___x_3059_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_mctx_3054_);
lean_ctor_set(v_reuseFailAlloc_3067_, 1, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3067_, 2, v_zetaDeltaFVarIds_3055_);
lean_ctor_set(v_reuseFailAlloc_3067_, 3, v_postponed_3056_);
lean_ctor_set(v_reuseFailAlloc_3067_, 4, v_diag_3057_);
v___x_3064_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = lean_st_ref_put(v___y_3032_, v___x_3064_);
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3061_);
return v___x_3066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(lean_object* v_matcherName_3073_, lean_object* v_info_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_3073_, v_info_3074_, v___y_3075_, v___y_3076_);
lean_dec(v___y_3076_);
lean_dec(v___y_3075_);
return v_res_3078_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0));
v___x_3081_ = l_Lean_stringToMessageData(v___x_3080_);
return v___x_3081_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2));
v___x_3084_ = l_Lean_stringToMessageData(v___x_3083_);
return v___x_3084_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v___x_3090_ = lean_box(0);
v___x_3091_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6));
v___x_3092_ = l_Lean_mkConst(v___x_3091_, v___x_3090_);
return v___x_3092_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8));
v___x_3095_ = l_Lean_stringToMessageData(v___x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(lean_object* v___x_3096_, lean_object* v_a_3097_, lean_object* v___x_3098_, lean_object* v_zs1_3099_, lean_object* v_snd_3100_, uint8_t v___x_3101_, uint8_t v___x_3102_, uint8_t v___x_3103_, lean_object* v_alts_3104_, lean_object* v_zs2_3105_, lean_object* v___ctorRet2_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = lean_array_get_borrowed(v___x_3096_, v_a_3097_, v___x_3098_);
lean_inc_ref(v_zs1_3099_);
v___x_3113_ = l_Array_append___redArg(v_zs1_3099_, v_zs2_3105_);
lean_inc(v___x_3112_);
v___x_3114_ = l_Lean_Meta_instantiateForall(v___x_3112_, v___x_3113_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
v___x_3116_ = lean_box(0);
v___x_3117_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_3115_, v___x_3116_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3119_ = l_Lean_Expr_mvarId_x21(v_a_3118_);
v___x_3120_ = lean_array_get_size(v_snd_3100_);
v___x_3121_ = lean_box(0);
v___x_3122_ = lean_box(0);
lean_inc_ref(v___y_3109_);
v___x_3123_ = l_Lean_Meta_Cases_unifyEqs_x3f(v___x_3120_, v___x_3119_, v___x_3121_, v___x_3122_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_a_3124_);
lean_dec_ref_known(v___x_3123_, 1);
if (lean_obj_tag(v_a_3124_) == 1)
{
lean_object* v_val_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3172_; 
v_val_3125_ = lean_ctor_get(v_a_3124_, 0);
v_isSharedCheck_3172_ = !lean_is_exclusive(v_a_3124_);
if (v_isSharedCheck_3172_ == 0)
{
v___x_3127_ = v_a_3124_;
v_isShared_3128_ = v_isSharedCheck_3172_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_val_3125_);
lean_dec(v_a_3124_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3172_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v_fst_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3170_; 
v_fst_3129_ = lean_ctor_get(v_val_3125_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_val_3125_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v_val_3125_, 1);
lean_dec(v_unused_3171_);
v___x_3131_ = v_val_3125_;
v_isShared_3132_ = v_isSharedCheck_3170_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_fst_3129_);
lean_dec(v_val_3125_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3170_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___y_3134_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3162_ = lean_array_get_borrowed(v___x_3096_, v_alts_3104_, v___x_3098_);
v___x_3163_ = lean_array_get_size(v_zs1_3099_);
lean_dec_ref(v_zs1_3099_);
v___x_3164_ = lean_unsigned_to_nat(0u);
v___x_3165_ = lean_nat_dec_eq(v___x_3163_, v___x_3164_);
if (v___x_3165_ == 0)
{
lean_inc(v___x_3162_);
v___y_3134_ = v___x_3162_;
goto v___jp_3133_;
}
else
{
lean_object* v___x_3166_; uint8_t v___x_3167_; 
v___x_3166_ = lean_array_get_size(v_zs2_3105_);
v___x_3167_ = lean_nat_dec_eq(v___x_3166_, v___x_3164_);
if (v___x_3167_ == 0)
{
lean_inc(v___x_3162_);
v___y_3134_ = v___x_3162_;
goto v___jp_3133_;
}
else
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
lean_inc(v___x_3162_);
v___x_3169_ = l_Lean_Expr_app___override(v___x_3162_, v___x_3168_);
v___y_3134_ = v___x_3169_;
goto v___jp_3133_;
}
}
v___jp_3133_:
{
uint8_t v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___x_3135_ = 0;
v___x_3136_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_3136_, 0, v___x_3135_);
lean_ctor_set_uint8(v___x_3136_, 1, v___x_3101_);
lean_ctor_set_uint8(v___x_3136_, 2, v___x_3102_);
lean_ctor_set_uint8(v___x_3136_, 3, v___x_3101_);
lean_inc_ref(v___y_3134_);
lean_inc(v_fst_3129_);
v___x_3137_ = l_Lean_MVarId_apply(v_fst_3129_, v___y_3134_, v___x_3136_, v___x_3122_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
lean_inc(v_a_3138_);
lean_dec_ref_known(v___x_3137_, 1);
if (lean_obj_tag(v_a_3138_) == 0)
{
lean_object* v___x_3139_; 
lean_dec_ref(v___y_3134_);
lean_del_object(v___x_3131_);
lean_dec(v_fst_3129_);
lean_del_object(v___x_3127_);
v___x_3139_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_3118_, v___y_3108_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___x_3139_, 1);
v___x_3141_ = l_Lean_Meta_mkLambdaFVars(v___x_3113_, v_a_3140_, v___x_3102_, v___x_3101_, v___x_3102_, v___x_3101_, v___x_3103_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
lean_dec_ref(v___x_3113_);
return v___x_3141_;
}
else
{
lean_dec_ref(v___x_3113_);
return v___x_3139_;
}
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
lean_dec(v_a_3138_);
lean_dec(v_a_3118_);
lean_dec_ref(v___x_3113_);
v___x_3142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
v___x_3143_ = l_Lean_MessageData_ofExpr(v___y_3134_);
if (v_isShared_3132_ == 0)
{
lean_ctor_set_tag(v___x_3131_, 7);
lean_ctor_set(v___x_3131_, 1, v___x_3143_);
lean_ctor_set(v___x_3131_, 0, v___x_3142_);
v___x_3145_ = v___x_3131_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3142_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v___x_3143_);
v___x_3145_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3146_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
v___x_3147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3145_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 0, v_fst_3129_);
v___x_3149_ = v___x_3127_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_fst_3129_);
v___x_3149_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3147_);
lean_ctor_set(v___x_3150_, 1, v___x_3149_);
v___x_3151_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_3150_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
return v___x_3151_;
}
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec_ref(v___y_3134_);
lean_del_object(v___x_3131_);
lean_dec(v_fst_3129_);
lean_del_object(v___x_3127_);
lean_dec(v_a_3118_);
lean_dec_ref(v___x_3113_);
v_a_3154_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3137_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3137_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec(v_a_3124_);
lean_dec(v_a_3118_);
lean_dec_ref(v___x_3113_);
lean_dec_ref(v_zs1_3099_);
v___x_3173_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
v___x_3174_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__17_spec__22___redArg(v___x_3173_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_);
return v___x_3174_;
}
}
else
{
lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3182_; 
lean_dec(v_a_3118_);
lean_dec_ref(v___x_3113_);
lean_dec_ref(v_zs1_3099_);
v_a_3175_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3177_ = v___x_3123_;
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3123_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3182_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3180_; 
if (v_isShared_3178_ == 0)
{
v___x_3180_ = v___x_3177_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3181_; 
v_reuseFailAlloc_3181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3181_, 0, v_a_3175_);
v___x_3180_ = v_reuseFailAlloc_3181_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
return v___x_3180_;
}
}
}
}
else
{
lean_dec_ref(v___x_3113_);
lean_dec_ref(v_zs1_3099_);
return v___x_3117_;
}
}
else
{
lean_dec_ref(v___x_3113_);
lean_dec_ref(v_zs1_3099_);
return v___x_3114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(lean_object* v___x_3183_, lean_object* v_a_3184_, lean_object* v___x_3185_, lean_object* v_zs1_3186_, lean_object* v_snd_3187_, lean_object* v___x_3188_, lean_object* v___x_3189_, lean_object* v___x_3190_, lean_object* v_alts_3191_, lean_object* v_zs2_3192_, lean_object* v___ctorRet2_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
uint8_t v___x_15201__boxed_3199_; uint8_t v___x_15202__boxed_3200_; uint8_t v___x_15203__boxed_3201_; lean_object* v_res_3202_; 
v___x_15201__boxed_3199_ = lean_unbox(v___x_3188_);
v___x_15202__boxed_3200_ = lean_unbox(v___x_3189_);
v___x_15203__boxed_3201_ = lean_unbox(v___x_3190_);
v_res_3202_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(v___x_3183_, v_a_3184_, v___x_3185_, v_zs1_3186_, v_snd_3187_, v___x_15201__boxed_3199_, v___x_15202__boxed_3200_, v___x_15203__boxed_3201_, v_alts_3191_, v_zs2_3192_, v___ctorRet2_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
lean_dec_ref(v___ctorRet2_3193_);
lean_dec_ref(v_zs2_3192_);
lean_dec_ref(v_alts_3191_);
lean_dec_ref(v_snd_3187_);
lean_dec(v___x_3185_);
lean_dec_ref(v_a_3184_);
lean_dec_ref(v___x_3183_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(lean_object* v___x_3203_, lean_object* v_a_3204_, lean_object* v___x_3205_, lean_object* v_snd_3206_, uint8_t v___x_3207_, uint8_t v___x_3208_, uint8_t v___x_3209_, lean_object* v_alts_3210_, lean_object* v_a_3211_, lean_object* v_zs1_3212_, lean_object* v___ctorRet1_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___f_3222_; lean_object* v___x_3223_; 
v___x_3219_ = lean_box(v___x_3207_);
v___x_3220_ = lean_box(v___x_3208_);
v___x_3221_ = lean_box(v___x_3209_);
v___f_3222_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed), 16, 9);
lean_closure_set(v___f_3222_, 0, v___x_3203_);
lean_closure_set(v___f_3222_, 1, v_a_3204_);
lean_closure_set(v___f_3222_, 2, v___x_3205_);
lean_closure_set(v___f_3222_, 3, v_zs1_3212_);
lean_closure_set(v___f_3222_, 4, v_snd_3206_);
lean_closure_set(v___f_3222_, 5, v___x_3219_);
lean_closure_set(v___f_3222_, 6, v___x_3220_);
lean_closure_set(v___f_3222_, 7, v___x_3221_);
lean_closure_set(v___f_3222_, 8, v_alts_3210_);
v___x_3223_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3211_, v___f_3222_, v___x_3208_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(lean_object* v___x_3224_, lean_object* v_a_3225_, lean_object* v___x_3226_, lean_object* v_snd_3227_, lean_object* v___x_3228_, lean_object* v___x_3229_, lean_object* v___x_3230_, lean_object* v_alts_3231_, lean_object* v_a_3232_, lean_object* v_zs1_3233_, lean_object* v___ctorRet1_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
uint8_t v___x_15400__boxed_3240_; uint8_t v___x_15401__boxed_3241_; uint8_t v___x_15402__boxed_3242_; lean_object* v_res_3243_; 
v___x_15400__boxed_3240_ = lean_unbox(v___x_3228_);
v___x_15401__boxed_3241_ = lean_unbox(v___x_3229_);
v___x_15402__boxed_3242_ = lean_unbox(v___x_3230_);
v_res_3243_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(v___x_3224_, v_a_3225_, v___x_3226_, v_snd_3227_, v___x_15400__boxed_3240_, v___x_15401__boxed_3241_, v___x_15402__boxed_3242_, v_alts_3231_, v_a_3232_, v_zs1_3233_, v___ctorRet1_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec_ref(v___ctorRet1_3234_);
return v_res_3243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(lean_object* v_tail_3244_, lean_object* v_params_3245_, lean_object* v_a_3246_, lean_object* v_snd_3247_, lean_object* v_alts_3248_, size_t v_sz_3249_, size_t v_i_3250_, lean_object* v_bs_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
uint8_t v___x_3257_; 
v___x_3257_ = lean_usize_dec_lt(v_i_3250_, v_sz_3249_);
if (v___x_3257_ == 0)
{
lean_object* v___x_3258_; 
lean_dec_ref(v_alts_3248_);
lean_dec_ref(v_snd_3247_);
lean_dec_ref(v_a_3246_);
lean_dec(v_tail_3244_);
v___x_3258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3258_, 0, v_bs_3251_);
return v___x_3258_;
}
else
{
lean_object* v___x_3259_; uint8_t v___x_3260_; uint8_t v___x_3261_; lean_object* v_v_3262_; lean_object* v___x_3263_; lean_object* v_bs_x27_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v___x_3259_ = l_Lean_instInhabitedExpr;
v___x_3260_ = 0;
v___x_3261_ = 1;
v_v_3262_ = lean_array_uget(v_bs_3251_, v_i_3250_);
v___x_3263_ = lean_unsigned_to_nat(0u);
v_bs_x27_3264_ = lean_array_uset(v_bs_3251_, v_i_3250_, v___x_3263_);
v___x_3265_ = lean_usize_to_nat(v_i_3250_);
lean_inc(v_tail_3244_);
v___x_3266_ = l_Lean_mkConst(v_v_3262_, v_tail_3244_);
v___x_3267_ = l_Lean_mkAppN(v___x_3266_, v_params_3245_);
lean_inc(v___y_3255_);
lean_inc_ref(v___y_3254_);
lean_inc(v___y_3253_);
lean_inc_ref(v___y_3252_);
v___x_3268_ = lean_infer_type(v___x_3267_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___f_3273_; lean_object* v___x_3274_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc_n(v_a_3269_, 2);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = lean_box(v___x_3257_);
v___x_3271_ = lean_box(v___x_3260_);
v___x_3272_ = lean_box(v___x_3261_);
lean_inc_ref(v_alts_3248_);
lean_inc_ref(v_snd_3247_);
lean_inc_ref(v_a_3246_);
v___f_3273_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3273_, 0, v___x_3259_);
lean_closure_set(v___f_3273_, 1, v_a_3246_);
lean_closure_set(v___f_3273_, 2, v___x_3265_);
lean_closure_set(v___f_3273_, 3, v_snd_3247_);
lean_closure_set(v___f_3273_, 4, v___x_3270_);
lean_closure_set(v___f_3273_, 5, v___x_3271_);
lean_closure_set(v___f_3273_, 6, v___x_3272_);
lean_closure_set(v___f_3273_, 7, v_alts_3248_);
lean_closure_set(v___f_3273_, 8, v_a_3269_);
v___x_3274_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_3269_, v___f_3273_, v___x_3260_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; size_t v___x_3276_; size_t v___x_3277_; lean_object* v___x_3278_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = ((size_t)1ULL);
v___x_3277_ = lean_usize_add(v_i_3250_, v___x_3276_);
v___x_3278_ = lean_array_uset(v_bs_x27_3264_, v_i_3250_, v_a_3275_);
v_i_3250_ = v___x_3277_;
v_bs_3251_ = v___x_3278_;
goto _start;
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_dec_ref(v_bs_x27_3264_);
lean_dec_ref(v_alts_3248_);
lean_dec_ref(v_snd_3247_);
lean_dec_ref(v_a_3246_);
lean_dec(v_tail_3244_);
v_a_3280_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3274_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3274_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec(v___x_3265_);
lean_dec_ref(v_bs_x27_3264_);
lean_dec_ref(v_alts_3248_);
lean_dec_ref(v_snd_3247_);
lean_dec_ref(v_a_3246_);
lean_dec(v_tail_3244_);
v_a_3288_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3268_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3268_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(lean_object* v_tail_3296_, lean_object* v_params_3297_, lean_object* v_a_3298_, lean_object* v_snd_3299_, lean_object* v_alts_3300_, lean_object* v_sz_3301_, lean_object* v_i_3302_, lean_object* v_bs_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
size_t v_sz_boxed_3309_; size_t v_i_boxed_3310_; lean_object* v_res_3311_; 
v_sz_boxed_3309_ = lean_unbox_usize(v_sz_3301_);
lean_dec(v_sz_3301_);
v_i_boxed_3310_ = lean_unbox_usize(v_i_3302_);
lean_dec(v_i_3302_);
v_res_3311_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3296_, v_params_3297_, v_a_3298_, v_snd_3299_, v_alts_3300_, v_sz_boxed_3309_, v_i_boxed_3310_, v_bs_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec_ref(v_params_3297_);
return v_res_3311_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_unsigned_to_nat(16u);
v___x_3314_ = lean_mk_array(v___x_3313_, v___x_3312_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3(lean_object* v_motive_3315_, lean_object* v___x_3316_, uint8_t v___x_3317_, uint8_t v___x_3318_, uint8_t v___x_3319_, lean_object* v_ism1_x27_3320_, lean_object* v_is_3321_, lean_object* v___x_3322_, lean_object* v___x_3323_, lean_object* v___x_3324_, lean_object* v___x_3325_, lean_object* v_params_3326_, lean_object* v___x_3327_, lean_object* v___x_3328_, lean_object* v_heq_3329_, lean_object* v_val_3330_, lean_object* v_tail_3331_, lean_object* v_alts_3332_, size_t v_sz_3333_, size_t v___x_3334_, lean_object* v___x_3335_, lean_object* v___x_3336_, lean_object* v_declName_3337_, lean_object* v_levelParams_3338_, lean_object* v_numIndices_3339_, lean_object* v___x_3340_, lean_object* v___x_3341_, lean_object* v_numParams_3342_, lean_object* v_snd_3343_, lean_object* v_ism2_x27_3344_, lean_object* v_x_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___f_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3351_ = lean_box(v___x_3317_);
v___x_3352_ = lean_box(v___x_3318_);
v___x_3353_ = lean_box(v___x_3319_);
lean_inc_ref(v___x_3322_);
lean_inc_ref_n(v_is_3321_, 2);
lean_inc_ref(v_ism1_x27_3320_);
lean_inc_ref(v_motive_3315_);
v___f_3354_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__1___boxed), 16, 9);
lean_closure_set(v___f_3354_, 0, v_motive_3315_);
lean_closure_set(v___f_3354_, 1, v___x_3316_);
lean_closure_set(v___f_3354_, 2, v___x_3351_);
lean_closure_set(v___f_3354_, 3, v___x_3352_);
lean_closure_set(v___f_3354_, 4, v___x_3353_);
lean_closure_set(v___f_3354_, 5, v_ism1_x27_3320_);
lean_closure_set(v___f_3354_, 6, v_ism2_x27_3344_);
lean_closure_set(v___f_3354_, 7, v_is_3321_);
lean_closure_set(v___f_3354_, 8, v___x_3322_);
lean_inc_ref(v___x_3323_);
v___x_3355_ = lean_array_push(v_is_3321_, v___x_3323_);
v___x_3356_ = l_Lean_Meta_withNewEqs___redArg(v___x_3355_, v_ism1_x27_3320_, v___f_3354_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v_fst_3358_; lean_object* v_snd_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3460_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v_fst_3358_ = lean_ctor_get(v_a_3357_, 0);
v_snd_3359_ = lean_ctor_get(v_a_3357_, 1);
v_isSharedCheck_3460_ = !lean_is_exclusive(v_a_3357_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3361_ = v_a_3357_;
v_isShared_3362_ = v_isSharedCheck_3460_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_snd_3359_);
lean_inc(v_fst_3358_);
lean_dec(v_a_3357_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3460_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3363_ = l_Lean_mkConst(v___x_3324_, v___x_3325_);
v___x_3364_ = l_Lean_mkAppN(v___x_3363_, v_params_3326_);
v___x_3365_ = l_Lean_Expr_app___override(v___x_3364_, v_fst_3358_);
lean_inc_ref(v_is_3321_);
v___x_3366_ = l_Array_append___redArg(v_is_3321_, v___x_3327_);
v___x_3367_ = l_Array_append___redArg(v___x_3366_, v_is_3321_);
v___x_3368_ = l_Array_append___redArg(v___x_3367_, v___x_3328_);
v___x_3369_ = l_Lean_mkAppN(v___x_3365_, v___x_3368_);
lean_dec_ref(v___x_3368_);
lean_inc_ref(v_heq_3329_);
v___x_3370_ = l_Lean_Expr_app___override(v___x_3369_, v_heq_3329_);
v___x_3371_ = l_Lean_InductiveVal_numCtors(v_val_3330_);
lean_inc_ref(v___x_3370_);
v___x_3372_ = l_Lean_Meta_inferArgumentTypesN(v___x_3371_, v___x_3370_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3374_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
lean_dec_ref_known(v___x_3372_, 1);
lean_inc_ref(v_alts_3332_);
lean_inc(v_snd_3359_);
v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_3331_, v_params_3326_, v_a_3373_, v_snd_3359_, v_alts_3332_, v_sz_3333_, v___x_3334_, v___x_3335_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3374_) == 0)
{
lean_object* v_a_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v_a_3375_ = lean_ctor_get(v___x_3374_, 0);
lean_inc(v_a_3375_);
lean_dec_ref_known(v___x_3374_, 1);
v___x_3376_ = l_Lean_mkAppN(v___x_3370_, v_a_3375_);
lean_dec(v_a_3375_);
v___x_3377_ = l_Lean_mkAppN(v___x_3376_, v_snd_3359_);
lean_dec(v_snd_3359_);
lean_inc_ref(v___x_3336_);
v___x_3378_ = lean_array_push(v___x_3336_, v_motive_3315_);
v___x_3379_ = l_Array_append___redArg(v_params_3326_, v___x_3378_);
lean_dec_ref(v___x_3378_);
v___x_3380_ = l_Array_append___redArg(v___x_3379_, v_is_3321_);
lean_dec_ref(v_is_3321_);
v___x_3381_ = lean_unsigned_to_nat(2u);
v___x_3382_ = lean_mk_empty_array_with_capacity(v___x_3381_);
v___x_3383_ = lean_array_push(v___x_3382_, v___x_3323_);
v___x_3384_ = lean_array_push(v___x_3383_, v___x_3322_);
v___x_3385_ = l_Array_append___redArg(v___x_3380_, v___x_3384_);
lean_dec_ref(v___x_3384_);
v___x_3386_ = lean_array_push(v___x_3336_, v_heq_3329_);
v___x_3387_ = l_Array_append___redArg(v___x_3385_, v___x_3386_);
lean_dec_ref(v___x_3386_);
v___x_3388_ = l_Array_append___redArg(v___x_3387_, v_alts_3332_);
lean_dec_ref(v_alts_3332_);
v___x_3389_ = l_Lean_Meta_mkLambdaFVars(v___x_3388_, v___x_3377_, v___x_3317_, v___x_3318_, v___x_3317_, v___x_3318_, v___x_3319_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec_ref(v___x_3388_);
if (lean_obj_tag(v___x_3389_) == 0)
{
lean_object* v_a_3390_; lean_object* v___x_3391_; 
v_a_3390_ = lean_ctor_get(v___x_3389_, 0);
lean_inc_n(v_a_3390_, 2);
lean_dec_ref_known(v___x_3389_, 1);
lean_inc(v___y_3349_);
lean_inc_ref(v___y_3348_);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
v___x_3391_ = lean_infer_type(v_a_3390_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_object* v_a_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3427_; 
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
lean_inc(v_a_3392_);
lean_dec_ref_known(v___x_3391_, 1);
v___x_3393_ = lean_box(1);
lean_inc(v_declName_3337_);
v___x_3394_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_3337_, v_levelParams_3338_, v_a_3392_, v_a_3390_, v___x_3393_, v___y_3349_);
v_a_3395_ = lean_ctor_get(v___x_3394_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3397_ = v___x_3394_;
v_isShared_3398_ = v_isSharedCheck_3427_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3394_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3427_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 1);
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
lean_object* v___x_3401_; lean_object* v___f_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3412_; 
v___x_3401_ = lean_box(v___x_3317_);
lean_inc_ref(v___x_3400_);
v___f_3402_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__2___boxed), 7, 2);
lean_closure_set(v___f_3402_, 0, v___x_3400_);
lean_closure_set(v___f_3402_, 1, v___x_3401_);
v___x_3403_ = lean_nat_add(v_numIndices_3339_, v___x_3340_);
lean_inc(v___x_3341_);
v___x_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3341_);
v___x_3405_ = lean_box(0);
v___x_3406_ = lean_mk_empty_array_with_capacity(v___x_3340_);
v___x_3407_ = lean_array_push(v___x_3406_, v___x_3405_);
v___x_3408_ = lean_array_push(v___x_3407_, v___x_3405_);
v___x_3409_ = lean_array_push(v___x_3408_, v___x_3405_);
v___x_3410_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___lam__3___closed__0, &l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once, _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 1, v___x_3410_);
lean_ctor_set(v___x_3361_, 0, v___x_3341_);
v___x_3412_ = v___x_3361_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3341_);
lean_ctor_set(v_reuseFailAlloc_3425_, 1, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3413_; uint8_t v___y_3415_; uint8_t v___x_3424_; 
v___x_3413_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3413_, 0, v_numParams_3342_);
lean_ctor_set(v___x_3413_, 1, v___x_3403_);
lean_ctor_set(v___x_3413_, 2, v_snd_3343_);
lean_ctor_set(v___x_3413_, 3, v___x_3404_);
lean_ctor_set(v___x_3413_, 4, v___x_3409_);
lean_ctor_set(v___x_3413_, 5, v___x_3412_);
v___x_3424_ = l_Lean_isPrivateName(v_declName_3337_);
if (v___x_3424_ == 0)
{
v___y_3415_ = v___x_3318_;
goto v___jp_3414_;
}
else
{
v___y_3415_ = v___x_3317_;
goto v___jp_3414_;
}
v___jp_3414_:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(v___f_3402_, v___y_3415_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3416_) == 0)
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec_ref_known(v___x_3416_, 1);
v___x_3417_ = l_Lean_Elab_Term_elabAsElim;
lean_inc(v_declName_3337_);
v___x_3418_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__13(v___x_3417_, v_declName_3337_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v___x_3419_; uint8_t v___x_3420_; lean_object* v___x_3421_; 
lean_dec_ref_known(v___x_3418_, 1);
lean_inc_n(v_declName_3337_, 2);
v___x_3419_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_3337_, v___x_3413_, v___y_3347_, v___y_3349_);
lean_dec_ref(v___x_3419_);
v___x_3420_ = 0;
v___x_3421_ = l_Lean_Meta_setInlineAttribute(v_declName_3337_, v___x_3420_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v___x_3422_; 
lean_dec_ref_known(v___x_3421_, 1);
v___x_3422_ = l_Lean_enableRealizationsForConst(v_declName_3337_, v___y_3348_, v___y_3349_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v___x_3423_; 
lean_dec_ref_known(v___x_3422_, 1);
v___x_3423_ = l_Lean_compileDecl(v___x_3400_, v___x_3318_, v___y_3348_, v___y_3349_);
return v___x_3423_;
}
else
{
lean_dec_ref(v___x_3400_);
return v___x_3422_;
}
}
else
{
lean_dec_ref(v___x_3400_);
lean_dec(v_declName_3337_);
return v___x_3421_;
}
}
else
{
lean_dec_ref_known(v___x_3413_, 6);
lean_dec_ref(v___x_3400_);
lean_dec(v_declName_3337_);
return v___x_3418_;
}
}
else
{
lean_dec_ref_known(v___x_3413_, 6);
lean_dec_ref(v___x_3400_);
lean_dec(v_declName_3337_);
return v___x_3416_;
}
}
}
}
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_dec(v_a_3390_);
lean_del_object(v___x_3361_);
lean_dec_ref(v_snd_3343_);
lean_dec(v_numParams_3342_);
lean_dec(v___x_3341_);
lean_dec(v_levelParams_3338_);
lean_dec(v_declName_3337_);
v_a_3428_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3391_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3391_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
else
{
lean_object* v_a_3436_; lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3443_; 
lean_del_object(v___x_3361_);
lean_dec_ref(v_snd_3343_);
lean_dec(v_numParams_3342_);
lean_dec(v___x_3341_);
lean_dec(v_levelParams_3338_);
lean_dec(v_declName_3337_);
v_a_3436_ = lean_ctor_get(v___x_3389_, 0);
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3443_ == 0)
{
v___x_3438_ = v___x_3389_;
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
else
{
lean_inc(v_a_3436_);
lean_dec(v___x_3389_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3443_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3441_; 
if (v_isShared_3439_ == 0)
{
v___x_3441_ = v___x_3438_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v_a_3436_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
lean_dec_ref(v___x_3370_);
lean_del_object(v___x_3361_);
lean_dec(v_snd_3359_);
lean_dec_ref(v_snd_3343_);
lean_dec(v_numParams_3342_);
lean_dec(v___x_3341_);
lean_dec(v_levelParams_3338_);
lean_dec(v_declName_3337_);
lean_dec_ref(v___x_3336_);
lean_dec_ref(v_alts_3332_);
lean_dec_ref(v_heq_3329_);
lean_dec_ref(v_params_3326_);
lean_dec_ref(v___x_3323_);
lean_dec_ref(v___x_3322_);
lean_dec_ref(v_is_3321_);
lean_dec_ref(v_motive_3315_);
v_a_3444_ = lean_ctor_get(v___x_3374_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3374_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3374_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3374_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
lean_dec_ref(v___x_3370_);
lean_del_object(v___x_3361_);
lean_dec(v_snd_3359_);
lean_dec_ref(v_snd_3343_);
lean_dec(v_numParams_3342_);
lean_dec(v___x_3341_);
lean_dec(v_levelParams_3338_);
lean_dec(v_declName_3337_);
lean_dec_ref(v___x_3336_);
lean_dec_ref(v___x_3335_);
lean_dec_ref(v_alts_3332_);
lean_dec(v_tail_3331_);
lean_dec_ref(v_heq_3329_);
lean_dec_ref(v_params_3326_);
lean_dec_ref(v___x_3323_);
lean_dec_ref(v___x_3322_);
lean_dec_ref(v_is_3321_);
lean_dec_ref(v_motive_3315_);
v_a_3452_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3372_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3372_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref(v_snd_3343_);
lean_dec(v_numParams_3342_);
lean_dec(v___x_3341_);
lean_dec(v_levelParams_3338_);
lean_dec(v_declName_3337_);
lean_dec_ref(v___x_3336_);
lean_dec_ref(v___x_3335_);
lean_dec_ref(v_alts_3332_);
lean_dec(v_tail_3331_);
lean_dec_ref(v_heq_3329_);
lean_dec_ref(v_params_3326_);
lean_dec(v___x_3325_);
lean_dec(v___x_3324_);
lean_dec_ref(v___x_3323_);
lean_dec_ref(v___x_3322_);
lean_dec_ref(v_is_3321_);
lean_dec_ref(v_motive_3315_);
v_a_3461_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3356_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3356_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__3___boxed(lean_object** _args){
lean_object* v_motive_3469_ = _args[0];
lean_object* v___x_3470_ = _args[1];
lean_object* v___x_3471_ = _args[2];
lean_object* v___x_3472_ = _args[3];
lean_object* v___x_3473_ = _args[4];
lean_object* v_ism1_x27_3474_ = _args[5];
lean_object* v_is_3475_ = _args[6];
lean_object* v___x_3476_ = _args[7];
lean_object* v___x_3477_ = _args[8];
lean_object* v___x_3478_ = _args[9];
lean_object* v___x_3479_ = _args[10];
lean_object* v_params_3480_ = _args[11];
lean_object* v___x_3481_ = _args[12];
lean_object* v___x_3482_ = _args[13];
lean_object* v_heq_3483_ = _args[14];
lean_object* v_val_3484_ = _args[15];
lean_object* v_tail_3485_ = _args[16];
lean_object* v_alts_3486_ = _args[17];
lean_object* v_sz_3487_ = _args[18];
lean_object* v___x_3488_ = _args[19];
lean_object* v___x_3489_ = _args[20];
lean_object* v___x_3490_ = _args[21];
lean_object* v_declName_3491_ = _args[22];
lean_object* v_levelParams_3492_ = _args[23];
lean_object* v_numIndices_3493_ = _args[24];
lean_object* v___x_3494_ = _args[25];
lean_object* v___x_3495_ = _args[26];
lean_object* v_numParams_3496_ = _args[27];
lean_object* v_snd_3497_ = _args[28];
lean_object* v_ism2_x27_3498_ = _args[29];
lean_object* v_x_3499_ = _args[30];
lean_object* v___y_3500_ = _args[31];
lean_object* v___y_3501_ = _args[32];
lean_object* v___y_3502_ = _args[33];
lean_object* v___y_3503_ = _args[34];
lean_object* v___y_3504_ = _args[35];
_start:
{
uint8_t v___x_15550__boxed_3505_; uint8_t v___x_15551__boxed_3506_; uint8_t v___x_15552__boxed_3507_; size_t v_sz_boxed_3508_; size_t v___x_15561__boxed_3509_; lean_object* v_res_3510_; 
v___x_15550__boxed_3505_ = lean_unbox(v___x_3471_);
v___x_15551__boxed_3506_ = lean_unbox(v___x_3472_);
v___x_15552__boxed_3507_ = lean_unbox(v___x_3473_);
v_sz_boxed_3508_ = lean_unbox_usize(v_sz_3487_);
lean_dec(v_sz_3487_);
v___x_15561__boxed_3509_ = lean_unbox_usize(v___x_3488_);
lean_dec(v___x_3488_);
v_res_3510_ = l_Lean_mkCasesOnSameCtor___lam__3(v_motive_3469_, v___x_3470_, v___x_15550__boxed_3505_, v___x_15551__boxed_3506_, v___x_15552__boxed_3507_, v_ism1_x27_3474_, v_is_3475_, v___x_3476_, v___x_3477_, v___x_3478_, v___x_3479_, v_params_3480_, v___x_3481_, v___x_3482_, v_heq_3483_, v_val_3484_, v_tail_3485_, v_alts_3486_, v_sz_boxed_3508_, v___x_15561__boxed_3509_, v___x_3489_, v___x_3490_, v_declName_3491_, v_levelParams_3492_, v_numIndices_3493_, v___x_3494_, v___x_3495_, v_numParams_3496_, v_snd_3497_, v_ism2_x27_3498_, v_x_3499_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3500_);
lean_dec_ref(v_x_3499_);
lean_dec(v___x_3494_);
lean_dec(v_numIndices_3493_);
lean_dec_ref(v_val_3484_);
lean_dec_ref(v___x_3482_);
lean_dec_ref(v___x_3481_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4(lean_object* v_motive_3511_, lean_object* v___x_3512_, uint8_t v___x_3513_, uint8_t v___x_3514_, uint8_t v___x_3515_, lean_object* v_is_3516_, lean_object* v___x_3517_, lean_object* v___x_3518_, lean_object* v___x_3519_, lean_object* v___x_3520_, lean_object* v_params_3521_, lean_object* v___x_3522_, lean_object* v___x_3523_, lean_object* v_heq_3524_, lean_object* v_val_3525_, lean_object* v_tail_3526_, lean_object* v_alts_3527_, size_t v_sz_3528_, size_t v___x_3529_, lean_object* v___x_3530_, lean_object* v___x_3531_, lean_object* v_declName_3532_, lean_object* v_levelParams_3533_, lean_object* v_numIndices_3534_, lean_object* v___x_3535_, lean_object* v___x_3536_, lean_object* v_numParams_3537_, lean_object* v_snd_3538_, lean_object* v___x_3539_, lean_object* v___x_3540_, lean_object* v_ism1_x27_3541_, lean_object* v_x_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; 
v___x_3548_ = lean_box(v___x_3513_);
v___x_3549_ = lean_box(v___x_3514_);
v___x_3550_ = lean_box(v___x_3515_);
v___x_3551_ = lean_box_usize(v_sz_3528_);
v___x_3552_ = lean_box_usize(v___x_3529_);
v___f_3553_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__3___boxed), 36, 29);
lean_closure_set(v___f_3553_, 0, v_motive_3511_);
lean_closure_set(v___f_3553_, 1, v___x_3512_);
lean_closure_set(v___f_3553_, 2, v___x_3548_);
lean_closure_set(v___f_3553_, 3, v___x_3549_);
lean_closure_set(v___f_3553_, 4, v___x_3550_);
lean_closure_set(v___f_3553_, 5, v_ism1_x27_3541_);
lean_closure_set(v___f_3553_, 6, v_is_3516_);
lean_closure_set(v___f_3553_, 7, v___x_3517_);
lean_closure_set(v___f_3553_, 8, v___x_3518_);
lean_closure_set(v___f_3553_, 9, v___x_3519_);
lean_closure_set(v___f_3553_, 10, v___x_3520_);
lean_closure_set(v___f_3553_, 11, v_params_3521_);
lean_closure_set(v___f_3553_, 12, v___x_3522_);
lean_closure_set(v___f_3553_, 13, v___x_3523_);
lean_closure_set(v___f_3553_, 14, v_heq_3524_);
lean_closure_set(v___f_3553_, 15, v_val_3525_);
lean_closure_set(v___f_3553_, 16, v_tail_3526_);
lean_closure_set(v___f_3553_, 17, v_alts_3527_);
lean_closure_set(v___f_3553_, 18, v___x_3551_);
lean_closure_set(v___f_3553_, 19, v___x_3552_);
lean_closure_set(v___f_3553_, 20, v___x_3530_);
lean_closure_set(v___f_3553_, 21, v___x_3531_);
lean_closure_set(v___f_3553_, 22, v_declName_3532_);
lean_closure_set(v___f_3553_, 23, v_levelParams_3533_);
lean_closure_set(v___f_3553_, 24, v_numIndices_3534_);
lean_closure_set(v___f_3553_, 25, v___x_3535_);
lean_closure_set(v___f_3553_, 26, v___x_3536_);
lean_closure_set(v___f_3553_, 27, v_numParams_3537_);
lean_closure_set(v___f_3553_, 28, v_snd_3538_);
v___x_3554_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3539_, v___x_3540_, v___f_3553_, v___x_3513_, v___x_3513_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
return v___x_3554_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__4___boxed(lean_object** _args){
lean_object* v_motive_3555_ = _args[0];
lean_object* v___x_3556_ = _args[1];
lean_object* v___x_3557_ = _args[2];
lean_object* v___x_3558_ = _args[3];
lean_object* v___x_3559_ = _args[4];
lean_object* v_is_3560_ = _args[5];
lean_object* v___x_3561_ = _args[6];
lean_object* v___x_3562_ = _args[7];
lean_object* v___x_3563_ = _args[8];
lean_object* v___x_3564_ = _args[9];
lean_object* v_params_3565_ = _args[10];
lean_object* v___x_3566_ = _args[11];
lean_object* v___x_3567_ = _args[12];
lean_object* v_heq_3568_ = _args[13];
lean_object* v_val_3569_ = _args[14];
lean_object* v_tail_3570_ = _args[15];
lean_object* v_alts_3571_ = _args[16];
lean_object* v_sz_3572_ = _args[17];
lean_object* v___x_3573_ = _args[18];
lean_object* v___x_3574_ = _args[19];
lean_object* v___x_3575_ = _args[20];
lean_object* v_declName_3576_ = _args[21];
lean_object* v_levelParams_3577_ = _args[22];
lean_object* v_numIndices_3578_ = _args[23];
lean_object* v___x_3579_ = _args[24];
lean_object* v___x_3580_ = _args[25];
lean_object* v_numParams_3581_ = _args[26];
lean_object* v_snd_3582_ = _args[27];
lean_object* v___x_3583_ = _args[28];
lean_object* v___x_3584_ = _args[29];
lean_object* v_ism1_x27_3585_ = _args[30];
lean_object* v_x_3586_ = _args[31];
lean_object* v___y_3587_ = _args[32];
lean_object* v___y_3588_ = _args[33];
lean_object* v___y_3589_ = _args[34];
lean_object* v___y_3590_ = _args[35];
lean_object* v___y_3591_ = _args[36];
_start:
{
uint8_t v___x_15872__boxed_3592_; uint8_t v___x_15873__boxed_3593_; uint8_t v___x_15874__boxed_3594_; size_t v_sz_boxed_3595_; size_t v___x_15883__boxed_3596_; lean_object* v_res_3597_; 
v___x_15872__boxed_3592_ = lean_unbox(v___x_3557_);
v___x_15873__boxed_3593_ = lean_unbox(v___x_3558_);
v___x_15874__boxed_3594_ = lean_unbox(v___x_3559_);
v_sz_boxed_3595_ = lean_unbox_usize(v_sz_3572_);
lean_dec(v_sz_3572_);
v___x_15883__boxed_3596_ = lean_unbox_usize(v___x_3573_);
lean_dec(v___x_3573_);
v_res_3597_ = l_Lean_mkCasesOnSameCtor___lam__4(v_motive_3555_, v___x_3556_, v___x_15872__boxed_3592_, v___x_15873__boxed_3593_, v___x_15874__boxed_3594_, v_is_3560_, v___x_3561_, v___x_3562_, v___x_3563_, v___x_3564_, v_params_3565_, v___x_3566_, v___x_3567_, v_heq_3568_, v_val_3569_, v_tail_3570_, v_alts_3571_, v_sz_boxed_3595_, v___x_15883__boxed_3596_, v___x_3574_, v___x_3575_, v_declName_3576_, v_levelParams_3577_, v_numIndices_3578_, v___x_3579_, v___x_3580_, v_numParams_3581_, v_snd_3582_, v___x_3583_, v___x_3584_, v_ism1_x27_3585_, v_x_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec_ref(v_x_3586_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5(lean_object* v_numIndices_3598_, lean_object* v___x_3599_, lean_object* v_motive_3600_, lean_object* v___x_3601_, uint8_t v___x_3602_, uint8_t v___x_3603_, uint8_t v___x_3604_, lean_object* v_is_3605_, lean_object* v___x_3606_, lean_object* v___x_3607_, lean_object* v___x_3608_, lean_object* v___x_3609_, lean_object* v_params_3610_, lean_object* v___x_3611_, lean_object* v___x_3612_, lean_object* v_heq_3613_, lean_object* v_val_3614_, lean_object* v_tail_3615_, size_t v_sz_3616_, size_t v___x_3617_, lean_object* v___x_3618_, lean_object* v___x_3619_, lean_object* v_declName_3620_, lean_object* v_levelParams_3621_, lean_object* v___x_3622_, lean_object* v___x_3623_, lean_object* v_numParams_3624_, lean_object* v_snd_3625_, lean_object* v___x_3626_, lean_object* v_alts_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___f_3640_; lean_object* v___x_3641_; 
v___x_3633_ = lean_nat_add(v_numIndices_3598_, v___x_3599_);
v___x_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
v___x_3635_ = lean_box(v___x_3602_);
v___x_3636_ = lean_box(v___x_3603_);
v___x_3637_ = lean_box(v___x_3604_);
v___x_3638_ = lean_box_usize(v_sz_3616_);
v___x_3639_ = lean_box_usize(v___x_3617_);
lean_inc_ref(v___x_3634_);
lean_inc_ref(v___x_3626_);
v___f_3640_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__4___boxed), 37, 30);
lean_closure_set(v___f_3640_, 0, v_motive_3600_);
lean_closure_set(v___f_3640_, 1, v___x_3601_);
lean_closure_set(v___f_3640_, 2, v___x_3635_);
lean_closure_set(v___f_3640_, 3, v___x_3636_);
lean_closure_set(v___f_3640_, 4, v___x_3637_);
lean_closure_set(v___f_3640_, 5, v_is_3605_);
lean_closure_set(v___f_3640_, 6, v___x_3606_);
lean_closure_set(v___f_3640_, 7, v___x_3607_);
lean_closure_set(v___f_3640_, 8, v___x_3608_);
lean_closure_set(v___f_3640_, 9, v___x_3609_);
lean_closure_set(v___f_3640_, 10, v_params_3610_);
lean_closure_set(v___f_3640_, 11, v___x_3611_);
lean_closure_set(v___f_3640_, 12, v___x_3612_);
lean_closure_set(v___f_3640_, 13, v_heq_3613_);
lean_closure_set(v___f_3640_, 14, v_val_3614_);
lean_closure_set(v___f_3640_, 15, v_tail_3615_);
lean_closure_set(v___f_3640_, 16, v_alts_3627_);
lean_closure_set(v___f_3640_, 17, v___x_3638_);
lean_closure_set(v___f_3640_, 18, v___x_3639_);
lean_closure_set(v___f_3640_, 19, v___x_3618_);
lean_closure_set(v___f_3640_, 20, v___x_3619_);
lean_closure_set(v___f_3640_, 21, v_declName_3620_);
lean_closure_set(v___f_3640_, 22, v_levelParams_3621_);
lean_closure_set(v___f_3640_, 23, v_numIndices_3598_);
lean_closure_set(v___f_3640_, 24, v___x_3622_);
lean_closure_set(v___f_3640_, 25, v___x_3623_);
lean_closure_set(v___f_3640_, 26, v_numParams_3624_);
lean_closure_set(v___f_3640_, 27, v_snd_3625_);
lean_closure_set(v___f_3640_, 28, v___x_3626_);
lean_closure_set(v___f_3640_, 29, v___x_3634_);
v___x_3641_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_3626_, v___x_3634_, v___f_3640_, v___x_3602_, v___x_3602_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__5___boxed(lean_object** _args){
lean_object* v_numIndices_3642_ = _args[0];
lean_object* v___x_3643_ = _args[1];
lean_object* v_motive_3644_ = _args[2];
lean_object* v___x_3645_ = _args[3];
lean_object* v___x_3646_ = _args[4];
lean_object* v___x_3647_ = _args[5];
lean_object* v___x_3648_ = _args[6];
lean_object* v_is_3649_ = _args[7];
lean_object* v___x_3650_ = _args[8];
lean_object* v___x_3651_ = _args[9];
lean_object* v___x_3652_ = _args[10];
lean_object* v___x_3653_ = _args[11];
lean_object* v_params_3654_ = _args[12];
lean_object* v___x_3655_ = _args[13];
lean_object* v___x_3656_ = _args[14];
lean_object* v_heq_3657_ = _args[15];
lean_object* v_val_3658_ = _args[16];
lean_object* v_tail_3659_ = _args[17];
lean_object* v_sz_3660_ = _args[18];
lean_object* v___x_3661_ = _args[19];
lean_object* v___x_3662_ = _args[20];
lean_object* v___x_3663_ = _args[21];
lean_object* v_declName_3664_ = _args[22];
lean_object* v_levelParams_3665_ = _args[23];
lean_object* v___x_3666_ = _args[24];
lean_object* v___x_3667_ = _args[25];
lean_object* v_numParams_3668_ = _args[26];
lean_object* v_snd_3669_ = _args[27];
lean_object* v___x_3670_ = _args[28];
lean_object* v_alts_3671_ = _args[29];
lean_object* v___y_3672_ = _args[30];
lean_object* v___y_3673_ = _args[31];
lean_object* v___y_3674_ = _args[32];
lean_object* v___y_3675_ = _args[33];
lean_object* v___y_3676_ = _args[34];
_start:
{
uint8_t v___x_15965__boxed_3677_; uint8_t v___x_15966__boxed_3678_; uint8_t v___x_15967__boxed_3679_; size_t v_sz_boxed_3680_; size_t v___x_15976__boxed_3681_; lean_object* v_res_3682_; 
v___x_15965__boxed_3677_ = lean_unbox(v___x_3646_);
v___x_15966__boxed_3678_ = lean_unbox(v___x_3647_);
v___x_15967__boxed_3679_ = lean_unbox(v___x_3648_);
v_sz_boxed_3680_ = lean_unbox_usize(v_sz_3660_);
lean_dec(v_sz_3660_);
v___x_15976__boxed_3681_ = lean_unbox_usize(v___x_3661_);
lean_dec(v___x_3661_);
v_res_3682_ = l_Lean_mkCasesOnSameCtor___lam__5(v_numIndices_3642_, v___x_3643_, v_motive_3644_, v___x_3645_, v___x_15965__boxed_3677_, v___x_15966__boxed_3678_, v___x_15967__boxed_3679_, v_is_3649_, v___x_3650_, v___x_3651_, v___x_3652_, v___x_3653_, v_params_3654_, v___x_3655_, v___x_3656_, v_heq_3657_, v_val_3658_, v_tail_3659_, v_sz_boxed_3680_, v___x_15976__boxed_3681_, v___x_3662_, v___x_3663_, v_declName_3664_, v_levelParams_3665_, v___x_3666_, v___x_3667_, v_numParams_3668_, v_snd_3669_, v___x_3670_, v_alts_3671_, v___y_3672_, v___y_3673_, v___y_3674_, v___y_3675_);
lean_dec(v___y_3675_);
lean_dec_ref(v___y_3674_);
lean_dec(v___y_3673_);
lean_dec_ref(v___y_3672_);
lean_dec(v___x_3643_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(lean_object* v_acc_3683_, lean_object* v_declInfos_3684_, lean_object* v_k_3685_, lean_object* v_kind_3686_, lean_object* v_x_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
uint8_t v_kind_boxed_3693_; lean_object* v_res_3694_; 
v_kind_boxed_3693_ = lean_unbox(v_kind_3686_);
v_res_3694_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_3683_, v_declInfos_3684_, v_k_3685_, v_kind_boxed_3693_, v_x_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(lean_object* v_declInfos_3695_, lean_object* v_k_3696_, uint8_t v_kind_3697_, lean_object* v_acc_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v___x_3704_; lean_object* v_toApplicative_3705_; lean_object* v_toFunctor_3706_; lean_object* v_toSeq_3707_; lean_object* v_toSeqLeft_3708_; lean_object* v_toSeqRight_3709_; lean_object* v___f_3710_; lean_object* v___f_3711_; lean_object* v___f_3712_; lean_object* v___f_3713_; lean_object* v___x_3714_; lean_object* v___f_3715_; lean_object* v___f_3716_; lean_object* v___f_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v_toApplicative_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3779_; 
v___x_3704_ = lean_obj_once(&l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1, &l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1_once, _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__1);
v_toApplicative_3705_ = lean_ctor_get(v___x_3704_, 0);
v_toFunctor_3706_ = lean_ctor_get(v_toApplicative_3705_, 0);
v_toSeq_3707_ = lean_ctor_get(v_toApplicative_3705_, 2);
v_toSeqLeft_3708_ = lean_ctor_get(v_toApplicative_3705_, 3);
v_toSeqRight_3709_ = lean_ctor_get(v_toApplicative_3705_, 4);
v___f_3710_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__2));
v___f_3711_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__3));
lean_inc_ref_n(v_toFunctor_3706_, 2);
v___f_3712_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3712_, 0, v_toFunctor_3706_);
v___f_3713_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3713_, 0, v_toFunctor_3706_);
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___f_3712_);
lean_ctor_set(v___x_3714_, 1, v___f_3713_);
lean_inc(v_toSeqRight_3709_);
v___f_3715_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3715_, 0, v_toSeqRight_3709_);
lean_inc(v_toSeqLeft_3708_);
v___f_3716_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3716_, 0, v_toSeqLeft_3708_);
lean_inc(v_toSeq_3707_);
v___f_3717_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3717_, 0, v_toSeq_3707_);
v___x_3718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3714_);
lean_ctor_set(v___x_3718_, 1, v___f_3710_);
lean_ctor_set(v___x_3718_, 2, v___f_3717_);
lean_ctor_set(v___x_3718_, 3, v___f_3716_);
lean_ctor_set(v___x_3718_, 4, v___f_3715_);
v___x_3719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
lean_ctor_set(v___x_3719_, 1, v___f_3711_);
v___x_3720_ = l_StateRefT_x27_instMonad___redArg(v___x_3719_);
v_toApplicative_3721_ = lean_ctor_get(v___x_3720_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3779_ == 0)
{
lean_object* v_unused_3780_; 
v_unused_3780_ = lean_ctor_get(v___x_3720_, 1);
lean_dec(v_unused_3780_);
v___x_3723_ = v___x_3720_;
v_isShared_3724_ = v_isSharedCheck_3779_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_toApplicative_3721_);
lean_dec(v___x_3720_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3779_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v_toFunctor_3725_; lean_object* v_toSeq_3726_; lean_object* v_toSeqLeft_3727_; lean_object* v_toSeqRight_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3777_; 
v_toFunctor_3725_ = lean_ctor_get(v_toApplicative_3721_, 0);
v_toSeq_3726_ = lean_ctor_get(v_toApplicative_3721_, 2);
v_toSeqLeft_3727_ = lean_ctor_get(v_toApplicative_3721_, 3);
v_toSeqRight_3728_ = lean_ctor_get(v_toApplicative_3721_, 4);
v_isSharedCheck_3777_ = !lean_is_exclusive(v_toApplicative_3721_);
if (v_isSharedCheck_3777_ == 0)
{
lean_object* v_unused_3778_; 
v_unused_3778_ = lean_ctor_get(v_toApplicative_3721_, 1);
lean_dec(v_unused_3778_);
v___x_3730_ = v_toApplicative_3721_;
v_isShared_3731_ = v_isSharedCheck_3777_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_toSeqRight_3728_);
lean_inc(v_toSeqLeft_3727_);
lean_inc(v_toSeq_3726_);
lean_inc(v_toFunctor_3725_);
lean_dec(v_toApplicative_3721_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3777_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___f_3732_; lean_object* v___f_3733_; lean_object* v___f_3734_; lean_object* v___f_3735_; lean_object* v___x_3736_; lean_object* v___f_3737_; lean_object* v___f_3738_; lean_object* v___f_3739_; lean_object* v___x_3741_; 
v___f_3732_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__4));
v___f_3733_ = ((lean_object*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___closed__5));
lean_inc_ref(v_toFunctor_3725_);
v___f_3734_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3734_, 0, v_toFunctor_3725_);
v___f_3735_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3735_, 0, v_toFunctor_3725_);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___f_3734_);
lean_ctor_set(v___x_3736_, 1, v___f_3735_);
v___f_3737_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3737_, 0, v_toSeqRight_3728_);
v___f_3738_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3738_, 0, v_toSeqLeft_3727_);
v___f_3739_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3739_, 0, v_toSeq_3726_);
if (v_isShared_3731_ == 0)
{
lean_ctor_set(v___x_3730_, 4, v___f_3737_);
lean_ctor_set(v___x_3730_, 3, v___f_3738_);
lean_ctor_set(v___x_3730_, 2, v___f_3739_);
lean_ctor_set(v___x_3730_, 1, v___f_3732_);
lean_ctor_set(v___x_3730_, 0, v___x_3736_);
v___x_3741_ = v___x_3730_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v___x_3736_);
lean_ctor_set(v_reuseFailAlloc_3776_, 1, v___f_3732_);
lean_ctor_set(v_reuseFailAlloc_3776_, 2, v___f_3739_);
lean_ctor_set(v_reuseFailAlloc_3776_, 3, v___f_3738_);
lean_ctor_set(v_reuseFailAlloc_3776_, 4, v___f_3737_);
v___x_3741_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
lean_object* v___x_3743_; 
if (v_isShared_3724_ == 0)
{
lean_ctor_set(v___x_3723_, 1, v___f_3733_);
lean_ctor_set(v___x_3723_, 0, v___x_3741_);
v___x_3743_ = v___x_3723_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3741_);
lean_ctor_set(v_reuseFailAlloc_3775_, 1, v___f_3733_);
v___x_3743_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; uint8_t v___x_3746_; 
v___x_3744_ = lean_array_get_size(v_acc_3698_);
v___x_3745_ = lean_array_get_size(v_declInfos_3695_);
v___x_3746_ = lean_nat_dec_lt(v___x_3744_, v___x_3745_);
if (v___x_3746_ == 0)
{
lean_object* v___x_3747_; 
lean_dec_ref(v___x_3743_);
lean_dec_ref(v_declInfos_3695_);
lean_inc(v___y_3702_);
lean_inc_ref(v___y_3701_);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3699_);
v___x_3747_ = lean_apply_6(v_k_3696_, v_acc_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, lean_box(0));
return v___x_3747_;
}
else
{
lean_object* v___x_3748_; uint8_t v___x_3749_; lean_object* v___x_3750_; lean_object* v___f_3751_; lean_object* v___f_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v_snd_3757_; lean_object* v_fst_3758_; lean_object* v_fst_3759_; lean_object* v_snd_3760_; lean_object* v___x_3761_; lean_object* v___f_3762_; lean_object* v___x_3763_; 
v___x_3748_ = lean_box(0);
v___x_3749_ = 0;
v___x_3750_ = l_Lean_instInhabitedExpr;
v___f_3751_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16_spec__23___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3751_, 0, v___x_3743_);
lean_closure_set(v___f_3751_, 1, v___x_3750_);
v___f_3752_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3752_, 0, v___f_3751_);
v___x_3753_ = lean_box(v___x_3749_);
v___x_3754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
lean_ctor_set(v___x_3754_, 1, v___f_3752_);
v___x_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3748_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = lean_array_get(v___x_3755_, v_declInfos_3695_, v___x_3744_);
lean_dec_ref_known(v___x_3755_, 2);
v_snd_3757_ = lean_ctor_get(v___x_3756_, 1);
lean_inc(v_snd_3757_);
v_fst_3758_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_fst_3758_);
lean_dec(v___x_3756_);
v_fst_3759_ = lean_ctor_get(v_snd_3757_, 0);
lean_inc(v_fst_3759_);
v_snd_3760_ = lean_ctor_get(v_snd_3757_, 1);
lean_inc(v_snd_3760_);
lean_dec(v_snd_3757_);
v___x_3761_ = lean_box(v_kind_3697_);
lean_inc_ref(v_acc_3698_);
v___f_3762_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3762_, 0, v_acc_3698_);
lean_closure_set(v___f_3762_, 1, v_declInfos_3695_);
lean_closure_set(v___f_3762_, 2, v_k_3696_);
lean_closure_set(v___f_3762_, 3, v___x_3761_);
lean_inc(v___y_3702_);
lean_inc_ref(v___y_3701_);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3699_);
v___x_3763_ = lean_apply_6(v_snd_3760_, v_acc_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_, lean_box(0));
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; uint8_t v___x_3765_; lean_object* v___x_3766_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3763_, 1);
v___x_3765_ = lean_unbox(v_fst_3759_);
lean_dec(v_fst_3759_);
v___x_3766_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_3758_, v___x_3765_, v_a_3764_, v___f_3762_, v_kind_3697_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
return v___x_3766_;
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_dec_ref(v___f_3762_);
lean_dec(v_fst_3759_);
lean_dec(v_fst_3758_);
v_a_3767_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3763_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3763_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(lean_object* v_acc_3781_, lean_object* v_declInfos_3782_, lean_object* v_k_3783_, uint8_t v_kind_3784_, lean_object* v_x_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_array_push(v_acc_3781_, v_x_3785_);
v___x_3792_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3782_, v_k_3783_, v_kind_3784_, v___x_3791_, v___y_3786_, v___y_3787_, v___y_3788_, v___y_3789_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(lean_object* v_declInfos_3793_, lean_object* v_k_3794_, lean_object* v_kind_3795_, lean_object* v_acc_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
uint8_t v_kind_boxed_3802_; lean_object* v_res_3803_; 
v_kind_boxed_3802_ = lean_unbox(v_kind_3795_);
v_res_3803_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3793_, v_k_3794_, v_kind_boxed_3802_, v_acc_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(lean_object* v_declInfos_3804_, lean_object* v_k_3805_, uint8_t v_kind_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = ((lean_object*)(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___closed__0));
v___x_3813_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_3804_, v_k_3805_, v_kind_3806_, v___x_3812_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_);
return v___x_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(lean_object* v_declInfos_3814_, lean_object* v_k_3815_, lean_object* v_kind_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
uint8_t v_kind_boxed_3822_; lean_object* v_res_3823_; 
v_kind_boxed_3822_ = lean_unbox(v_kind_3816_);
v_res_3823_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_3814_, v_k_3815_, v_kind_boxed_3822_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(lean_object* v_declInfos_3824_, lean_object* v_k_3825_, uint8_t v_kind_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
size_t v_sz_3832_; size_t v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v_sz_3832_ = lean_array_size(v_declInfos_3824_);
v___x_3833_ = ((size_t)0ULL);
v___x_3834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__15(v_sz_3832_, v___x_3833_, v_declInfos_3824_);
v___x_3835_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_3834_, v_k_3825_, v_kind_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
return v___x_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(lean_object* v_declInfos_3836_, lean_object* v_k_3837_, lean_object* v_kind_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
uint8_t v_kind_boxed_3844_; lean_object* v_res_3845_; 
v_kind_boxed_3844_ = lean_unbox(v_kind_3838_);
v_res_3845_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_3836_, v_k_3837_, v_kind_boxed_3844_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(lean_object* v_declInfos_3846_, lean_object* v_k_3847_, uint8_t v_kind_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
size_t v_sz_3854_; size_t v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
v_sz_3854_ = lean_array_size(v_declInfos_3846_);
v___x_3855_ = ((size_t)0ULL);
v___x_3856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_3854_, v___x_3855_, v_declInfos_3846_);
v___x_3857_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_3856_, v_k_3847_, v_kind_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(lean_object* v_declInfos_3858_, lean_object* v_k_3859_, lean_object* v_kind_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
uint8_t v_kind_boxed_3866_; lean_object* v_res_3867_; 
v_kind_boxed_3866_ = lean_unbox(v_kind_3860_);
v_res_3867_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_declInfos_3858_, v_k_3859_, v_kind_boxed_3866_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
return v_res_3867_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3870_ = lean_box(0);
v___x_3871_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0));
v___x_3872_ = l_Lean_mkConst(v___x_3871_, v___x_3870_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(lean_object* v___x_3873_, lean_object* v_v_3874_, lean_object* v___x_3875_, lean_object* v___x_3876_, lean_object* v___x_3877_, lean_object* v_motive_3878_, uint8_t v___x_3879_, uint8_t v___x_3880_, uint8_t v___x_3881_, lean_object* v_zs12_3882_, lean_object* v_is_3883_, lean_object* v_fields1_3884_, lean_object* v_fields2_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v___y_3892_; lean_object* v___y_3893_; lean_object* v_e_3901_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
lean_inc_ref(v___x_3877_);
v___x_3911_ = l_Lean_mkAppN(v___x_3877_, v_fields1_3884_);
v___x_3912_ = l_Lean_mkAppN(v___x_3877_, v_fields2_3885_);
lean_inc(v___x_3875_);
v___x_3913_ = l_Lean_mkNatLit(v___x_3875_);
v___x_3914_ = l_Lean_Meta_mkEqRefl(v___x_3913_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
v___x_3916_ = lean_unsigned_to_nat(3u);
v___x_3917_ = lean_mk_empty_array_with_capacity(v___x_3916_);
v___x_3918_ = lean_array_push(v___x_3917_, v___x_3911_);
v___x_3919_ = lean_array_push(v___x_3918_, v___x_3912_);
v___x_3920_ = lean_array_push(v___x_3919_, v_a_3915_);
v___x_3921_ = l_Array_append___redArg(v_is_3883_, v___x_3920_);
lean_dec_ref(v___x_3920_);
v___x_3922_ = l_Lean_mkAppN(v_motive_3878_, v___x_3921_);
lean_dec_ref(v___x_3921_);
v___x_3923_ = l_Lean_Meta_mkForallFVars(v_zs12_3882_, v___x_3922_, v___x_3879_, v___x_3880_, v___x_3880_, v___x_3881_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v_a_3924_; lean_object* v___x_3925_; uint8_t v___x_3926_; 
v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_a_3924_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3925_ = lean_array_get_size(v_zs12_3882_);
v___x_3926_ = lean_nat_dec_eq(v___x_3925_, v___x_3873_);
if (v___x_3926_ == 0)
{
v_e_3901_ = v_a_3924_;
goto v___jp_3900_;
}
else
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
v___x_3927_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
v___x_3928_ = l_Lean_mkArrow(v___x_3927_, v_a_3924_, v___y_3888_, v___y_3889_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc(v_a_3929_);
lean_dec_ref_known(v___x_3928_, 1);
v_e_3901_ = v_a_3929_;
goto v___jp_3900_;
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec(v___x_3875_);
lean_dec(v_v_3874_);
lean_dec(v___x_3873_);
v_a_3930_ = lean_ctor_get(v___x_3928_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3928_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3928_);
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
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec(v___x_3875_);
lean_dec(v_v_3874_);
lean_dec(v___x_3873_);
v_a_3938_ = lean_ctor_get(v___x_3923_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3923_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3923_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3923_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref(v___x_3912_);
lean_dec_ref(v___x_3911_);
lean_dec_ref(v_is_3883_);
lean_dec_ref(v_motive_3878_);
lean_dec(v___x_3875_);
lean_dec(v_v_3874_);
lean_dec(v___x_3873_);
v_a_3946_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3914_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3914_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
v___jp_3891_:
{
lean_object* v___x_3894_; uint8_t v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3894_ = lean_array_get_size(v_zs12_3882_);
v___x_3895_ = lean_nat_dec_eq(v___x_3894_, v___x_3873_);
v___x_3896_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3896_, 0, v___x_3894_);
lean_ctor_set(v___x_3896_, 1, v___x_3873_);
lean_ctor_set_uint8(v___x_3896_, sizeof(void*)*2, v___x_3895_);
v___x_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3897_, 0, v___y_3893_);
lean_ctor_set(v___x_3897_, 1, v___y_3892_);
v___x_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
lean_ctor_set(v___x_3898_, 1, v___x_3896_);
v___x_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
return v___x_3899_;
}
v___jp_3900_:
{
if (lean_obj_tag(v_v_3874_) == 1)
{
lean_object* v_str_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_dec(v___x_3875_);
v_str_3902_ = lean_ctor_get(v_v_3874_, 1);
lean_inc_ref(v_str_3902_);
lean_dec_ref_known(v_v_3874_, 2);
v___x_3903_ = lean_box(0);
v___x_3904_ = l_Lean_Name_str___override(v___x_3903_, v_str_3902_);
v___y_3892_ = v_e_3901_;
v___y_3893_ = v___x_3904_;
goto v___jp_3891_;
}
else
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
lean_dec(v_v_3874_);
v___x_3905_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0));
v___x_3906_ = lean_nat_add(v___x_3875_, v___x_3876_);
lean_dec(v___x_3875_);
v___x_3907_ = l_Nat_reprFast(v___x_3906_);
v___x_3908_ = lean_string_append(v___x_3905_, v___x_3907_);
lean_dec_ref(v___x_3907_);
v___x_3909_ = lean_box(0);
v___x_3910_ = l_Lean_Name_str___override(v___x_3909_, v___x_3908_);
v___y_3892_ = v_e_3901_;
v___y_3893_ = v___x_3910_;
goto v___jp_3891_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(lean_object** _args){
lean_object* v___x_3954_ = _args[0];
lean_object* v_v_3955_ = _args[1];
lean_object* v___x_3956_ = _args[2];
lean_object* v___x_3957_ = _args[3];
lean_object* v___x_3958_ = _args[4];
lean_object* v_motive_3959_ = _args[5];
lean_object* v___x_3960_ = _args[6];
lean_object* v___x_3961_ = _args[7];
lean_object* v___x_3962_ = _args[8];
lean_object* v_zs12_3963_ = _args[9];
lean_object* v_is_3964_ = _args[10];
lean_object* v_fields1_3965_ = _args[11];
lean_object* v_fields2_3966_ = _args[12];
lean_object* v___y_3967_ = _args[13];
lean_object* v___y_3968_ = _args[14];
lean_object* v___y_3969_ = _args[15];
lean_object* v___y_3970_ = _args[16];
lean_object* v___y_3971_ = _args[17];
_start:
{
uint8_t v___x_16312__boxed_3972_; uint8_t v___x_16313__boxed_3973_; uint8_t v___x_16314__boxed_3974_; lean_object* v_res_3975_; 
v___x_16312__boxed_3972_ = lean_unbox(v___x_3960_);
v___x_16313__boxed_3973_ = lean_unbox(v___x_3961_);
v___x_16314__boxed_3974_ = lean_unbox(v___x_3962_);
v_res_3975_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(v___x_3954_, v_v_3955_, v___x_3956_, v___x_3957_, v___x_3958_, v_motive_3959_, v___x_16312__boxed_3972_, v___x_16313__boxed_3973_, v___x_16314__boxed_3974_, v_zs12_3963_, v_is_3964_, v_fields1_3965_, v_fields2_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec(v___y_3968_);
lean_dec_ref(v___y_3967_);
lean_dec_ref(v_fields2_3966_);
lean_dec_ref(v_fields1_3965_);
lean_dec_ref(v_zs12_3963_);
lean_dec(v___x_3957_);
return v_res_3975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(lean_object* v_tail_3976_, lean_object* v_params_3977_, lean_object* v_motive_3978_, size_t v_sz_3979_, size_t v_i_3980_, lean_object* v_bs_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
uint8_t v___x_3987_; 
v___x_3987_ = lean_usize_dec_lt(v_i_3980_, v_sz_3979_);
if (v___x_3987_ == 0)
{
lean_object* v___x_3988_; 
lean_dec_ref(v_motive_3978_);
lean_dec(v_tail_3976_);
v___x_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3988_, 0, v_bs_3981_);
return v___x_3988_;
}
else
{
lean_object* v___x_3989_; lean_object* v___x_3990_; uint8_t v___x_3991_; uint8_t v___x_3992_; lean_object* v_v_3993_; lean_object* v_bs_x27_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___f_4001_; lean_object* v___x_4002_; 
v___x_3989_ = lean_unsigned_to_nat(0u);
v___x_3990_ = lean_unsigned_to_nat(1u);
v___x_3991_ = 0;
v___x_3992_ = 1;
v_v_3993_ = lean_array_uget(v_bs_3981_, v_i_3980_);
v_bs_x27_3994_ = lean_array_uset(v_bs_3981_, v_i_3980_, v___x_3989_);
v___x_3995_ = lean_usize_to_nat(v_i_3980_);
lean_inc(v_tail_3976_);
lean_inc(v_v_3993_);
v___x_3996_ = l_Lean_mkConst(v_v_3993_, v_tail_3976_);
v___x_3997_ = l_Lean_mkAppN(v___x_3996_, v_params_3977_);
v___x_3998_ = lean_box(v___x_3991_);
v___x_3999_ = lean_box(v___x_3987_);
v___x_4000_ = lean_box(v___x_3992_);
lean_inc_ref(v_motive_3978_);
lean_inc_ref(v___x_3997_);
v___f_4001_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed), 18, 9);
lean_closure_set(v___f_4001_, 0, v___x_3989_);
lean_closure_set(v___f_4001_, 1, v_v_3993_);
lean_closure_set(v___f_4001_, 2, v___x_3995_);
lean_closure_set(v___f_4001_, 3, v___x_3990_);
lean_closure_set(v___f_4001_, 4, v___x_3997_);
lean_closure_set(v___f_4001_, 5, v_motive_3978_);
lean_closure_set(v___f_4001_, 6, v___x_3998_);
lean_closure_set(v___f_4001_, 7, v___x_3999_);
lean_closure_set(v___f_4001_, 8, v___x_4000_);
v___x_4002_ = l_Lean_Meta_withSharedCtorIndices___redArg(v___x_3997_, v___f_4001_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_);
if (lean_obj_tag(v___x_4002_) == 0)
{
lean_object* v_a_4003_; size_t v___x_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
v_a_4003_ = lean_ctor_get(v___x_4002_, 0);
lean_inc(v_a_4003_);
lean_dec_ref_known(v___x_4002_, 1);
v___x_4004_ = ((size_t)1ULL);
v___x_4005_ = lean_usize_add(v_i_3980_, v___x_4004_);
v___x_4006_ = lean_array_uset(v_bs_x27_3994_, v_i_3980_, v_a_4003_);
v_i_3980_ = v___x_4005_;
v_bs_3981_ = v___x_4006_;
goto _start;
}
else
{
lean_object* v_a_4008_; lean_object* v___x_4010_; uint8_t v_isShared_4011_; uint8_t v_isSharedCheck_4015_; 
lean_dec_ref(v_bs_x27_3994_);
lean_dec_ref(v_motive_3978_);
lean_dec(v_tail_3976_);
v_a_4008_ = lean_ctor_get(v___x_4002_, 0);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_4002_);
if (v_isSharedCheck_4015_ == 0)
{
v___x_4010_ = v___x_4002_;
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
else
{
lean_inc(v_a_4008_);
lean_dec(v___x_4002_);
v___x_4010_ = lean_box(0);
v_isShared_4011_ = v_isSharedCheck_4015_;
goto v_resetjp_4009_;
}
v_resetjp_4009_:
{
lean_object* v___x_4013_; 
if (v_isShared_4011_ == 0)
{
v___x_4013_ = v___x_4010_;
goto v_reusejp_4012_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_a_4008_);
v___x_4013_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4012_;
}
v_reusejp_4012_:
{
return v___x_4013_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(lean_object* v_tail_4016_, lean_object* v_params_4017_, lean_object* v_motive_4018_, lean_object* v_sz_4019_, lean_object* v_i_4020_, lean_object* v_bs_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
size_t v_sz_boxed_4027_; size_t v_i_boxed_4028_; lean_object* v_res_4029_; 
v_sz_boxed_4027_ = lean_unbox_usize(v_sz_4019_);
lean_dec(v_sz_4019_);
v_i_boxed_4028_ = lean_unbox_usize(v_i_4020_);
lean_dec(v_i_4020_);
v_res_4029_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4016_, v_params_4017_, v_motive_4018_, v_sz_boxed_4027_, v_i_boxed_4028_, v_bs_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec_ref(v_params_4017_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6(lean_object* v_ctors_4032_, lean_object* v_tail_4033_, lean_object* v_params_4034_, lean_object* v_numIndices_4035_, lean_object* v___x_4036_, lean_object* v___x_4037_, uint8_t v___x_4038_, uint8_t v___x_4039_, uint8_t v___x_4040_, lean_object* v_is_4041_, lean_object* v___x_4042_, lean_object* v___x_4043_, lean_object* v___x_4044_, lean_object* v___x_4045_, lean_object* v___x_4046_, lean_object* v___x_4047_, lean_object* v_heq_4048_, lean_object* v_val_4049_, lean_object* v___x_4050_, lean_object* v_declName_4051_, lean_object* v_levelParams_4052_, lean_object* v___x_4053_, lean_object* v___x_4054_, lean_object* v_numParams_4055_, lean_object* v___x_4056_, lean_object* v_motive_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; size_t v_sz_4064_; size_t v___x_4065_; lean_object* v___x_4066_; 
v___x_4063_ = lean_array_mk(v_ctors_4032_);
v_sz_4064_ = lean_array_size(v___x_4063_);
v___x_4065_ = ((size_t)0ULL);
lean_inc_ref(v___x_4063_);
lean_inc_ref(v_motive_4057_);
lean_inc(v_tail_4033_);
v___x_4066_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4033_, v_params_4034_, v_motive_4057_, v_sz_4064_, v___x_4065_, v___x_4063_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4068_; lean_object* v_fst_4069_; lean_object* v_snd_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___f_4076_; uint8_t v___x_4077_; lean_object* v___x_4078_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v___x_4068_ = l_Array_unzip___redArg(v_a_4067_);
lean_dec(v_a_4067_);
v_fst_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_fst_4069_);
v_snd_4070_ = lean_ctor_get(v___x_4068_, 1);
lean_inc(v_snd_4070_);
lean_dec_ref(v___x_4068_);
v___x_4071_ = lean_box(v___x_4038_);
v___x_4072_ = lean_box(v___x_4039_);
v___x_4073_ = lean_box(v___x_4040_);
v___x_4074_ = lean_box_usize(v_sz_4064_);
v___x_4075_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed__const__1));
v___f_4076_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__5___boxed), 35, 29);
lean_closure_set(v___f_4076_, 0, v_numIndices_4035_);
lean_closure_set(v___f_4076_, 1, v___x_4036_);
lean_closure_set(v___f_4076_, 2, v_motive_4057_);
lean_closure_set(v___f_4076_, 3, v___x_4037_);
lean_closure_set(v___f_4076_, 4, v___x_4071_);
lean_closure_set(v___f_4076_, 5, v___x_4072_);
lean_closure_set(v___f_4076_, 6, v___x_4073_);
lean_closure_set(v___f_4076_, 7, v_is_4041_);
lean_closure_set(v___f_4076_, 8, v___x_4042_);
lean_closure_set(v___f_4076_, 9, v___x_4043_);
lean_closure_set(v___f_4076_, 10, v___x_4044_);
lean_closure_set(v___f_4076_, 11, v___x_4045_);
lean_closure_set(v___f_4076_, 12, v_params_4034_);
lean_closure_set(v___f_4076_, 13, v___x_4046_);
lean_closure_set(v___f_4076_, 14, v___x_4047_);
lean_closure_set(v___f_4076_, 15, v_heq_4048_);
lean_closure_set(v___f_4076_, 16, v_val_4049_);
lean_closure_set(v___f_4076_, 17, v_tail_4033_);
lean_closure_set(v___f_4076_, 18, v___x_4074_);
lean_closure_set(v___f_4076_, 19, v___x_4075_);
lean_closure_set(v___f_4076_, 20, v___x_4063_);
lean_closure_set(v___f_4076_, 21, v___x_4050_);
lean_closure_set(v___f_4076_, 22, v_declName_4051_);
lean_closure_set(v___f_4076_, 23, v_levelParams_4052_);
lean_closure_set(v___f_4076_, 24, v___x_4053_);
lean_closure_set(v___f_4076_, 25, v___x_4054_);
lean_closure_set(v___f_4076_, 26, v_numParams_4055_);
lean_closure_set(v___f_4076_, 27, v_snd_4070_);
lean_closure_set(v___f_4076_, 28, v___x_4056_);
v___x_4077_ = 0;
v___x_4078_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(v_fst_4069_, v___f_4076_, v___x_4077_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
return v___x_4078_;
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec_ref(v___x_4063_);
lean_dec_ref(v_motive_4057_);
lean_dec_ref(v___x_4056_);
lean_dec(v_numParams_4055_);
lean_dec(v___x_4054_);
lean_dec(v___x_4053_);
lean_dec(v_levelParams_4052_);
lean_dec(v_declName_4051_);
lean_dec_ref(v___x_4050_);
lean_dec_ref(v_val_4049_);
lean_dec_ref(v_heq_4048_);
lean_dec_ref(v___x_4047_);
lean_dec_ref(v___x_4046_);
lean_dec(v___x_4045_);
lean_dec(v___x_4044_);
lean_dec_ref(v___x_4043_);
lean_dec_ref(v___x_4042_);
lean_dec_ref(v_is_4041_);
lean_dec_ref(v___x_4037_);
lean_dec(v___x_4036_);
lean_dec(v_numIndices_4035_);
lean_dec_ref(v_params_4034_);
lean_dec(v_tail_4033_);
v_a_4079_ = lean_ctor_get(v___x_4066_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4066_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4066_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4066_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__6___boxed(lean_object** _args){
lean_object* v_ctors_4087_ = _args[0];
lean_object* v_tail_4088_ = _args[1];
lean_object* v_params_4089_ = _args[2];
lean_object* v_numIndices_4090_ = _args[3];
lean_object* v___x_4091_ = _args[4];
lean_object* v___x_4092_ = _args[5];
lean_object* v___x_4093_ = _args[6];
lean_object* v___x_4094_ = _args[7];
lean_object* v___x_4095_ = _args[8];
lean_object* v_is_4096_ = _args[9];
lean_object* v___x_4097_ = _args[10];
lean_object* v___x_4098_ = _args[11];
lean_object* v___x_4099_ = _args[12];
lean_object* v___x_4100_ = _args[13];
lean_object* v___x_4101_ = _args[14];
lean_object* v___x_4102_ = _args[15];
lean_object* v_heq_4103_ = _args[16];
lean_object* v_val_4104_ = _args[17];
lean_object* v___x_4105_ = _args[18];
lean_object* v_declName_4106_ = _args[19];
lean_object* v_levelParams_4107_ = _args[20];
lean_object* v___x_4108_ = _args[21];
lean_object* v___x_4109_ = _args[22];
lean_object* v_numParams_4110_ = _args[23];
lean_object* v___x_4111_ = _args[24];
lean_object* v_motive_4112_ = _args[25];
lean_object* v___y_4113_ = _args[26];
lean_object* v___y_4114_ = _args[27];
lean_object* v___y_4115_ = _args[28];
lean_object* v___y_4116_ = _args[29];
lean_object* v___y_4117_ = _args[30];
_start:
{
uint8_t v___x_16549__boxed_4118_; uint8_t v___x_16550__boxed_4119_; uint8_t v___x_16551__boxed_4120_; lean_object* v_res_4121_; 
v___x_16549__boxed_4118_ = lean_unbox(v___x_4093_);
v___x_16550__boxed_4119_ = lean_unbox(v___x_4094_);
v___x_16551__boxed_4120_ = lean_unbox(v___x_4095_);
v_res_4121_ = l_Lean_mkCasesOnSameCtor___lam__6(v_ctors_4087_, v_tail_4088_, v_params_4089_, v_numIndices_4090_, v___x_4091_, v___x_4092_, v___x_16549__boxed_4118_, v___x_16550__boxed_4119_, v___x_16551__boxed_4120_, v_is_4096_, v___x_4097_, v___x_4098_, v___x_4099_, v___x_4100_, v___x_4101_, v___x_4102_, v_heq_4103_, v_val_4104_, v___x_4105_, v_declName_4106_, v_levelParams_4107_, v___x_4108_, v___x_4109_, v_numParams_4110_, v___x_4111_, v_motive_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7(lean_object* v___x_4122_, lean_object* v___x_4123_, lean_object* v_is_4124_, lean_object* v_head_4125_, lean_object* v_ctors_4126_, lean_object* v_tail_4127_, lean_object* v_params_4128_, lean_object* v_numIndices_4129_, lean_object* v___x_4130_, lean_object* v___x_4131_, lean_object* v___x_4132_, lean_object* v___x_4133_, lean_object* v___x_4134_, lean_object* v_val_4135_, lean_object* v___x_4136_, lean_object* v_declName_4137_, lean_object* v_levelParams_4138_, lean_object* v___x_4139_, lean_object* v_numParams_4140_, lean_object* v___x_4141_, lean_object* v_heq_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; uint8_t v___x_4155_; uint8_t v___x_4156_; uint8_t v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___f_4161_; lean_object* v___x_4162_; 
v___x_4148_ = lean_unsigned_to_nat(3u);
v___x_4149_ = lean_mk_empty_array_with_capacity(v___x_4148_);
lean_inc_ref(v___x_4122_);
v___x_4150_ = lean_array_push(v___x_4149_, v___x_4122_);
lean_inc_ref(v___x_4123_);
v___x_4151_ = lean_array_push(v___x_4150_, v___x_4123_);
lean_inc_ref(v_heq_4142_);
v___x_4152_ = lean_array_push(v___x_4151_, v_heq_4142_);
lean_inc_ref(v_is_4124_);
v___x_4153_ = l_Array_append___redArg(v_is_4124_, v___x_4152_);
lean_dec_ref(v___x_4152_);
v___x_4154_ = l_Lean_mkSort(v_head_4125_);
v___x_4155_ = 0;
v___x_4156_ = 1;
v___x_4157_ = 1;
v___x_4158_ = lean_box(v___x_4155_);
v___x_4159_ = lean_box(v___x_4156_);
v___x_4160_ = lean_box(v___x_4157_);
lean_inc_ref(v___x_4153_);
v___f_4161_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__6___boxed), 31, 25);
lean_closure_set(v___f_4161_, 0, v_ctors_4126_);
lean_closure_set(v___f_4161_, 1, v_tail_4127_);
lean_closure_set(v___f_4161_, 2, v_params_4128_);
lean_closure_set(v___f_4161_, 3, v_numIndices_4129_);
lean_closure_set(v___f_4161_, 4, v___x_4130_);
lean_closure_set(v___f_4161_, 5, v___x_4153_);
lean_closure_set(v___f_4161_, 6, v___x_4158_);
lean_closure_set(v___f_4161_, 7, v___x_4159_);
lean_closure_set(v___f_4161_, 8, v___x_4160_);
lean_closure_set(v___f_4161_, 9, v_is_4124_);
lean_closure_set(v___f_4161_, 10, v___x_4123_);
lean_closure_set(v___f_4161_, 11, v___x_4122_);
lean_closure_set(v___f_4161_, 12, v___x_4131_);
lean_closure_set(v___f_4161_, 13, v___x_4132_);
lean_closure_set(v___f_4161_, 14, v___x_4133_);
lean_closure_set(v___f_4161_, 15, v___x_4134_);
lean_closure_set(v___f_4161_, 16, v_heq_4142_);
lean_closure_set(v___f_4161_, 17, v_val_4135_);
lean_closure_set(v___f_4161_, 18, v___x_4136_);
lean_closure_set(v___f_4161_, 19, v_declName_4137_);
lean_closure_set(v___f_4161_, 20, v_levelParams_4138_);
lean_closure_set(v___f_4161_, 21, v___x_4148_);
lean_closure_set(v___f_4161_, 22, v___x_4139_);
lean_closure_set(v___f_4161_, 23, v_numParams_4140_);
lean_closure_set(v___f_4161_, 24, v___x_4141_);
v___x_4162_ = l_Lean_Meta_mkForallFVars(v___x_4153_, v___x_4154_, v___x_4155_, v___x_4156_, v___x_4156_, v___x_4157_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec_ref(v___x_4153_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; lean_object* v___x_4166_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
lean_inc(v_a_4163_);
lean_dec_ref_known(v___x_4162_, 1);
v___x_4164_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1));
v___x_4165_ = 0;
v___x_4166_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_4164_, v___x_4157_, v_a_4163_, v___f_4161_, v___x_4165_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
return v___x_4166_;
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_dec_ref(v___f_4161_);
v_a_4167_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4162_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4162_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__7___boxed(lean_object** _args){
lean_object* v___x_4175_ = _args[0];
lean_object* v___x_4176_ = _args[1];
lean_object* v_is_4177_ = _args[2];
lean_object* v_head_4178_ = _args[3];
lean_object* v_ctors_4179_ = _args[4];
lean_object* v_tail_4180_ = _args[5];
lean_object* v_params_4181_ = _args[6];
lean_object* v_numIndices_4182_ = _args[7];
lean_object* v___x_4183_ = _args[8];
lean_object* v___x_4184_ = _args[9];
lean_object* v___x_4185_ = _args[10];
lean_object* v___x_4186_ = _args[11];
lean_object* v___x_4187_ = _args[12];
lean_object* v_val_4188_ = _args[13];
lean_object* v___x_4189_ = _args[14];
lean_object* v_declName_4190_ = _args[15];
lean_object* v_levelParams_4191_ = _args[16];
lean_object* v___x_4192_ = _args[17];
lean_object* v_numParams_4193_ = _args[18];
lean_object* v___x_4194_ = _args[19];
lean_object* v_heq_4195_ = _args[20];
lean_object* v___y_4196_ = _args[21];
lean_object* v___y_4197_ = _args[22];
lean_object* v___y_4198_ = _args[23];
lean_object* v___y_4199_ = _args[24];
lean_object* v___y_4200_ = _args[25];
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_mkCasesOnSameCtor___lam__7(v___x_4175_, v___x_4176_, v_is_4177_, v_head_4178_, v_ctors_4179_, v_tail_4180_, v_params_4181_, v_numIndices_4182_, v___x_4183_, v___x_4184_, v___x_4185_, v___x_4186_, v___x_4187_, v_val_4188_, v___x_4189_, v_declName_4190_, v_levelParams_4191_, v___x_4192_, v_numParams_4193_, v___x_4194_, v_heq_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8(lean_object* v___x_4202_, lean_object* v_x1_4203_, lean_object* v_indName_4204_, lean_object* v_tail_4205_, lean_object* v_params_4206_, lean_object* v_is_4207_, lean_object* v___x_4208_, lean_object* v_head_4209_, lean_object* v_ctors_4210_, lean_object* v_numIndices_4211_, lean_object* v___x_4212_, lean_object* v___x_4213_, lean_object* v_val_4214_, lean_object* v_declName_4215_, lean_object* v_levelParams_4216_, lean_object* v_numParams_4217_, lean_object* v___x_4218_, lean_object* v_x2_4219_, lean_object* v_x_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___f_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4226_ = lean_unsigned_to_nat(0u);
v___x_4227_ = lean_array_get_borrowed(v___x_4202_, v_x1_4203_, v___x_4226_);
v___x_4228_ = lean_array_get_borrowed(v___x_4202_, v_x2_4219_, v___x_4226_);
v___x_4229_ = l_Lean_mkCtorIdxName(v_indName_4204_);
lean_inc(v_tail_4205_);
v___x_4230_ = l_Lean_mkConst(v___x_4229_, v_tail_4205_);
lean_inc_ref(v_params_4206_);
v___x_4231_ = l_Array_append___redArg(v_params_4206_, v_is_4207_);
v___x_4232_ = lean_mk_empty_array_with_capacity(v___x_4208_);
lean_inc_n(v___x_4227_, 2);
lean_inc_ref_n(v___x_4232_, 2);
v___x_4233_ = lean_array_push(v___x_4232_, v___x_4227_);
lean_inc_ref(v___x_4231_);
v___x_4234_ = l_Array_append___redArg(v___x_4231_, v___x_4233_);
lean_inc_ref(v___x_4230_);
v___x_4235_ = l_Lean_mkAppN(v___x_4230_, v___x_4234_);
lean_dec_ref(v___x_4234_);
lean_inc_n(v___x_4228_, 2);
v___x_4236_ = lean_array_push(v___x_4232_, v___x_4228_);
lean_inc_ref(v___x_4236_);
v___f_4237_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__7___boxed), 26, 20);
lean_closure_set(v___f_4237_, 0, v___x_4227_);
lean_closure_set(v___f_4237_, 1, v___x_4228_);
lean_closure_set(v___f_4237_, 2, v_is_4207_);
lean_closure_set(v___f_4237_, 3, v_head_4209_);
lean_closure_set(v___f_4237_, 4, v_ctors_4210_);
lean_closure_set(v___f_4237_, 5, v_tail_4205_);
lean_closure_set(v___f_4237_, 6, v_params_4206_);
lean_closure_set(v___f_4237_, 7, v_numIndices_4211_);
lean_closure_set(v___f_4237_, 8, v___x_4208_);
lean_closure_set(v___f_4237_, 9, v___x_4212_);
lean_closure_set(v___f_4237_, 10, v___x_4213_);
lean_closure_set(v___f_4237_, 11, v___x_4233_);
lean_closure_set(v___f_4237_, 12, v___x_4236_);
lean_closure_set(v___f_4237_, 13, v_val_4214_);
lean_closure_set(v___f_4237_, 14, v___x_4232_);
lean_closure_set(v___f_4237_, 15, v_declName_4215_);
lean_closure_set(v___f_4237_, 16, v_levelParams_4216_);
lean_closure_set(v___f_4237_, 17, v___x_4226_);
lean_closure_set(v___f_4237_, 18, v_numParams_4217_);
lean_closure_set(v___f_4237_, 19, v___x_4218_);
v___x_4238_ = l_Array_append___redArg(v___x_4231_, v___x_4236_);
lean_dec_ref(v___x_4236_);
v___x_4239_ = l_Lean_mkAppN(v___x_4230_, v___x_4238_);
lean_dec_ref(v___x_4238_);
v___x_4240_ = l_Lean_Meta_mkEq(v___x_4235_, v___x_4239_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref_known(v___x_4240_, 1);
v___x_4242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1));
v___x_4243_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_4242_, v_a_4241_, v___f_4237_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
return v___x_4243_;
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec_ref(v___f_4237_);
v_a_4244_ = lean_ctor_get(v___x_4240_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4240_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4240_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4240_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__8___boxed(lean_object** _args){
lean_object* v___x_4252_ = _args[0];
lean_object* v_x1_4253_ = _args[1];
lean_object* v_indName_4254_ = _args[2];
lean_object* v_tail_4255_ = _args[3];
lean_object* v_params_4256_ = _args[4];
lean_object* v_is_4257_ = _args[5];
lean_object* v___x_4258_ = _args[6];
lean_object* v_head_4259_ = _args[7];
lean_object* v_ctors_4260_ = _args[8];
lean_object* v_numIndices_4261_ = _args[9];
lean_object* v___x_4262_ = _args[10];
lean_object* v___x_4263_ = _args[11];
lean_object* v_val_4264_ = _args[12];
lean_object* v_declName_4265_ = _args[13];
lean_object* v_levelParams_4266_ = _args[14];
lean_object* v_numParams_4267_ = _args[15];
lean_object* v___x_4268_ = _args[16];
lean_object* v_x2_4269_ = _args[17];
lean_object* v_x_4270_ = _args[18];
lean_object* v___y_4271_ = _args[19];
lean_object* v___y_4272_ = _args[20];
lean_object* v___y_4273_ = _args[21];
lean_object* v___y_4274_ = _args[22];
lean_object* v___y_4275_ = _args[23];
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_mkCasesOnSameCtor___lam__8(v___x_4252_, v_x1_4253_, v_indName_4254_, v_tail_4255_, v_params_4256_, v_is_4257_, v___x_4258_, v_head_4259_, v_ctors_4260_, v_numIndices_4261_, v___x_4262_, v___x_4263_, v_val_4264_, v_declName_4265_, v_levelParams_4266_, v_numParams_4267_, v___x_4268_, v_x2_4269_, v_x_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
lean_dec_ref(v_x_4270_);
lean_dec_ref(v_x2_4269_);
lean_dec_ref(v_x1_4253_);
lean_dec_ref(v___x_4252_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9(lean_object* v___x_4277_, lean_object* v_indName_4278_, lean_object* v_tail_4279_, lean_object* v_params_4280_, lean_object* v_is_4281_, lean_object* v___x_4282_, lean_object* v_head_4283_, lean_object* v_ctors_4284_, lean_object* v_numIndices_4285_, lean_object* v___x_4286_, lean_object* v___x_4287_, lean_object* v_val_4288_, lean_object* v_declName_4289_, lean_object* v_levelParams_4290_, lean_object* v_numParams_4291_, lean_object* v___x_4292_, lean_object* v_t_4293_, lean_object* v___x_4294_, lean_object* v_x1_4295_, lean_object* v_x_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
lean_object* v___f_4302_; uint8_t v___x_4303_; lean_object* v___x_4304_; 
v___f_4302_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__8___boxed), 24, 17);
lean_closure_set(v___f_4302_, 0, v___x_4277_);
lean_closure_set(v___f_4302_, 1, v_x1_4295_);
lean_closure_set(v___f_4302_, 2, v_indName_4278_);
lean_closure_set(v___f_4302_, 3, v_tail_4279_);
lean_closure_set(v___f_4302_, 4, v_params_4280_);
lean_closure_set(v___f_4302_, 5, v_is_4281_);
lean_closure_set(v___f_4302_, 6, v___x_4282_);
lean_closure_set(v___f_4302_, 7, v_head_4283_);
lean_closure_set(v___f_4302_, 8, v_ctors_4284_);
lean_closure_set(v___f_4302_, 9, v_numIndices_4285_);
lean_closure_set(v___f_4302_, 10, v___x_4286_);
lean_closure_set(v___f_4302_, 11, v___x_4287_);
lean_closure_set(v___f_4302_, 12, v_val_4288_);
lean_closure_set(v___f_4302_, 13, v_declName_4289_);
lean_closure_set(v___f_4302_, 14, v_levelParams_4290_);
lean_closure_set(v___f_4302_, 15, v_numParams_4291_);
lean_closure_set(v___f_4302_, 16, v___x_4292_);
v___x_4303_ = 0;
v___x_4304_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4293_, v___x_4294_, v___f_4302_, v___x_4303_, v___x_4303_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
return v___x_4304_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__9___boxed(lean_object** _args){
lean_object* v___x_4305_ = _args[0];
lean_object* v_indName_4306_ = _args[1];
lean_object* v_tail_4307_ = _args[2];
lean_object* v_params_4308_ = _args[3];
lean_object* v_is_4309_ = _args[4];
lean_object* v___x_4310_ = _args[5];
lean_object* v_head_4311_ = _args[6];
lean_object* v_ctors_4312_ = _args[7];
lean_object* v_numIndices_4313_ = _args[8];
lean_object* v___x_4314_ = _args[9];
lean_object* v___x_4315_ = _args[10];
lean_object* v_val_4316_ = _args[11];
lean_object* v_declName_4317_ = _args[12];
lean_object* v_levelParams_4318_ = _args[13];
lean_object* v_numParams_4319_ = _args[14];
lean_object* v___x_4320_ = _args[15];
lean_object* v_t_4321_ = _args[16];
lean_object* v___x_4322_ = _args[17];
lean_object* v_x1_4323_ = _args[18];
lean_object* v_x_4324_ = _args[19];
lean_object* v___y_4325_ = _args[20];
lean_object* v___y_4326_ = _args[21];
lean_object* v___y_4327_ = _args[22];
lean_object* v___y_4328_ = _args[23];
lean_object* v___y_4329_ = _args[24];
_start:
{
lean_object* v_res_4330_; 
v_res_4330_ = l_Lean_mkCasesOnSameCtor___lam__9(v___x_4305_, v_indName_4306_, v_tail_4307_, v_params_4308_, v_is_4309_, v___x_4310_, v_head_4311_, v_ctors_4312_, v_numIndices_4313_, v___x_4314_, v___x_4315_, v_val_4316_, v_declName_4317_, v_levelParams_4318_, v_numParams_4319_, v___x_4320_, v_t_4321_, v___x_4322_, v_x1_4323_, v_x_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec(v___y_4326_);
lean_dec_ref(v___y_4325_);
lean_dec_ref(v_x_4324_);
return v_res_4330_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10(lean_object* v___x_4331_, lean_object* v_indName_4332_, lean_object* v_tail_4333_, lean_object* v_params_4334_, lean_object* v_head_4335_, lean_object* v_ctors_4336_, lean_object* v_numIndices_4337_, lean_object* v___x_4338_, lean_object* v___x_4339_, lean_object* v_val_4340_, lean_object* v_declName_4341_, lean_object* v_levelParams_4342_, lean_object* v_numParams_4343_, lean_object* v___x_4344_, lean_object* v_is_4345_, lean_object* v_t_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___f_4354_; uint8_t v___x_4355_; lean_object* v___x_4356_; 
v___x_4352_ = lean_unsigned_to_nat(1u);
v___x_4353_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0));
lean_inc_ref(v_t_4346_);
v___f_4354_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__9___boxed), 25, 18);
lean_closure_set(v___f_4354_, 0, v___x_4331_);
lean_closure_set(v___f_4354_, 1, v_indName_4332_);
lean_closure_set(v___f_4354_, 2, v_tail_4333_);
lean_closure_set(v___f_4354_, 3, v_params_4334_);
lean_closure_set(v___f_4354_, 4, v_is_4345_);
lean_closure_set(v___f_4354_, 5, v___x_4352_);
lean_closure_set(v___f_4354_, 6, v_head_4335_);
lean_closure_set(v___f_4354_, 7, v_ctors_4336_);
lean_closure_set(v___f_4354_, 8, v_numIndices_4337_);
lean_closure_set(v___f_4354_, 9, v___x_4338_);
lean_closure_set(v___f_4354_, 10, v___x_4339_);
lean_closure_set(v___f_4354_, 11, v_val_4340_);
lean_closure_set(v___f_4354_, 12, v_declName_4341_);
lean_closure_set(v___f_4354_, 13, v_levelParams_4342_);
lean_closure_set(v___f_4354_, 14, v_numParams_4343_);
lean_closure_set(v___f_4354_, 15, v___x_4344_);
lean_closure_set(v___f_4354_, 16, v_t_4346_);
lean_closure_set(v___f_4354_, 17, v___x_4353_);
v___x_4355_ = 0;
v___x_4356_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_t_4346_, v___x_4353_, v___f_4354_, v___x_4355_, v___x_4355_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__10___boxed(lean_object** _args){
lean_object* v___x_4357_ = _args[0];
lean_object* v_indName_4358_ = _args[1];
lean_object* v_tail_4359_ = _args[2];
lean_object* v_params_4360_ = _args[3];
lean_object* v_head_4361_ = _args[4];
lean_object* v_ctors_4362_ = _args[5];
lean_object* v_numIndices_4363_ = _args[6];
lean_object* v___x_4364_ = _args[7];
lean_object* v___x_4365_ = _args[8];
lean_object* v_val_4366_ = _args[9];
lean_object* v_declName_4367_ = _args[10];
lean_object* v_levelParams_4368_ = _args[11];
lean_object* v_numParams_4369_ = _args[12];
lean_object* v___x_4370_ = _args[13];
lean_object* v_is_4371_ = _args[14];
lean_object* v_t_4372_ = _args[15];
lean_object* v___y_4373_ = _args[16];
lean_object* v___y_4374_ = _args[17];
lean_object* v___y_4375_ = _args[18];
lean_object* v___y_4376_ = _args[19];
lean_object* v___y_4377_ = _args[20];
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_mkCasesOnSameCtor___lam__10(v___x_4357_, v_indName_4358_, v_tail_4359_, v_params_4360_, v_head_4361_, v_ctors_4362_, v_numIndices_4363_, v___x_4364_, v___x_4365_, v_val_4366_, v_declName_4367_, v_levelParams_4368_, v_numParams_4369_, v___x_4370_, v_is_4371_, v_t_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11(lean_object* v___x_4379_, lean_object* v_indName_4380_, lean_object* v_tail_4381_, lean_object* v_head_4382_, lean_object* v_ctors_4383_, lean_object* v_numIndices_4384_, lean_object* v___x_4385_, lean_object* v___x_4386_, lean_object* v_val_4387_, lean_object* v_declName_4388_, lean_object* v_levelParams_4389_, lean_object* v_numParams_4390_, lean_object* v_params_4391_, lean_object* v_t_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4398_; lean_object* v___f_4399_; lean_object* v___x_4400_; uint8_t v___x_4401_; lean_object* v___x_4402_; 
v___x_4398_ = l_Lean_Expr_bindingBody_x21(v_t_4392_);
lean_inc_ref(v___x_4398_);
lean_inc(v_numIndices_4384_);
v___f_4399_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__10___boxed), 21, 14);
lean_closure_set(v___f_4399_, 0, v___x_4379_);
lean_closure_set(v___f_4399_, 1, v_indName_4380_);
lean_closure_set(v___f_4399_, 2, v_tail_4381_);
lean_closure_set(v___f_4399_, 3, v_params_4391_);
lean_closure_set(v___f_4399_, 4, v_head_4382_);
lean_closure_set(v___f_4399_, 5, v_ctors_4383_);
lean_closure_set(v___f_4399_, 6, v_numIndices_4384_);
lean_closure_set(v___f_4399_, 7, v___x_4385_);
lean_closure_set(v___f_4399_, 8, v___x_4386_);
lean_closure_set(v___f_4399_, 9, v_val_4387_);
lean_closure_set(v___f_4399_, 10, v_declName_4388_);
lean_closure_set(v___f_4399_, 11, v_levelParams_4389_);
lean_closure_set(v___f_4399_, 12, v_numParams_4390_);
lean_closure_set(v___f_4399_, 13, v___x_4398_);
v___x_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4400_, 0, v_numIndices_4384_);
v___x_4401_ = 0;
v___x_4402_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v___x_4398_, v___x_4400_, v___f_4399_, v___x_4401_, v___x_4401_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
return v___x_4402_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___lam__11___boxed(lean_object** _args){
lean_object* v___x_4403_ = _args[0];
lean_object* v_indName_4404_ = _args[1];
lean_object* v_tail_4405_ = _args[2];
lean_object* v_head_4406_ = _args[3];
lean_object* v_ctors_4407_ = _args[4];
lean_object* v_numIndices_4408_ = _args[5];
lean_object* v___x_4409_ = _args[6];
lean_object* v___x_4410_ = _args[7];
lean_object* v_val_4411_ = _args[8];
lean_object* v_declName_4412_ = _args[9];
lean_object* v_levelParams_4413_ = _args[10];
lean_object* v_numParams_4414_ = _args[11];
lean_object* v_params_4415_ = _args[12];
lean_object* v_t_4416_ = _args[13];
lean_object* v___y_4417_ = _args[14];
lean_object* v___y_4418_ = _args[15];
lean_object* v___y_4419_ = _args[16];
lean_object* v___y_4420_ = _args[17];
lean_object* v___y_4421_ = _args[18];
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l_Lean_mkCasesOnSameCtor___lam__11(v___x_4403_, v_indName_4404_, v_tail_4405_, v_head_4406_, v_ctors_4407_, v_numIndices_4408_, v___x_4409_, v___x_4410_, v_val_4411_, v_declName_4412_, v_levelParams_4413_, v_numParams_4414_, v_params_4415_, v_t_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec_ref(v_t_4416_);
return v_res_4422_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__3(void){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4427_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__2));
v___x_4428_ = lean_unsigned_to_nat(58u);
v___x_4429_ = lean_unsigned_to_nat(142u);
v___x_4430_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4431_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4432_ = l_mkPanicMessageWithDecl(v___x_4431_, v___x_4430_, v___x_4429_, v___x_4428_, v___x_4427_);
return v___x_4432_;
}
}
static lean_object* _init_l_Lean_mkCasesOnSameCtor___closed__4(void){
_start:
{
lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4433_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__4));
v___x_4434_ = lean_unsigned_to_nat(60u);
v___x_4435_ = lean_unsigned_to_nat(136u);
v___x_4436_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__2));
v___x_4437_ = ((lean_object*)(l_Lean_mkCasesOnSameCtorHet___closed__0));
v___x_4438_ = l_mkPanicMessageWithDecl(v___x_4437_, v___x_4436_, v___x_4435_, v___x_4434_, v___x_4433_);
return v___x_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor(lean_object* v_declName_4439_, lean_object* v_indName_4440_, lean_object* v_a_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_){
_start:
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4446_ = l_Lean_instInhabitedExpr;
lean_inc(v_indName_4440_);
v___x_4447_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(v_indName_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
lean_dec_ref_known(v___x_4447_, 1);
if (lean_obj_tag(v_a_4448_) == 5)
{
lean_object* v_val_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v_val_4449_ = lean_ctor_get(v_a_4448_, 0);
lean_inc_ref(v_val_4449_);
lean_dec_ref_known(v_a_4448_, 1);
v___x_4450_ = ((lean_object*)(l_Lean_mkCasesOnSameCtor___closed__1));
lean_inc(v_declName_4439_);
v___x_4451_ = l_Lean_Name_append(v_declName_4439_, v___x_4450_);
lean_inc(v_indName_4440_);
lean_inc(v___x_4451_);
v___x_4452_ = l_Lean_mkCasesOnSameCtorHet(v___x_4451_, v_indName_4440_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4484_; 
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4484_ == 0)
{
lean_object* v_unused_4485_; 
v_unused_4485_ = lean_ctor_get(v___x_4452_, 0);
lean_dec(v_unused_4485_);
v___x_4454_ = v___x_4452_;
v_isShared_4455_ = v_isSharedCheck_4484_;
goto v_resetjp_4453_;
}
else
{
lean_dec(v___x_4452_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4484_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4456_; lean_object* v___x_4457_; 
lean_inc(v_indName_4440_);
v___x_4456_ = l_Lean_mkCasesOnName(v_indName_4440_);
v___x_4457_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(v___x_4456_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
if (lean_obj_tag(v___x_4457_) == 0)
{
lean_object* v_a_4458_; lean_object* v_levelParams_4459_; lean_object* v_type_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; 
v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
lean_inc(v_a_4458_);
lean_dec_ref_known(v___x_4457_, 1);
v_levelParams_4459_ = lean_ctor_get(v_a_4458_, 1);
lean_inc_n(v_levelParams_4459_, 2);
v_type_4460_ = lean_ctor_get(v_a_4458_, 2);
lean_inc_ref(v_type_4460_);
lean_dec(v_a_4458_);
v___x_4461_ = lean_box(0);
v___x_4462_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(v_levelParams_4459_, v___x_4461_);
if (lean_obj_tag(v___x_4462_) == 1)
{
lean_object* v_head_4463_; lean_object* v_tail_4464_; lean_object* v_numParams_4465_; lean_object* v_numIndices_4466_; lean_object* v_ctors_4467_; lean_object* v___f_4468_; lean_object* v___x_4470_; 
v_head_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc(v_head_4463_);
v_tail_4464_ = lean_ctor_get(v___x_4462_, 1);
lean_inc(v_tail_4464_);
v_numParams_4465_ = lean_ctor_get(v_val_4449_, 1);
lean_inc_n(v_numParams_4465_, 2);
v_numIndices_4466_ = lean_ctor_get(v_val_4449_, 2);
lean_inc(v_numIndices_4466_);
v_ctors_4467_ = lean_ctor_get(v_val_4449_, 4);
lean_inc(v_ctors_4467_);
v___f_4468_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnSameCtor___lam__11___boxed), 19, 12);
lean_closure_set(v___f_4468_, 0, v___x_4446_);
lean_closure_set(v___f_4468_, 1, v_indName_4440_);
lean_closure_set(v___f_4468_, 2, v_tail_4464_);
lean_closure_set(v___f_4468_, 3, v_head_4463_);
lean_closure_set(v___f_4468_, 4, v_ctors_4467_);
lean_closure_set(v___f_4468_, 5, v_numIndices_4466_);
lean_closure_set(v___f_4468_, 6, v___x_4451_);
lean_closure_set(v___f_4468_, 7, v___x_4462_);
lean_closure_set(v___f_4468_, 8, v_val_4449_);
lean_closure_set(v___f_4468_, 9, v_declName_4439_);
lean_closure_set(v___f_4468_, 10, v_levelParams_4459_);
lean_closure_set(v___f_4468_, 11, v_numParams_4465_);
if (v_isShared_4455_ == 0)
{
lean_ctor_set_tag(v___x_4454_, 1);
lean_ctor_set(v___x_4454_, 0, v_numParams_4465_);
v___x_4470_ = v___x_4454_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_numParams_4465_);
v___x_4470_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
uint8_t v___x_4471_; lean_object* v___x_4472_; 
v___x_4471_ = 0;
v___x_4472_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_4460_, v___x_4470_, v___f_4468_, v___x_4471_, v___x_4471_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
return v___x_4472_;
}
}
else
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
lean_dec(v___x_4462_);
lean_dec_ref(v_type_4460_);
lean_dec(v_levelParams_4459_);
lean_del_object(v___x_4454_);
lean_dec(v___x_4451_);
lean_dec_ref(v_val_4449_);
lean_dec(v_indName_4440_);
lean_dec(v_declName_4439_);
v___x_4474_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__3, &l_Lean_mkCasesOnSameCtor___closed__3_once, _init_l_Lean_mkCasesOnSameCtor___closed__3);
v___x_4475_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_4474_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
return v___x_4475_;
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_del_object(v___x_4454_);
lean_dec(v___x_4451_);
lean_dec_ref(v_val_4449_);
lean_dec(v_indName_4440_);
lean_dec(v_declName_4439_);
v_a_4476_ = lean_ctor_get(v___x_4457_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4457_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4457_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4457_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
}
else
{
lean_dec(v___x_4451_);
lean_dec_ref(v_val_4449_);
lean_dec(v_indName_4440_);
lean_dec(v_declName_4439_);
return v___x_4452_;
}
}
else
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
lean_dec(v_a_4448_);
lean_dec(v_indName_4440_);
lean_dec(v_declName_4439_);
v___x_4486_ = lean_obj_once(&l_Lean_mkCasesOnSameCtor___closed__4, &l_Lean_mkCasesOnSameCtor___closed__4_once, _init_l_Lean_mkCasesOnSameCtor___closed__4);
v___x_4487_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__15(v___x_4486_, v_a_4441_, v_a_4442_, v_a_4443_, v_a_4444_);
return v___x_4487_;
}
}
else
{
lean_object* v_a_4488_; lean_object* v___x_4490_; uint8_t v_isShared_4491_; uint8_t v_isSharedCheck_4495_; 
lean_dec(v_indName_4440_);
lean_dec(v_declName_4439_);
v_a_4488_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4490_ = v___x_4447_;
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
else
{
lean_inc(v_a_4488_);
lean_dec(v___x_4447_);
v___x_4490_ = lean_box(0);
v_isShared_4491_ = v_isSharedCheck_4495_;
goto v_resetjp_4489_;
}
v_resetjp_4489_:
{
lean_object* v___x_4493_; 
if (v_isShared_4491_ == 0)
{
v___x_4493_ = v___x_4490_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnSameCtor___boxed(lean_object* v_declName_4496_, lean_object* v_indName_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v_a_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_mkCasesOnSameCtor(v_declName_4496_, v_indName_4497_, v_a_4498_, v_a_4499_, v_a_4500_, v_a_4501_);
lean_dec(v_a_4501_);
lean_dec_ref(v_a_4500_);
lean_dec(v_a_4499_);
lean_dec_ref(v_a_4498_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(lean_object* v_tail_4504_, lean_object* v_params_4505_, lean_object* v_motive_4506_, lean_object* v_as_4507_, size_t v_sz_4508_, size_t v_i_4509_, lean_object* v_bs_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(v_tail_4504_, v_params_4505_, v_motive_4506_, v_sz_4508_, v_i_4509_, v_bs_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(lean_object* v_tail_4517_, lean_object* v_params_4518_, lean_object* v_motive_4519_, lean_object* v_as_4520_, lean_object* v_sz_4521_, lean_object* v_i_4522_, lean_object* v_bs_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
size_t v_sz_boxed_4529_; size_t v_i_boxed_4530_; lean_object* v_res_4531_; 
v_sz_boxed_4529_ = lean_unbox_usize(v_sz_4521_);
lean_dec(v_sz_4521_);
v_i_boxed_4530_ = lean_unbox_usize(v_i_4522_);
lean_dec(v_i_4522_);
v_res_4531_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__0(v_tail_4517_, v_params_4518_, v_motive_4519_, v_as_4520_, v_sz_boxed_4529_, v_i_boxed_4530_, v_bs_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
lean_dec(v___y_4527_);
lean_dec_ref(v___y_4526_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec_ref(v_as_4520_);
lean_dec_ref(v_params_4518_);
return v_res_4531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(lean_object* v_tail_4532_, lean_object* v_params_4533_, lean_object* v_a_4534_, lean_object* v_snd_4535_, lean_object* v_alts_4536_, lean_object* v_as_4537_, size_t v_sz_4538_, size_t v_i_4539_, lean_object* v_bs_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_){
_start:
{
lean_object* v___x_4546_; 
v___x_4546_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(v_tail_4532_, v_params_4533_, v_a_4534_, v_snd_4535_, v_alts_4536_, v_sz_4538_, v_i_4539_, v_bs_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
return v___x_4546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(lean_object* v_tail_4547_, lean_object* v_params_4548_, lean_object* v_a_4549_, lean_object* v_snd_4550_, lean_object* v_alts_4551_, lean_object* v_as_4552_, lean_object* v_sz_4553_, lean_object* v_i_4554_, lean_object* v_bs_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
size_t v_sz_boxed_4561_; size_t v_i_boxed_4562_; lean_object* v_res_4563_; 
v_sz_boxed_4561_ = lean_unbox_usize(v_sz_4553_);
lean_dec(v_sz_4553_);
v_i_boxed_4562_ = lean_unbox_usize(v_i_4554_);
lean_dec(v_i_4554_);
v_res_4563_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_mkCasesOnSameCtor_spec__2(v_tail_4547_, v_params_4548_, v_a_4549_, v_snd_4550_, v_alts_4551_, v_as_4552_, v_sz_boxed_4561_, v_i_boxed_4562_, v_bs_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
lean_dec(v___y_4559_);
lean_dec_ref(v___y_4558_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec_ref(v_as_4552_);
lean_dec_ref(v_params_4548_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(lean_object* v_matcherName_4564_, lean_object* v_info_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v___x_4571_; 
v___x_4571_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_matcherName_4564_, v_info_4565_, v___y_4567_, v___y_4569_);
return v___x_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(lean_object* v_matcherName_4572_, lean_object* v_info_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_res_4579_; 
v_res_4579_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(v_matcherName_4572_, v_info_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
lean_dec(v___y_4577_);
lean_dec_ref(v___y_4576_);
lean_dec(v___y_4575_);
lean_dec_ref(v___y_4574_);
return v_res_4579_;
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
