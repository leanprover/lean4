// Lean compiler output
// Module: Lean.Elab.Tactic.Do.VCGen.Split
// Imports: public import Lean.Meta.Tactic.Simp.Types public import Lean.Meta.Match.MatcherApp.Transform public import Lean.Data.Array import Lean.Meta.Match.Rewrite import Lean.Meta.Tactic.Simp.Rewrite import Lean.Meta.Tactic.Assumption
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_etaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Array_mask___redArg(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_transform___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_abstractM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withLocalDeclsDND___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withLocalDeclsD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_rwIfWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_rwMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_arity(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_getMotivePos(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_Meta_Match_MatcherInfo_numAlts(lean_object*);
uint8_t l_Lean_isCasesOnRecursor(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
lean_object* l_Lean_Meta_Simp_simpMatchDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_cond_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_cond_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_resTy(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_expr(lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ite"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(15, 2, 151, 246, 61, 29, 192, 254)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "e"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(26, 154, 90, 102, 217, 192, 49, 255)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 228, 43, 115, 146, 126, 91, 53)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dec"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 11, 154, 178, 201, 214, 183, 192)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "dite"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 166, 197, 161, 68, 218, 116, 116)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cond"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 140, 200, 235, 144, 197, 118, 1)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 128, 245, 49, 225, 62, 36, 86)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "discr"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 61, 20, 168, 108, 94, 13, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_etaExpand___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31___boxed(lean_object**);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "c"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(38, 183, 255, 58, 84, 31, 100, 5)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9;
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "isFalse"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(113, 70, 3, 12, 31, 103, 230, 247)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "isTrue"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(125, 82, 240, 34, 69, 121, 64, 234)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2_value)} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "dcond"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_MatcherApp_toExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.Match.MatcherApp.Basic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.Meta.matchMatcherApp\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "expected constructor"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1;
static lean_once_cell_t l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2;
static const lean_ctor_object l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3 = (const lean_object*)&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Failed to find proof for if condition "};
static const lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Failed to find proof for cond condition "};
static const lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(v_x_6_);
lean_dec_ref(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
lean_object* v_e_10_; lean_object* v___x_11_; 
v_e_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc_ref(v_e_10_);
lean_dec_ref(v_t_8_);
v___x_11_ = lean_apply_1(v_k_9_, v_e_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim___redArg(lean_object* v_t_24_, lean_object* v_ite_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_24_, v_ite_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_ite_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_28_, v_ite_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim___redArg(lean_object* v_t_32_, lean_object* v_dite_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_32_, v_dite_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_dite_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_36_, v_dite_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_cond_elim___redArg(lean_object* v_t_40_, lean_object* v_cond_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_40_, v_cond_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_cond_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_cond_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_44_, v_cond_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim___redArg(lean_object* v_t_48_, lean_object* v_matcher_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_48_, v_matcher_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_matcher_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_52_, v_matcher_54_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_box(0);
v___x_60_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1));
v___x_61_ = l_Lean_Expr_const___override(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2, &l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default(void){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3, &l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3);
return v___x_64_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo(void){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default;
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
lean_object* v_zero_68_; uint8_t v_isZero_69_; 
v_zero_68_ = lean_unsigned_to_nat(0u);
v_isZero_69_ = lean_nat_dec_eq(v_x_66_, v_zero_68_);
if (v_isZero_69_ == 1)
{
lean_dec(v_x_66_);
return v_x_67_;
}
else
{
lean_object* v_one_70_; lean_object* v_n_71_; 
v_one_70_ = lean_unsigned_to_nat(1u);
v_n_71_ = lean_nat_sub(v_x_66_, v_one_70_);
lean_dec(v_x_66_);
if (lean_obj_tag(v_x_67_) == 1)
{
lean_object* v_val_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_83_; 
v_val_72_ = lean_ctor_get(v_x_67_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_83_ == 0)
{
v___x_74_ = v_x_67_;
v_isShared_75_ = v_isSharedCheck_83_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_val_72_);
lean_dec(v_x_67_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_83_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
if (lean_obj_tag(v_val_72_) == 6)
{
lean_object* v_body_76_; lean_object* v___x_78_; 
v_body_76_ = lean_ctor_get(v_val_72_, 2);
lean_inc_ref(v_body_76_);
lean_dec_ref_known(v_val_72_, 3);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v_body_76_);
v___x_78_ = v___x_74_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_body_76_);
v___x_78_ = v_reuseFailAlloc_80_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
v_x_66_ = v_n_71_;
v_x_67_ = v___x_78_;
goto _start;
}
}
else
{
lean_object* v___x_81_; 
lean_del_object(v___x_74_);
lean_dec(v_val_72_);
v___x_81_ = lean_box(0);
v_x_66_ = v_n_71_;
v_x_67_ = v___x_81_;
goto _start;
}
}
}
else
{
lean_object* v___x_84_; 
lean_dec(v_x_67_);
v___x_84_ = lean_box(0);
v_x_66_ = v_n_71_;
v_x_67_ = v___x_84_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_resTy(lean_object* v_info_86_){
_start:
{
lean_object* v_e_88_; 
if (lean_obj_tag(v_info_86_) == 3)
{
lean_object* v_matcherApp_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_111_; 
v_matcherApp_94_ = lean_ctor_get(v_info_86_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v_info_86_);
if (v_isSharedCheck_111_ == 0)
{
v___x_96_ = v_info_86_;
v_isShared_97_ = v_isSharedCheck_111_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_matcherApp_94_);
lean_dec(v_info_86_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_111_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v_toMatcherInfo_98_; lean_object* v_motive_99_; lean_object* v_discrInfos_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v_toMatcherInfo_98_ = lean_ctor_get(v_matcherApp_94_, 0);
lean_inc_ref(v_toMatcherInfo_98_);
v_motive_99_ = lean_ctor_get(v_matcherApp_94_, 4);
lean_inc_ref_n(v_motive_99_, 2);
lean_dec_ref(v_matcherApp_94_);
v_discrInfos_100_ = lean_ctor_get(v_toMatcherInfo_98_, 4);
lean_inc_ref(v_discrInfos_100_);
lean_dec_ref(v_toMatcherInfo_98_);
v___x_101_ = lean_array_get_size(v_discrInfos_100_);
lean_dec_ref(v_discrInfos_100_);
if (v_isShared_97_ == 0)
{
lean_ctor_set_tag(v___x_96_, 1);
lean_ctor_set(v___x_96_, 0, v_motive_99_);
v___x_103_ = v___x_96_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_motive_99_);
v___x_103_ = v_reuseFailAlloc_110_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(v___x_101_, v___x_103_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_dec_ref(v_motive_99_);
return v___x_104_;
}
else
{
lean_object* v_val_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_val_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_val_105_);
v___x_106_ = l_Lean_Expr_looseBVarRange(v_val_105_);
lean_dec(v_val_105_);
v___x_107_ = l_Lean_Expr_looseBVarRange(v_motive_99_);
lean_dec_ref(v_motive_99_);
v___x_108_ = lean_nat_dec_eq(v___x_106_, v___x_107_);
lean_dec(v___x_107_);
lean_dec(v___x_106_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
lean_dec_ref_known(v___x_104_, 1);
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
return v___x_104_;
}
}
}
}
}
else
{
lean_object* v_e_112_; 
v_e_112_ = lean_ctor_get(v_info_86_, 0);
lean_inc_ref(v_e_112_);
lean_dec_ref(v_info_86_);
v_e_88_ = v_e_112_;
goto v___jp_87_;
}
v___jp_87_:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_89_ = l_Lean_Expr_getAppNumArgs(v_e_88_);
v___x_90_ = lean_unsigned_to_nat(1u);
v___x_91_ = lean_nat_sub(v___x_89_, v___x_90_);
lean_dec(v___x_89_);
v___x_92_ = l_Lean_Expr_getRevArg_x21(v_e_88_, v___x_91_);
lean_dec_ref(v_e_88_);
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object* v_matcherApp_113_, size_t v_sz_114_, size_t v_i_115_, lean_object* v_bs_116_){
_start:
{
uint8_t v___x_117_; 
v___x_117_ = lean_usize_dec_lt(v_i_115_, v_sz_114_);
if (v___x_117_ == 0)
{
return v_bs_116_;
}
else
{
lean_object* v_v_118_; lean_object* v_alts_119_; lean_object* v___x_120_; lean_object* v_bs_x27_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; size_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
v_v_118_ = lean_array_uget(v_bs_116_, v_i_115_);
v_alts_119_ = lean_ctor_get(v_matcherApp_113_, 6);
v___x_120_ = lean_unsigned_to_nat(0u);
v_bs_x27_121_ = lean_array_uset(v_bs_116_, v_i_115_, v___x_120_);
v___x_122_ = l_Lean_instInhabitedExpr;
v___x_123_ = lean_usize_to_nat(v_i_115_);
v___x_124_ = lean_array_get_borrowed(v___x_122_, v_alts_119_, v___x_123_);
lean_dec(v___x_123_);
lean_inc(v___x_124_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_v_118_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = ((size_t)1ULL);
v___x_127_ = lean_usize_add(v_i_115_, v___x_126_);
v___x_128_ = lean_array_uset(v_bs_x27_121_, v_i_115_, v___x_125_);
v_i_115_ = v___x_127_;
v_bs_116_ = v___x_128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object* v_matcherApp_130_, lean_object* v_sz_131_, lean_object* v_i_132_, lean_object* v_bs_133_){
_start:
{
size_t v_sz_boxed_134_; size_t v_i_boxed_135_; lean_object* v_res_136_; 
v_sz_boxed_134_ = lean_unbox_usize(v_sz_131_);
lean_dec(v_sz_131_);
v_i_boxed_135_ = lean_unbox_usize(v_i_132_);
lean_dec(v_i_132_);
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_130_, v_sz_boxed_134_, v_i_boxed_135_, v_bs_133_);
lean_dec_ref(v_matcherApp_130_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object* v_info_137_){
_start:
{
switch(lean_obj_tag(v_info_137_))
{
case 0:
{
lean_object* v_e_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v_e_138_ = lean_ctor_get(v_info_137_, 0);
lean_inc_ref(v_e_138_);
lean_dec_ref_known(v_info_137_, 1);
v___x_139_ = lean_unsigned_to_nat(0u);
v___x_140_ = lean_unsigned_to_nat(3u);
v___x_141_ = l_Lean_Expr_getAppNumArgs(v_e_138_);
v___x_142_ = lean_nat_sub(v___x_141_, v___x_140_);
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = lean_nat_sub(v___x_142_, v___x_143_);
lean_dec(v___x_142_);
v___x_145_ = l_Lean_Expr_getRevArg_x21(v_e_138_, v___x_144_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_139_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_unsigned_to_nat(4u);
v___x_148_ = lean_nat_sub(v___x_141_, v___x_147_);
lean_dec(v___x_141_);
v___x_149_ = lean_nat_sub(v___x_148_, v___x_143_);
lean_dec(v___x_148_);
v___x_150_ = l_Lean_Expr_getRevArg_x21(v_e_138_, v___x_149_);
lean_dec_ref(v_e_138_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_139_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_unsigned_to_nat(2u);
v___x_153_ = lean_mk_empty_array_with_capacity(v___x_152_);
v___x_154_ = lean_array_push(v___x_153_, v___x_146_);
v___x_155_ = lean_array_push(v___x_154_, v___x_151_);
return v___x_155_;
}
case 1:
{
lean_object* v_e_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_e_156_ = lean_ctor_get(v_info_137_, 0);
lean_inc_ref(v_e_156_);
lean_dec_ref_known(v_info_137_, 1);
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_unsigned_to_nat(3u);
v___x_159_ = l_Lean_Expr_getAppNumArgs(v_e_156_);
v___x_160_ = lean_nat_sub(v___x_159_, v___x_158_);
v___x_161_ = lean_nat_sub(v___x_160_, v___x_157_);
lean_dec(v___x_160_);
v___x_162_ = l_Lean_Expr_getRevArg_x21(v_e_156_, v___x_161_);
v___x_163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_157_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_unsigned_to_nat(4u);
v___x_165_ = lean_nat_sub(v___x_159_, v___x_164_);
lean_dec(v___x_159_);
v___x_166_ = lean_nat_sub(v___x_165_, v___x_157_);
lean_dec(v___x_165_);
v___x_167_ = l_Lean_Expr_getRevArg_x21(v_e_156_, v___x_166_);
lean_dec_ref(v_e_156_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_157_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_unsigned_to_nat(2u);
v___x_170_ = lean_mk_empty_array_with_capacity(v___x_169_);
v___x_171_ = lean_array_push(v___x_170_, v___x_163_);
v___x_172_ = lean_array_push(v___x_171_, v___x_168_);
return v___x_172_;
}
case 2:
{
lean_object* v_e_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_e_173_ = lean_ctor_get(v_info_137_, 0);
lean_inc_ref(v_e_173_);
lean_dec_ref_known(v_info_137_, 1);
v___x_174_ = lean_unsigned_to_nat(0u);
v___x_175_ = lean_unsigned_to_nat(2u);
v___x_176_ = l_Lean_Expr_getAppNumArgs(v_e_173_);
v___x_177_ = lean_nat_sub(v___x_176_, v___x_175_);
v___x_178_ = lean_unsigned_to_nat(1u);
v___x_179_ = lean_nat_sub(v___x_177_, v___x_178_);
lean_dec(v___x_177_);
v___x_180_ = l_Lean_Expr_getRevArg_x21(v_e_173_, v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_174_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_unsigned_to_nat(3u);
v___x_183_ = lean_nat_sub(v___x_176_, v___x_182_);
lean_dec(v___x_176_);
v___x_184_ = lean_nat_sub(v___x_183_, v___x_178_);
lean_dec(v___x_183_);
v___x_185_ = l_Lean_Expr_getRevArg_x21(v_e_173_, v___x_184_);
lean_dec_ref(v_e_173_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_174_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_mk_empty_array_with_capacity(v___x_175_);
v___x_188_ = lean_array_push(v___x_187_, v___x_181_);
v___x_189_ = lean_array_push(v___x_188_, v___x_186_);
return v___x_189_;
}
default: 
{
lean_object* v_matcherApp_190_; lean_object* v___x_191_; size_t v_sz_192_; size_t v___x_193_; lean_object* v___x_194_; 
v_matcherApp_190_ = lean_ctor_get(v_info_137_, 0);
lean_inc_ref_n(v_matcherApp_190_, 2);
lean_dec_ref_known(v_info_137_, 1);
v___x_191_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_190_);
v_sz_192_ = lean_array_size(v___x_191_);
v___x_193_ = ((size_t)0ULL);
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_190_, v_sz_192_, v___x_193_, v___x_191_);
lean_dec_ref(v_matcherApp_190_);
return v___x_194_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object* v_matcherApp_195_, lean_object* v_as_196_, size_t v_sz_197_, size_t v_i_198_, lean_object* v_bs_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_195_, v_sz_197_, v_i_198_, v_bs_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object* v_matcherApp_201_, lean_object* v_as_202_, lean_object* v_sz_203_, lean_object* v_i_204_, lean_object* v_bs_205_){
_start:
{
size_t v_sz_boxed_206_; size_t v_i_boxed_207_; lean_object* v_res_208_; 
v_sz_boxed_206_ = lean_unbox_usize(v_sz_203_);
lean_dec(v_sz_203_);
v_i_boxed_207_ = lean_unbox_usize(v_i_204_);
lean_dec(v_i_204_);
v_res_208_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(v_matcherApp_201_, v_as_202_, v_sz_boxed_206_, v_i_boxed_207_, v_bs_205_);
lean_dec_ref(v_as_202_);
lean_dec_ref(v_matcherApp_201_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_expr(lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_209_) == 3)
{
lean_object* v_matcherApp_210_; lean_object* v___x_211_; 
v_matcherApp_210_ = lean_ctor_get(v_x_209_, 0);
lean_inc_ref(v_matcherApp_210_);
lean_dec_ref_known(v_x_209_, 1);
v___x_211_ = l_Lean_Meta_MatcherApp_toExpr(v_matcherApp_210_);
return v___x_211_;
}
else
{
lean_object* v_e_212_; 
v_e_212_ = lean_ctor_get(v_x_209_, 0);
lean_inc_ref(v_e_212_);
lean_dec_ref(v_x_209_);
return v_e_212_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0(lean_object* v___x_216_, lean_object* v_resTy_217_, lean_object* v_c_218_, lean_object* v_dec_219_, lean_object* v_t_220_, lean_object* v_e_221_, lean_object* v_k_222_, lean_object* v_u_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_224_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_225_, 0, v_u_223_);
lean_ctor_set(v___x_225_, 1, v___x_216_);
v___x_226_ = l_Lean_mkConst(v___x_224_, v___x_225_);
lean_inc_ref(v_e_221_);
lean_inc_ref(v_t_220_);
lean_inc_ref(v_dec_219_);
lean_inc_ref(v_c_218_);
v___x_227_ = l_Lean_mkApp5(v___x_226_, v_resTy_217_, v_c_218_, v_dec_219_, v_t_220_, v_e_221_);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
v___x_229_ = lean_unsigned_to_nat(4u);
v___x_230_ = lean_mk_empty_array_with_capacity(v___x_229_);
v___x_231_ = lean_array_push(v___x_230_, v_c_218_);
v___x_232_ = lean_array_push(v___x_231_, v_dec_219_);
v___x_233_ = lean_array_push(v___x_232_, v_t_220_);
v___x_234_ = lean_array_push(v___x_233_, v_e_221_);
v___x_235_ = lean_apply_2(v_k_222_, v___x_228_, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1(lean_object* v___x_236_, lean_object* v_resTy_237_, lean_object* v_c_238_, lean_object* v_dec_239_, lean_object* v_t_240_, lean_object* v_k_241_, lean_object* v_inst_242_, lean_object* v_toBind_243_, lean_object* v_e_244_){
_start:
{
lean_object* v___f_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
lean_inc_ref(v_resTy_237_);
v___f_245_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0), 8, 7);
lean_closure_set(v___f_245_, 0, v___x_236_);
lean_closure_set(v___f_245_, 1, v_resTy_237_);
lean_closure_set(v___f_245_, 2, v_c_238_);
lean_closure_set(v___f_245_, 3, v_dec_239_);
lean_closure_set(v___f_245_, 4, v_t_240_);
lean_closure_set(v___f_245_, 5, v_e_244_);
lean_closure_set(v___f_245_, 6, v_k_241_);
v___x_246_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_246_, 0, v_resTy_237_);
v___x_247_ = lean_apply_2(v_inst_242_, lean_box(0), v___x_246_);
v___x_248_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v___x_247_, v___f_245_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2(lean_object* v___x_252_, lean_object* v_resTy_253_, lean_object* v_c_254_, lean_object* v_dec_255_, lean_object* v_k_256_, lean_object* v_inst_257_, lean_object* v_toBind_258_, lean_object* v_inst_259_, lean_object* v_inst_260_, lean_object* v_t_261_){
_start:
{
lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
lean_inc_ref(v_resTy_253_);
v___f_262_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1), 9, 8);
lean_closure_set(v___f_262_, 0, v___x_252_);
lean_closure_set(v___f_262_, 1, v_resTy_253_);
lean_closure_set(v___f_262_, 2, v_c_254_);
lean_closure_set(v___f_262_, 3, v_dec_255_);
lean_closure_set(v___f_262_, 4, v_t_261_);
lean_closure_set(v___f_262_, 5, v_k_256_);
lean_closure_set(v___f_262_, 6, v_inst_257_);
lean_closure_set(v___f_262_, 7, v_toBind_258_);
v___x_263_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_264_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_259_, v_inst_260_, v___x_263_, v_resTy_253_, v___f_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3(lean_object* v___x_268_, lean_object* v_resTy_269_, lean_object* v_c_270_, lean_object* v_k_271_, lean_object* v_inst_272_, lean_object* v_toBind_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_dec_276_){
_start:
{
lean_object* v___f_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
lean_inc_ref(v_inst_275_);
lean_inc_ref(v_inst_274_);
lean_inc_ref(v_resTy_269_);
v___f_277_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2), 10, 9);
lean_closure_set(v___f_277_, 0, v___x_268_);
lean_closure_set(v___f_277_, 1, v_resTy_269_);
lean_closure_set(v___f_277_, 2, v_c_270_);
lean_closure_set(v___f_277_, 3, v_dec_276_);
lean_closure_set(v___f_277_, 4, v_k_271_);
lean_closure_set(v___f_277_, 5, v_inst_272_);
lean_closure_set(v___f_277_, 6, v_toBind_273_);
lean_closure_set(v___f_277_, 7, v_inst_274_);
lean_closure_set(v___f_277_, 8, v_inst_275_);
v___x_278_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_279_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_274_, v_inst_275_, v___x_278_, v_resTy_269_, v___f_277_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_box(0);
v___x_287_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3));
v___x_288_ = l_Lean_mkConst(v___x_287_, v___x_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4(lean_object* v_resTy_289_, lean_object* v_k_290_, lean_object* v_inst_291_, lean_object* v_toBind_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_c_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_296_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_297_ = lean_box(0);
lean_inc_ref(v_inst_294_);
lean_inc_ref(v_inst_293_);
lean_inc_ref(v_c_295_);
v___f_298_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3), 9, 8);
lean_closure_set(v___f_298_, 0, v___x_297_);
lean_closure_set(v___f_298_, 1, v_resTy_289_);
lean_closure_set(v___f_298_, 2, v_c_295_);
lean_closure_set(v___f_298_, 3, v_k_290_);
lean_closure_set(v___f_298_, 4, v_inst_291_);
lean_closure_set(v___f_298_, 5, v_toBind_292_);
lean_closure_set(v___f_298_, 6, v_inst_293_);
lean_closure_set(v___f_298_, 7, v_inst_294_);
v___x_299_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_300_ = l_Lean_Expr_app___override(v___x_299_, v_c_295_);
v___x_301_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_293_, v_inst_294_, v___x_296_, v___x_300_, v___f_298_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(lean_object* v_c_302_, lean_object* v_resTy_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_mkArrow(v_c_302_, v_resTy_303_, v___y_306_, v___y_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed(lean_object* v_c_310_, lean_object* v_resTy_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(v_c_310_, v_resTy_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6(lean_object* v___x_321_, lean_object* v_resTy_322_, lean_object* v_c_323_, lean_object* v_dec_324_, lean_object* v_t_325_, lean_object* v_e_326_, lean_object* v_k_327_, lean_object* v_u_328_){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_329_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_330_, 0, v_u_328_);
lean_ctor_set(v___x_330_, 1, v___x_321_);
v___x_331_ = l_Lean_mkConst(v___x_329_, v___x_330_);
lean_inc_ref(v_e_326_);
lean_inc_ref(v_t_325_);
lean_inc_ref(v_dec_324_);
lean_inc_ref(v_c_323_);
v___x_332_ = l_Lean_mkApp5(v___x_331_, v_resTy_322_, v_c_323_, v_dec_324_, v_t_325_, v_e_326_);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
v___x_334_ = lean_unsigned_to_nat(4u);
v___x_335_ = lean_mk_empty_array_with_capacity(v___x_334_);
v___x_336_ = lean_array_push(v___x_335_, v_c_323_);
v___x_337_ = lean_array_push(v___x_336_, v_dec_324_);
v___x_338_ = lean_array_push(v___x_337_, v_t_325_);
v___x_339_ = lean_array_push(v___x_338_, v_e_326_);
v___x_340_ = lean_apply_2(v_k_327_, v___x_333_, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7(lean_object* v___x_341_, lean_object* v_resTy_342_, lean_object* v_c_343_, lean_object* v_dec_344_, lean_object* v_t_345_, lean_object* v_k_346_, lean_object* v_inst_347_, lean_object* v_toBind_348_, lean_object* v_e_349_){
_start:
{
lean_object* v___f_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
lean_inc_ref(v_resTy_342_);
v___f_350_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6), 8, 7);
lean_closure_set(v___f_350_, 0, v___x_341_);
lean_closure_set(v___f_350_, 1, v_resTy_342_);
lean_closure_set(v___f_350_, 2, v_c_343_);
lean_closure_set(v___f_350_, 3, v_dec_344_);
lean_closure_set(v___f_350_, 4, v_t_345_);
lean_closure_set(v___f_350_, 5, v_e_349_);
lean_closure_set(v___f_350_, 6, v_k_346_);
v___x_351_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_351_, 0, v_resTy_342_);
v___x_352_ = lean_apply_2(v_inst_347_, lean_box(0), v___x_351_);
v___x_353_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_352_, v___f_350_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8(lean_object* v___x_354_, lean_object* v_resTy_355_, lean_object* v_c_356_, lean_object* v_dec_357_, lean_object* v_k_358_, lean_object* v_inst_359_, lean_object* v_toBind_360_, lean_object* v_inst_361_, lean_object* v_inst_362_, lean_object* v_eTy_363_, lean_object* v_t_364_){
_start:
{
lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___f_365_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7), 9, 8);
lean_closure_set(v___f_365_, 0, v___x_354_);
lean_closure_set(v___f_365_, 1, v_resTy_355_);
lean_closure_set(v___f_365_, 2, v_c_356_);
lean_closure_set(v___f_365_, 3, v_dec_357_);
lean_closure_set(v___f_365_, 4, v_t_364_);
lean_closure_set(v___f_365_, 5, v_k_358_);
lean_closure_set(v___f_365_, 6, v_inst_359_);
lean_closure_set(v___f_365_, 7, v_toBind_360_);
v___x_366_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_367_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_361_, v_inst_362_, v___x_366_, v_eTy_363_, v___f_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9(lean_object* v___x_368_, lean_object* v_resTy_369_, lean_object* v_c_370_, lean_object* v_dec_371_, lean_object* v_k_372_, lean_object* v_inst_373_, lean_object* v_toBind_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_tTy_377_, lean_object* v_eTy_378_){
_start:
{
lean_object* v___f_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
lean_inc_ref(v_inst_376_);
lean_inc_ref(v_inst_375_);
v___f_379_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8), 11, 10);
lean_closure_set(v___f_379_, 0, v___x_368_);
lean_closure_set(v___f_379_, 1, v_resTy_369_);
lean_closure_set(v___f_379_, 2, v_c_370_);
lean_closure_set(v___f_379_, 3, v_dec_371_);
lean_closure_set(v___f_379_, 4, v_k_372_);
lean_closure_set(v___f_379_, 5, v_inst_373_);
lean_closure_set(v___f_379_, 6, v_toBind_374_);
lean_closure_set(v___f_379_, 7, v_inst_375_);
lean_closure_set(v___f_379_, 8, v_inst_376_);
lean_closure_set(v___f_379_, 9, v_eTy_378_);
v___x_380_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_381_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_375_, v_inst_376_, v___x_380_, v_tTy_377_, v___f_379_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(lean_object* v___x_382_, lean_object* v_resTy_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_mkArrow(v___x_382_, v_resTy_383_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(lean_object* v___x_390_, lean_object* v_resTy_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(v___x_390_, v_resTy_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(lean_object* v___x_398_, lean_object* v_resTy_399_, lean_object* v_c_400_, lean_object* v_dec_401_, lean_object* v_k_402_, lean_object* v_inst_403_, lean_object* v_toBind_404_, lean_object* v_inst_405_, lean_object* v_inst_406_, lean_object* v_tTy_407_){
_start:
{
lean_object* v___f_408_; lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_inc(v_toBind_404_);
lean_inc(v_inst_403_);
lean_inc_ref(v_c_400_);
lean_inc_ref(v_resTy_399_);
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9), 11, 10);
lean_closure_set(v___f_408_, 0, v___x_398_);
lean_closure_set(v___f_408_, 1, v_resTy_399_);
lean_closure_set(v___f_408_, 2, v_c_400_);
lean_closure_set(v___f_408_, 3, v_dec_401_);
lean_closure_set(v___f_408_, 4, v_k_402_);
lean_closure_set(v___f_408_, 5, v_inst_403_);
lean_closure_set(v___f_408_, 6, v_toBind_404_);
lean_closure_set(v___f_408_, 7, v_inst_405_);
lean_closure_set(v___f_408_, 8, v_inst_406_);
lean_closure_set(v___f_408_, 9, v_tTy_407_);
v___x_409_ = l_Lean_mkNot(v_c_400_);
v___f_410_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed), 7, 2);
lean_closure_set(v___f_410_, 0, v___x_409_);
lean_closure_set(v___f_410_, 1, v_resTy_399_);
v___x_411_ = lean_apply_2(v_inst_403_, lean_box(0), v___f_410_);
v___x_412_ = lean_apply_4(v_toBind_404_, lean_box(0), lean_box(0), v___x_411_, v___f_408_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(lean_object* v___x_413_, lean_object* v_resTy_414_, lean_object* v_c_415_, lean_object* v_k_416_, lean_object* v_inst_417_, lean_object* v_toBind_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v___f_421_, lean_object* v_dec_422_){
_start:
{
lean_object* v___f_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_inc(v_toBind_418_);
lean_inc(v_inst_417_);
v___f_423_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11), 10, 9);
lean_closure_set(v___f_423_, 0, v___x_413_);
lean_closure_set(v___f_423_, 1, v_resTy_414_);
lean_closure_set(v___f_423_, 2, v_c_415_);
lean_closure_set(v___f_423_, 3, v_dec_422_);
lean_closure_set(v___f_423_, 4, v_k_416_);
lean_closure_set(v___f_423_, 5, v_inst_417_);
lean_closure_set(v___f_423_, 6, v_toBind_418_);
lean_closure_set(v___f_423_, 7, v_inst_419_);
lean_closure_set(v___f_423_, 8, v_inst_420_);
v___x_424_ = lean_apply_2(v_inst_417_, lean_box(0), v___f_421_);
v___x_425_ = lean_apply_4(v_toBind_418_, lean_box(0), lean_box(0), v___x_424_, v___f_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(lean_object* v_resTy_426_, lean_object* v_k_427_, lean_object* v_inst_428_, lean_object* v_toBind_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_c_432_){
_start:
{
lean_object* v___f_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___f_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
lean_inc_ref(v_resTy_426_);
lean_inc_ref_n(v_c_432_, 2);
v___f_433_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed), 7, 2);
lean_closure_set(v___f_433_, 0, v_c_432_);
lean_closure_set(v___f_433_, 1, v_resTy_426_);
v___x_434_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_435_ = lean_box(0);
lean_inc_ref(v_inst_431_);
lean_inc_ref(v_inst_430_);
v___f_436_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12), 10, 9);
lean_closure_set(v___f_436_, 0, v___x_435_);
lean_closure_set(v___f_436_, 1, v_resTy_426_);
lean_closure_set(v___f_436_, 2, v_c_432_);
lean_closure_set(v___f_436_, 3, v_k_427_);
lean_closure_set(v___f_436_, 4, v_inst_428_);
lean_closure_set(v___f_436_, 5, v_toBind_429_);
lean_closure_set(v___f_436_, 6, v_inst_430_);
lean_closure_set(v___f_436_, 7, v_inst_431_);
lean_closure_set(v___f_436_, 8, v___f_433_);
v___x_437_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_438_ = l_Lean_Expr_app___override(v___x_437_, v_c_432_);
v___x_439_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_430_, v_inst_431_, v___x_434_, v___x_438_, v___f_436_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object* v___x_443_, lean_object* v_resTy_444_, lean_object* v_c_445_, lean_object* v_t_446_, lean_object* v_e_447_, lean_object* v_k_448_, lean_object* v_u_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_450_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_451_, 0, v_u_449_);
lean_ctor_set(v___x_451_, 1, v___x_443_);
v___x_452_ = l_Lean_mkConst(v___x_450_, v___x_451_);
lean_inc_ref(v_e_447_);
lean_inc_ref(v_t_446_);
lean_inc_ref(v_c_445_);
v___x_453_ = l_Lean_mkApp4(v___x_452_, v_resTy_444_, v_c_445_, v_t_446_, v_e_447_);
v___x_454_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
v___x_455_ = lean_unsigned_to_nat(3u);
v___x_456_ = lean_mk_empty_array_with_capacity(v___x_455_);
v___x_457_ = lean_array_push(v___x_456_, v_c_445_);
v___x_458_ = lean_array_push(v___x_457_, v_t_446_);
v___x_459_ = lean_array_push(v___x_458_, v_e_447_);
v___x_460_ = lean_apply_2(v_k_448_, v___x_454_, v___x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object* v___x_461_, lean_object* v_resTy_462_, lean_object* v_c_463_, lean_object* v_t_464_, lean_object* v_k_465_, lean_object* v_inst_466_, lean_object* v_toBind_467_, lean_object* v_e_468_){
_start:
{
lean_object* v___f_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
lean_inc_ref(v_resTy_462_);
v___f_469_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14), 7, 6);
lean_closure_set(v___f_469_, 0, v___x_461_);
lean_closure_set(v___f_469_, 1, v_resTy_462_);
lean_closure_set(v___f_469_, 2, v_c_463_);
lean_closure_set(v___f_469_, 3, v_t_464_);
lean_closure_set(v___f_469_, 4, v_e_468_);
lean_closure_set(v___f_469_, 5, v_k_465_);
v___x_470_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_470_, 0, v_resTy_462_);
v___x_471_ = lean_apply_2(v_inst_466_, lean_box(0), v___x_470_);
v___x_472_ = lean_apply_4(v_toBind_467_, lean_box(0), lean_box(0), v___x_471_, v___f_469_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object* v___x_473_, lean_object* v_resTy_474_, lean_object* v_c_475_, lean_object* v_k_476_, lean_object* v_inst_477_, lean_object* v_toBind_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_t_481_){
_start:
{
lean_object* v___f_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
lean_inc_ref(v_resTy_474_);
v___f_482_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15), 8, 7);
lean_closure_set(v___f_482_, 0, v___x_473_);
lean_closure_set(v___f_482_, 1, v_resTy_474_);
lean_closure_set(v___f_482_, 2, v_c_475_);
lean_closure_set(v___f_482_, 3, v_t_481_);
lean_closure_set(v___f_482_, 4, v_k_476_);
lean_closure_set(v___f_482_, 5, v_inst_477_);
lean_closure_set(v___f_482_, 6, v_toBind_478_);
v___x_483_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_484_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_479_, v_inst_480_, v___x_483_, v_resTy_474_, v___f_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object* v___x_485_, lean_object* v_resTy_486_, lean_object* v_k_487_, lean_object* v_inst_488_, lean_object* v_toBind_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_c_492_){
_start:
{
lean_object* v___f_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_inc_ref(v_inst_491_);
lean_inc_ref(v_inst_490_);
lean_inc_ref(v_resTy_486_);
v___f_493_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16), 9, 8);
lean_closure_set(v___f_493_, 0, v___x_485_);
lean_closure_set(v___f_493_, 1, v_resTy_486_);
lean_closure_set(v___f_493_, 2, v_c_492_);
lean_closure_set(v___f_493_, 3, v_k_487_);
lean_closure_set(v___f_493_, 4, v_inst_488_);
lean_closure_set(v___f_493_, 5, v_toBind_489_);
lean_closure_set(v___f_493_, 6, v_inst_490_);
lean_closure_set(v___f_493_, 7, v_inst_491_);
v___x_494_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_495_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_490_, v_inst_491_, v___x_494_, v_resTy_486_, v___f_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object* v_resTy_496_, lean_object* v_motiveArgs_497_, lean_object* v_x_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
uint8_t v___x_504_; uint8_t v___x_505_; uint8_t v___x_506_; lean_object* v___x_507_; 
v___x_504_ = 0;
v___x_505_ = 1;
v___x_506_ = 1;
v___x_507_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_497_, v_resTy_496_, v___x_504_, v___x_505_, v___x_504_, v___x_505_, v___x_506_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed(lean_object* v_resTy_508_, lean_object* v_motiveArgs_509_, lean_object* v_x_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(v_resTy_508_, v_motiveArgs_509_, v_x_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec_ref(v_x_510_);
lean_dec_ref(v_motiveArgs_509_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object* v_i_520_, lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_523_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1));
v___x_524_ = lean_unsigned_to_nat(1u);
v___x_525_ = lean_nat_add(v_i_520_, v___x_524_);
v___x_526_ = lean_name_append_index_after(v___x_523_, v___x_525_);
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v_a_521_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___boxed(lean_object* v_i_528_, lean_object* v_a_529_, lean_object* v_x_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(v_i_528_, v_a_529_, v_x_530_);
lean_dec(v_i_528_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object* v_i_532_, lean_object* v___x_533_, lean_object* v_discrs_534_, lean_object* v_prior_535_, lean_object* v_next_536_, lean_object* v_acc_537_, lean_object* v_h_538_, lean_object* v_G_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_a_546_; uint8_t v___x_550_; 
v___x_550_ = lean_nat_dec_lt(v_next_536_, v_i_532_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_dec_ref(v_G_539_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v_acc_537_);
return v___x_551_;
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_array_get_borrowed(v___x_533_, v_discrs_534_, v_next_536_);
v___x_553_ = l_Lean_Expr_isFVar(v___x_552_);
if (v___x_553_ == 0)
{
v_a_546_ = v_acc_537_;
goto v___jp_545_;
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_array_get_borrowed(v___x_533_, v_prior_535_, v_next_536_);
lean_inc(v___x_552_);
v___x_555_ = l_Lean_Expr_replaceFVar(v_acc_537_, v___x_552_, v___x_554_);
lean_dec_ref(v_acc_537_);
v_a_546_ = v___x_555_;
goto v___jp_545_;
}
}
v___jp_545_:
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_add(v_next_536_, v___x_547_);
lean_inc(v___y_543_);
lean_inc_ref(v___y_542_);
lean_inc(v___y_541_);
lean_inc_ref(v___y_540_);
v___x_549_ = lean_apply_9(v_G_539_, v___x_548_, v_a_546_, lean_box(0), lean_box(0), v___y_540_, v___y_541_, v___y_542_, v___y_543_, lean_box(0));
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed(lean_object* v_i_556_, lean_object* v___x_557_, lean_object* v_discrs_558_, lean_object* v_prior_559_, lean_object* v_next_560_, lean_object* v_acc_561_, lean_object* v_h_562_, lean_object* v_G_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(v_i_556_, v___x_557_, v_discrs_558_, v_prior_559_, v_next_560_, v_acc_561_, v_h_562_, v_G_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
lean_dec(v___y_565_);
lean_dec_ref(v___y_564_);
lean_dec(v_next_560_);
lean_dec_ref(v_prior_559_);
lean_dec_ref(v_discrs_558_);
lean_dec_ref(v___x_557_);
lean_dec(v_i_556_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object* v_a_570_, lean_object* v___f_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
lean_object* v___x_577_; 
lean_inc(v___y_575_);
lean_inc_ref(v___y_574_);
lean_inc(v___y_573_);
lean_inc_ref(v___y_572_);
v___x_577_ = lean_infer_type(v_a_570_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_579_; lean_object* v___x_2396__overap_580_; lean_object* v___x_581_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref_known(v___x_577_, 1);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_2396__overap_580_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_571_, v___x_579_, v_a_578_, lean_box(0));
v___x_581_ = lean_apply_5(v___x_2396__overap_580_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, lean_box(0));
return v___x_581_;
}
else
{
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
lean_dec_ref(v___f_571_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed(lean_object* v_a_582_, lean_object* v___f_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(v_a_582_, v___f_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object* v_i_590_, lean_object* v___x_591_, lean_object* v_discrs_592_, lean_object* v_a_593_, lean_object* v_inst_594_, lean_object* v_prior_595_){
_start:
{
lean_object* v___f_596_; lean_object* v___f_597_; lean_object* v___x_598_; 
v___f_596_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed), 13, 4);
lean_closure_set(v___f_596_, 0, v_i_590_);
lean_closure_set(v___f_596_, 1, v___x_591_);
lean_closure_set(v___f_596_, 2, v_discrs_592_);
lean_closure_set(v___f_596_, 3, v_prior_595_);
v___f_597_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed), 7, 2);
lean_closure_set(v___f_597_, 0, v_a_593_);
lean_closure_set(v___f_597_, 1, v___f_596_);
v___x_598_ = lean_apply_2(v_inst_594_, lean_box(0), v___f_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object* v___x_602_, lean_object* v_discrs_603_, lean_object* v_inst_604_, lean_object* v_i_605_, lean_object* v_a_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___f_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_inc(v_i_605_);
v___f_608_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22), 6, 5);
lean_closure_set(v___f_608_, 0, v_i_605_);
lean_closure_set(v___f_608_, 1, v___x_602_);
lean_closure_set(v___f_608_, 2, v_discrs_603_);
lean_closure_set(v___f_608_, 3, v_a_606_);
lean_closure_set(v___f_608_, 4, v_inst_604_);
v___x_609_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__1));
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_add(v_i_605_, v___x_610_);
lean_dec(v_i_605_);
v___x_612_ = lean_name_append_index_after(v___x_609_, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
lean_ctor_set(v___x_613_, 1, v___f_608_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object* v_toMatcherInfo_616_, lean_object* v_matcherName_617_, lean_object* v_matcherLevels_618_, lean_object* v_params_619_, lean_object* v_motive_620_, lean_object* v_discrs_621_, lean_object* v_alts_622_, lean_object* v_k_623_, lean_object* v_____do__lift_624_){
_start:
{
lean_object* v___x_625_; lean_object* v_abstractMatcherApp_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_625_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
lean_inc_ref(v_discrs_621_);
v_abstractMatcherApp_626_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_abstractMatcherApp_626_, 0, v_toMatcherInfo_616_);
lean_ctor_set(v_abstractMatcherApp_626_, 1, v_matcherName_617_);
lean_ctor_set(v_abstractMatcherApp_626_, 2, v_matcherLevels_618_);
lean_ctor_set(v_abstractMatcherApp_626_, 3, v_params_619_);
lean_ctor_set(v_abstractMatcherApp_626_, 4, v_motive_620_);
lean_ctor_set(v_abstractMatcherApp_626_, 5, v_discrs_621_);
lean_ctor_set(v_abstractMatcherApp_626_, 6, v_____do__lift_624_);
lean_ctor_set(v_abstractMatcherApp_626_, 7, v___x_625_);
v___x_627_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_627_, 0, v_abstractMatcherApp_626_);
v___x_628_ = l_Array_append___redArg(v_discrs_621_, v_alts_622_);
v___x_629_ = lean_apply_2(v_k_623_, v___x_627_, v___x_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed(lean_object* v_toMatcherInfo_630_, lean_object* v_matcherName_631_, lean_object* v_matcherLevels_632_, lean_object* v_params_633_, lean_object* v_motive_634_, lean_object* v_discrs_635_, lean_object* v_alts_636_, lean_object* v_k_637_, lean_object* v_____do__lift_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(v_toMatcherInfo_630_, v_matcherName_631_, v_matcherLevels_632_, v_params_633_, v_motive_634_, v_discrs_635_, v_alts_636_, v_k_637_, v_____do__lift_638_);
lean_dec_ref(v_alts_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object* v_toMatcherInfo_641_, lean_object* v_matcherName_642_, lean_object* v_matcherLevels_643_, lean_object* v_params_644_, lean_object* v_motive_645_, lean_object* v_discrs_646_, lean_object* v_k_647_, lean_object* v___x_648_, lean_object* v_inst_649_, lean_object* v_toBind_650_, lean_object* v_alts_651_){
_start:
{
lean_object* v___f_652_; lean_object* v___x_653_; size_t v_sz_654_; size_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
lean_inc_ref(v_alts_651_);
v___f_652_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed), 9, 8);
lean_closure_set(v___f_652_, 0, v_toMatcherInfo_641_);
lean_closure_set(v___f_652_, 1, v_matcherName_642_);
lean_closure_set(v___f_652_, 2, v_matcherLevels_643_);
lean_closure_set(v___f_652_, 3, v_params_644_);
lean_closure_set(v___f_652_, 4, v_motive_645_);
lean_closure_set(v___f_652_, 5, v_discrs_646_);
lean_closure_set(v___f_652_, 6, v_alts_651_);
lean_closure_set(v___f_652_, 7, v_k_647_);
v___x_653_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___closed__0));
v_sz_654_ = lean_array_size(v_alts_651_);
v___x_655_ = ((size_t)0ULL);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_648_, v___x_653_, v_sz_654_, v___x_655_, v_alts_651_);
v___x_657_ = lean_apply_2(v_inst_649_, lean_box(0), v___x_656_);
v___x_658_ = lean_apply_4(v_toBind_650_, lean_box(0), lean_box(0), v___x_657_, v___f_652_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object* v___f_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v___f_681_, lean_object* v_origAltTypes_682_){
_start:
{
lean_object* v___x_683_; size_t v_sz_684_; size_t v___x_685_; lean_object* v_altNamesTypes_686_; uint8_t v___x_687_; lean_object* v___x_688_; 
v___x_683_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_684_ = lean_array_size(v_origAltTypes_682_);
v___x_685_ = ((size_t)0ULL);
lean_inc_ref(v_origAltTypes_682_);
v_altNamesTypes_686_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_683_, v_origAltTypes_682_, v___f_678_, v_sz_684_, v___x_685_, v_origAltTypes_682_);
lean_dec_ref(v_origAltTypes_682_);
v___x_687_ = 0;
v___x_688_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_679_, v_inst_680_, v_altNamesTypes_686_, v___f_681_, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object* v_toMatcherInfo_689_, lean_object* v_matcherName_690_, lean_object* v_params_691_, lean_object* v_motive_692_, lean_object* v_discrs_693_, lean_object* v_k_694_, lean_object* v___x_695_, lean_object* v_inst_696_, lean_object* v_toBind_697_, lean_object* v___f_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_alts_701_, lean_object* v_matcherLevels_702_){
_start:
{
lean_object* v___f_703_; lean_object* v___f_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v_matcherPartial_707_; lean_object* v_matcherPartial_708_; lean_object* v_matcherPartial_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_inc(v_toBind_697_);
lean_inc(v_inst_696_);
lean_inc_ref(v_discrs_693_);
lean_inc_ref(v_motive_692_);
lean_inc_ref(v_params_691_);
lean_inc_ref(v_matcherLevels_702_);
lean_inc(v_matcherName_690_);
v___f_703_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25), 11, 10);
lean_closure_set(v___f_703_, 0, v_toMatcherInfo_689_);
lean_closure_set(v___f_703_, 1, v_matcherName_690_);
lean_closure_set(v___f_703_, 2, v_matcherLevels_702_);
lean_closure_set(v___f_703_, 3, v_params_691_);
lean_closure_set(v___f_703_, 4, v_motive_692_);
lean_closure_set(v___f_703_, 5, v_discrs_693_);
lean_closure_set(v___f_703_, 6, v_k_694_);
lean_closure_set(v___f_703_, 7, v___x_695_);
lean_closure_set(v___f_703_, 8, v_inst_696_);
lean_closure_set(v___f_703_, 9, v_toBind_697_);
v___f_704_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26), 5, 4);
lean_closure_set(v___f_704_, 0, v___f_698_);
lean_closure_set(v___f_704_, 1, v_inst_699_);
lean_closure_set(v___f_704_, 2, v_inst_700_);
lean_closure_set(v___f_704_, 3, v___f_703_);
v___x_705_ = lean_array_to_list(v_matcherLevels_702_);
v___x_706_ = l_Lean_mkConst(v_matcherName_690_, v___x_705_);
v_matcherPartial_707_ = l_Lean_mkAppN(v___x_706_, v_params_691_);
lean_dec_ref(v_params_691_);
v_matcherPartial_708_ = l_Lean_Expr_app___override(v_matcherPartial_707_, v_motive_692_);
v_matcherPartial_709_ = l_Lean_mkAppN(v_matcherPartial_708_, v_discrs_693_);
lean_dec_ref(v_discrs_693_);
v___x_710_ = lean_array_get_size(v_alts_701_);
v___x_711_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_711_, 0, v___x_710_);
lean_closure_set(v___x_711_, 1, v_matcherPartial_709_);
v___x_712_ = lean_apply_2(v_inst_696_, lean_box(0), v___x_711_);
v___x_713_ = lean_apply_4(v_toBind_697_, lean_box(0), lean_box(0), v___x_712_, v___f_704_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object* v_toMatcherInfo_714_, lean_object* v_matcherName_715_, lean_object* v_params_716_, lean_object* v_motive_717_, lean_object* v_discrs_718_, lean_object* v_k_719_, lean_object* v___x_720_, lean_object* v_inst_721_, lean_object* v_toBind_722_, lean_object* v___f_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_alts_726_, lean_object* v_matcherLevels_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(v_toMatcherInfo_714_, v_matcherName_715_, v_params_716_, v_motive_717_, v_discrs_718_, v_k_719_, v___x_720_, v_inst_721_, v_toBind_722_, v___f_723_, v_inst_724_, v_inst_725_, v_alts_726_, v_matcherLevels_727_);
lean_dec_ref(v_alts_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28(lean_object* v___f_729_, lean_object* v_matcherLevels_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_apply_1(v___f_729_, v_matcherLevels_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30(lean_object* v_matcherLevels_732_, lean_object* v_val_733_, lean_object* v_toPure_734_, lean_object* v_toBind_735_, lean_object* v___f_736_, lean_object* v_uElim_737_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_array_set(v_matcherLevels_732_, v_val_733_, v_uElim_737_);
v___x_739_ = lean_apply_2(v_toPure_734_, lean_box(0), v___x_738_);
v___x_740_ = lean_apply_4(v_toBind_735_, lean_box(0), lean_box(0), v___x_739_, v___f_736_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30___boxed(lean_object* v_matcherLevels_741_, lean_object* v_val_742_, lean_object* v_toPure_743_, lean_object* v_toBind_744_, lean_object* v___f_745_, lean_object* v_uElim_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30(v_matcherLevels_741_, v_val_742_, v_toPure_743_, v_toBind_744_, v___f_745_, v_uElim_746_);
lean_dec(v_val_742_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__29(lean_object* v_toMatcherInfo_748_, lean_object* v_matcherName_749_, lean_object* v_params_750_, lean_object* v_discrs_751_, lean_object* v_k_752_, lean_object* v___x_753_, lean_object* v_inst_754_, lean_object* v_toBind_755_, lean_object* v___f_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_alts_759_, lean_object* v_toPure_760_, lean_object* v_matcherLevels_761_, lean_object* v_resTy_762_, lean_object* v_motive_763_){
_start:
{
lean_object* v_uElimPos_x3f_764_; lean_object* v___f_765_; 
v_uElimPos_x3f_764_ = lean_ctor_get(v_toMatcherInfo_748_, 3);
lean_inc(v_uElimPos_x3f_764_);
lean_inc(v_toBind_755_);
lean_inc(v_inst_754_);
v___f_765_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed), 14, 13);
lean_closure_set(v___f_765_, 0, v_toMatcherInfo_748_);
lean_closure_set(v___f_765_, 1, v_matcherName_749_);
lean_closure_set(v___f_765_, 2, v_params_750_);
lean_closure_set(v___f_765_, 3, v_motive_763_);
lean_closure_set(v___f_765_, 4, v_discrs_751_);
lean_closure_set(v___f_765_, 5, v_k_752_);
lean_closure_set(v___f_765_, 6, v___x_753_);
lean_closure_set(v___f_765_, 7, v_inst_754_);
lean_closure_set(v___f_765_, 8, v_toBind_755_);
lean_closure_set(v___f_765_, 9, v___f_756_);
lean_closure_set(v___f_765_, 10, v_inst_757_);
lean_closure_set(v___f_765_, 11, v_inst_758_);
lean_closure_set(v___f_765_, 12, v_alts_759_);
if (lean_obj_tag(v_uElimPos_x3f_764_) == 0)
{
lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec_ref(v_resTy_762_);
lean_dec(v_inst_754_);
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28), 2, 1);
lean_closure_set(v___f_766_, 0, v___f_765_);
v___x_767_ = lean_apply_2(v_toPure_760_, lean_box(0), v_matcherLevels_761_);
v___x_768_ = lean_apply_4(v_toBind_755_, lean_box(0), lean_box(0), v___x_767_, v___f_766_);
return v___x_768_;
}
else
{
lean_object* v_val_769_; lean_object* v___f_770_; lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_val_769_ = lean_ctor_get(v_uElimPos_x3f_764_, 0);
lean_inc(v_val_769_);
lean_dec_ref_known(v_uElimPos_x3f_764_, 1);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28), 2, 1);
lean_closure_set(v___f_770_, 0, v___f_765_);
lean_inc(v_toBind_755_);
v___f_771_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30___boxed), 6, 5);
lean_closure_set(v___f_771_, 0, v_matcherLevels_761_);
lean_closure_set(v___f_771_, 1, v_val_769_);
lean_closure_set(v___f_771_, 2, v_toPure_760_);
lean_closure_set(v___f_771_, 3, v_toBind_755_);
lean_closure_set(v___f_771_, 4, v___f_770_);
v___x_772_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_772_, 0, v_resTy_762_);
v___x_773_ = lean_apply_2(v_inst_754_, lean_box(0), v___x_772_);
v___x_774_ = lean_apply_4(v_toBind_755_, lean_box(0), lean_box(0), v___x_773_, v___f_771_);
return v___x_774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(lean_object* v_toMatcherInfo_775_, lean_object* v_matcherName_776_, lean_object* v_params_777_, lean_object* v_k_778_, lean_object* v___x_779_, lean_object* v_inst_780_, lean_object* v_toBind_781_, lean_object* v___f_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_alts_785_, lean_object* v_toPure_786_, lean_object* v_matcherLevels_787_, lean_object* v_resTy_788_, lean_object* v___x_789_, lean_object* v_motive_790_, lean_object* v___f_791_, lean_object* v_discrs_792_){
_start:
{
lean_object* v___f_793_; uint8_t v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_inc(v_toBind_781_);
lean_inc(v_inst_780_);
lean_inc_ref(v___x_779_);
v___f_793_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__29), 16, 15);
lean_closure_set(v___f_793_, 0, v_toMatcherInfo_775_);
lean_closure_set(v___f_793_, 1, v_matcherName_776_);
lean_closure_set(v___f_793_, 2, v_params_777_);
lean_closure_set(v___f_793_, 3, v_discrs_792_);
lean_closure_set(v___f_793_, 4, v_k_778_);
lean_closure_set(v___f_793_, 5, v___x_779_);
lean_closure_set(v___f_793_, 6, v_inst_780_);
lean_closure_set(v___f_793_, 7, v_toBind_781_);
lean_closure_set(v___f_793_, 8, v___f_782_);
lean_closure_set(v___f_793_, 9, v_inst_783_);
lean_closure_set(v___f_793_, 10, v_inst_784_);
lean_closure_set(v___f_793_, 11, v_alts_785_);
lean_closure_set(v___f_793_, 12, v_toPure_786_);
lean_closure_set(v___f_793_, 13, v_matcherLevels_787_);
lean_closure_set(v___f_793_, 14, v_resTy_788_);
v___x_794_ = 0;
v___x_795_ = l_Lean_Meta_lambdaTelescope___redArg(v___x_789_, v___x_779_, v_motive_790_, v___f_791_, v___x_794_);
v___x_796_ = lean_apply_2(v_inst_780_, lean_box(0), v___x_795_);
v___x_797_ = lean_apply_4(v_toBind_781_, lean_box(0), lean_box(0), v___x_796_, v___f_793_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_798_ = _args[0];
lean_object* v_matcherName_799_ = _args[1];
lean_object* v_params_800_ = _args[2];
lean_object* v_k_801_ = _args[3];
lean_object* v___x_802_ = _args[4];
lean_object* v_inst_803_ = _args[5];
lean_object* v_toBind_804_ = _args[6];
lean_object* v___f_805_ = _args[7];
lean_object* v_inst_806_ = _args[8];
lean_object* v_inst_807_ = _args[9];
lean_object* v_alts_808_ = _args[10];
lean_object* v_toPure_809_ = _args[11];
lean_object* v_matcherLevels_810_ = _args[12];
lean_object* v_resTy_811_ = _args[13];
lean_object* v___x_812_ = _args[14];
lean_object* v_motive_813_ = _args[15];
lean_object* v___f_814_ = _args[16];
lean_object* v_discrs_815_ = _args[17];
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(v_toMatcherInfo_798_, v_matcherName_799_, v_params_800_, v_k_801_, v___x_802_, v_inst_803_, v_toBind_804_, v___f_805_, v_inst_806_, v_inst_807_, v_alts_808_, v_toPure_809_, v_matcherLevels_810_, v_resTy_811_, v___x_812_, v_motive_813_, v___f_814_, v_discrs_815_);
return v_res_816_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0(void){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_instMonadEIO(lean_box(0));
return v___x_817_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0);
v___x_819_ = l_StateRefT_x27_instMonad___redArg(v___x_818_);
return v___x_819_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = l_Lean_Level_ofNat(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8);
v___x_830_ = l_Lean_mkSort(v___x_829_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_box(0);
v___x_835_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__11));
v___x_836_ = l_Lean_mkConst(v___x_835_, v___x_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_info_841_, lean_object* v_resTy_842_, lean_object* v_k_843_){
_start:
{
lean_object* v___x_844_; lean_object* v_toApplicative_845_; lean_object* v_toFunctor_846_; lean_object* v_toSeq_847_; lean_object* v_toSeqLeft_848_; lean_object* v_toSeqRight_849_; lean_object* v___f_850_; lean_object* v___f_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v_toApplicative_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_942_; 
v___x_844_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_845_ = lean_ctor_get(v___x_844_, 0);
v_toFunctor_846_ = lean_ctor_get(v_toApplicative_845_, 0);
v_toSeq_847_ = lean_ctor_get(v_toApplicative_845_, 2);
v_toSeqLeft_848_ = lean_ctor_get(v_toApplicative_845_, 3);
v_toSeqRight_849_ = lean_ctor_get(v_toApplicative_845_, 4);
v___f_850_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_851_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_846_, 2);
v___f_852_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_852_, 0, v_toFunctor_846_);
v___f_853_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_853_, 0, v_toFunctor_846_);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___f_852_);
lean_ctor_set(v___x_854_, 1, v___f_853_);
lean_inc(v_toSeqRight_849_);
v___f_855_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_855_, 0, v_toSeqRight_849_);
lean_inc(v_toSeqLeft_848_);
v___f_856_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_856_, 0, v_toSeqLeft_848_);
lean_inc(v_toSeq_847_);
v___f_857_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_857_, 0, v_toSeq_847_);
v___x_858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_858_, 0, v___x_854_);
lean_ctor_set(v___x_858_, 1, v___f_850_);
lean_ctor_set(v___x_858_, 2, v___f_857_);
lean_ctor_set(v___x_858_, 3, v___f_856_);
lean_ctor_set(v___x_858_, 4, v___f_855_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___f_851_);
v___x_860_ = l_StateRefT_x27_instMonad___redArg(v___x_859_);
v_toApplicative_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v___x_860_, 1);
lean_dec(v_unused_943_);
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_942_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_toApplicative_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_942_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v_toFunctor_865_; lean_object* v_toSeq_866_; lean_object* v_toSeqLeft_867_; lean_object* v_toSeqRight_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_940_; 
v_toFunctor_865_ = lean_ctor_get(v_toApplicative_861_, 0);
v_toSeq_866_ = lean_ctor_get(v_toApplicative_861_, 2);
v_toSeqLeft_867_ = lean_ctor_get(v_toApplicative_861_, 3);
v_toSeqRight_868_ = lean_ctor_get(v_toApplicative_861_, 4);
v_isSharedCheck_940_ = !lean_is_exclusive(v_toApplicative_861_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v_toApplicative_861_, 1);
lean_dec(v_unused_941_);
v___x_870_ = v_toApplicative_861_;
v_isShared_871_ = v_isSharedCheck_940_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_toSeqRight_868_);
lean_inc(v_toSeqLeft_867_);
lean_inc(v_toSeq_866_);
lean_inc(v_toFunctor_865_);
lean_dec(v_toApplicative_861_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_940_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___f_872_; lean_object* v___f_873_; lean_object* v___f_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___x_881_; 
v___f_872_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_873_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_865_);
v___f_874_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_874_, 0, v_toFunctor_865_);
v___f_875_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_875_, 0, v_toFunctor_865_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___f_874_);
lean_ctor_set(v___x_876_, 1, v___f_875_);
v___f_877_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_877_, 0, v_toSeqRight_868_);
v___f_878_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_878_, 0, v_toSeqLeft_867_);
v___f_879_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_879_, 0, v_toSeq_866_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 4, v___f_877_);
lean_ctor_set(v___x_870_, 3, v___f_878_);
lean_ctor_set(v___x_870_, 2, v___f_879_);
lean_ctor_set(v___x_870_, 1, v___f_872_);
lean_ctor_set(v___x_870_, 0, v___x_876_);
v___x_881_ = v___x_870_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___f_872_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v___f_879_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v___f_878_);
lean_ctor_set(v_reuseFailAlloc_939_, 4, v___f_877_);
v___x_881_ = v_reuseFailAlloc_939_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_883_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 1, v___f_873_);
lean_ctor_set(v___x_863_, 0, v___x_881_);
v___x_883_ = v___x_863_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_938_, 1, v___f_873_);
v___x_883_ = v_reuseFailAlloc_938_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
lean_object* v_toApplicative_884_; lean_object* v_toFunctor_885_; lean_object* v_toSeq_886_; lean_object* v_toSeqLeft_887_; lean_object* v_toSeqRight_888_; lean_object* v___f_889_; lean_object* v___f_890_; lean_object* v___x_891_; lean_object* v___f_892_; lean_object* v___f_893_; lean_object* v___f_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_toApplicative_884_ = lean_ctor_get(v___x_844_, 0);
v_toFunctor_885_ = lean_ctor_get(v_toApplicative_884_, 0);
v_toSeq_886_ = lean_ctor_get(v_toApplicative_884_, 2);
v_toSeqLeft_887_ = lean_ctor_get(v_toApplicative_884_, 3);
v_toSeqRight_888_ = lean_ctor_get(v_toApplicative_884_, 4);
lean_inc_ref_n(v_toFunctor_885_, 2);
v___f_889_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_889_, 0, v_toFunctor_885_);
v___f_890_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_890_, 0, v_toFunctor_885_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___f_889_);
lean_ctor_set(v___x_891_, 1, v___f_890_);
lean_inc(v_toSeqRight_888_);
v___f_892_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_892_, 0, v_toSeqRight_888_);
lean_inc(v_toSeqLeft_887_);
v___f_893_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_893_, 0, v_toSeqLeft_887_);
lean_inc(v_toSeq_886_);
v___f_894_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_894_, 0, v_toSeq_886_);
v___x_895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_895_, 0, v___x_891_);
lean_ctor_set(v___x_895_, 1, v___f_850_);
lean_ctor_set(v___x_895_, 2, v___f_894_);
lean_ctor_set(v___x_895_, 3, v___f_893_);
lean_ctor_set(v___x_895_, 4, v___f_892_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___f_851_);
v___x_897_ = l_StateRefT_x27_instMonad___redArg(v___x_896_);
v___x_898_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_898_, 0, lean_box(0));
lean_closure_set(v___x_898_, 1, lean_box(0));
lean_closure_set(v___x_898_, 2, v___x_897_);
v___x_899_ = l_instMonadControlTOfPure___redArg(v___x_898_);
switch(lean_obj_tag(v_info_841_))
{
case 0:
{
lean_object* v_toBind_900_; lean_object* v___f_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
lean_dec_ref_known(v_info_841_, 1);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_883_);
v_toBind_900_ = lean_ctor_get(v_inst_840_, 1);
lean_inc_ref(v_inst_840_);
lean_inc_ref(v_inst_839_);
lean_inc(v_toBind_900_);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4), 7, 6);
lean_closure_set(v___f_901_, 0, v_resTy_842_);
lean_closure_set(v___f_901_, 1, v_k_843_);
lean_closure_set(v___f_901_, 2, v_inst_838_);
lean_closure_set(v___f_901_, 3, v_toBind_900_);
lean_closure_set(v___f_901_, 4, v_inst_839_);
lean_closure_set(v___f_901_, 5, v_inst_840_);
v___x_902_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_903_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_904_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_839_, v_inst_840_, v___x_902_, v___x_903_, v___f_901_);
return v___x_904_;
}
case 1:
{
lean_object* v_toBind_905_; lean_object* v___f_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec_ref_known(v_info_841_, 1);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_883_);
v_toBind_905_ = lean_ctor_get(v_inst_840_, 1);
lean_inc_ref(v_inst_840_);
lean_inc_ref(v_inst_839_);
lean_inc(v_toBind_905_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13), 7, 6);
lean_closure_set(v___f_906_, 0, v_resTy_842_);
lean_closure_set(v___f_906_, 1, v_k_843_);
lean_closure_set(v___f_906_, 2, v_inst_838_);
lean_closure_set(v___f_906_, 3, v_toBind_905_);
lean_closure_set(v___f_906_, 4, v_inst_839_);
lean_closure_set(v___f_906_, 5, v_inst_840_);
v___x_907_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_908_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_909_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_839_, v_inst_840_, v___x_907_, v___x_908_, v___f_906_);
return v___x_909_;
}
case 2:
{
lean_object* v_toBind_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec_ref_known(v_info_841_, 1);
lean_dec_ref(v___x_899_);
lean_dec_ref(v___x_883_);
v_toBind_910_ = lean_ctor_get(v_inst_840_, 1);
v___x_911_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_912_ = lean_box(0);
lean_inc_ref(v_inst_840_);
lean_inc_ref(v_inst_839_);
lean_inc(v_toBind_910_);
v___f_913_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17), 8, 7);
lean_closure_set(v___f_913_, 0, v___x_912_);
lean_closure_set(v___f_913_, 1, v_resTy_842_);
lean_closure_set(v___f_913_, 2, v_k_843_);
lean_closure_set(v___f_913_, 3, v_inst_838_);
lean_closure_set(v___f_913_, 4, v_toBind_910_);
lean_closure_set(v___f_913_, 5, v_inst_839_);
lean_closure_set(v___f_913_, 6, v_inst_840_);
v___x_914_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12);
v___x_915_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_839_, v_inst_840_, v___x_911_, v___x_914_, v___f_913_);
return v___x_915_;
}
default: 
{
lean_object* v_toApplicative_916_; lean_object* v_matcherApp_917_; lean_object* v_toBind_918_; lean_object* v_toPure_919_; lean_object* v_toMatcherInfo_920_; lean_object* v_matcherName_921_; lean_object* v_matcherLevels_922_; lean_object* v_params_923_; lean_object* v_motive_924_; lean_object* v_discrs_925_; lean_object* v_alts_926_; lean_object* v___f_927_; lean_object* v___f_928_; lean_object* v___x_929_; lean_object* v___f_930_; lean_object* v___f_931_; lean_object* v___x_932_; size_t v_sz_933_; size_t v___x_934_; lean_object* v_discrDecls_935_; uint8_t v___x_936_; lean_object* v___x_937_; 
v_toApplicative_916_ = lean_ctor_get(v_inst_840_, 0);
v_matcherApp_917_ = lean_ctor_get(v_info_841_, 0);
lean_inc_ref(v_matcherApp_917_);
lean_dec_ref_known(v_info_841_, 1);
v_toBind_918_ = lean_ctor_get(v_inst_840_, 1);
v_toPure_919_ = lean_ctor_get(v_toApplicative_916_, 1);
v_toMatcherInfo_920_ = lean_ctor_get(v_matcherApp_917_, 0);
lean_inc_ref(v_toMatcherInfo_920_);
v_matcherName_921_ = lean_ctor_get(v_matcherApp_917_, 1);
lean_inc(v_matcherName_921_);
v_matcherLevels_922_ = lean_ctor_get(v_matcherApp_917_, 2);
lean_inc_ref(v_matcherLevels_922_);
v_params_923_ = lean_ctor_get(v_matcherApp_917_, 3);
lean_inc_ref(v_params_923_);
v_motive_924_ = lean_ctor_get(v_matcherApp_917_, 4);
lean_inc_ref(v_motive_924_);
v_discrs_925_ = lean_ctor_get(v_matcherApp_917_, 5);
lean_inc_ref_n(v_discrs_925_, 3);
v_alts_926_ = lean_ctor_get(v_matcherApp_917_, 6);
lean_inc_ref(v_alts_926_);
lean_dec_ref(v_matcherApp_917_);
lean_inc_ref(v_resTy_842_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed), 8, 1);
lean_closure_set(v___f_927_, 0, v_resTy_842_);
v___f_928_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__13));
v___x_929_ = l_Lean_instInhabitedExpr;
lean_inc(v_inst_838_);
v___f_930_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23), 6, 3);
lean_closure_set(v___f_930_, 0, v___x_929_);
lean_closure_set(v___f_930_, 1, v_discrs_925_);
lean_closure_set(v___f_930_, 2, v_inst_838_);
lean_inc(v_toPure_919_);
lean_inc_ref(v_inst_840_);
lean_inc_ref(v_inst_839_);
lean_inc(v_toBind_918_);
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_931_, 0, v_toMatcherInfo_920_);
lean_closure_set(v___f_931_, 1, v_matcherName_921_);
lean_closure_set(v___f_931_, 2, v_params_923_);
lean_closure_set(v___f_931_, 3, v_k_843_);
lean_closure_set(v___f_931_, 4, v___x_883_);
lean_closure_set(v___f_931_, 5, v_inst_838_);
lean_closure_set(v___f_931_, 6, v_toBind_918_);
lean_closure_set(v___f_931_, 7, v___f_928_);
lean_closure_set(v___f_931_, 8, v_inst_839_);
lean_closure_set(v___f_931_, 9, v_inst_840_);
lean_closure_set(v___f_931_, 10, v_alts_926_);
lean_closure_set(v___f_931_, 11, v_toPure_919_);
lean_closure_set(v___f_931_, 12, v_matcherLevels_922_);
lean_closure_set(v___f_931_, 13, v_resTy_842_);
lean_closure_set(v___f_931_, 14, v___x_899_);
lean_closure_set(v___f_931_, 15, v_motive_924_);
lean_closure_set(v___f_931_, 16, v___f_927_);
v___x_932_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_933_ = lean_array_size(v_discrs_925_);
v___x_934_ = ((size_t)0ULL);
v_discrDecls_935_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_932_, v_discrs_925_, v___f_930_, v_sz_933_, v___x_934_, v_discrs_925_);
lean_dec_ref(v_discrs_925_);
v___x_936_ = 0;
v___x_937_ = l_Lean_Meta_withLocalDeclsD___redArg(v_inst_839_, v_inst_840_, v_discrDecls_935_, v___f_931_, v___x_936_);
return v___x_937_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object* v_n_944_, lean_object* v_00_u03b1_945_, lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_inst_948_, lean_object* v_inst_949_, lean_object* v_info_950_, lean_object* v_resTy_951_, lean_object* v_k_952_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(v_inst_946_, v_inst_947_, v_inst_948_, v_info_950_, v_resTy_951_, v_k_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object* v_n_954_, lean_object* v_00_u03b1_955_, lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_info_960_, lean_object* v_resTy_961_, lean_object* v_k_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(v_n_954_, v_00_u03b1_955_, v_inst_956_, v_inst_957_, v_inst_958_, v_inst_959_, v_info_960_, v_resTy_961_, v_k_962_);
lean_dec(v_inst_959_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object* v_u_964_, lean_object* v_resTy_965_, lean_object* v_c_966_, lean_object* v_h_967_, lean_object* v_t_968_, lean_object* v_toPure_969_, lean_object* v_e_970_){
_start:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_971_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_972_ = lean_box(0);
v___x_973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_973_, 0, v_u_964_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
v___x_974_ = l_Lean_mkConst(v___x_971_, v___x_973_);
v___x_975_ = l_Lean_mkApp5(v___x_974_, v_resTy_965_, v_c_966_, v_h_967_, v_t_968_, v_e_970_);
v___x_976_ = lean_apply_2(v_toPure_969_, lean_box(0), v___x_975_);
return v___x_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object* v_u_980_, lean_object* v_resTy_981_, lean_object* v_c_982_, lean_object* v_h_983_, lean_object* v_toPure_984_, lean_object* v_onAlt_985_, lean_object* v___x_986_, lean_object* v___x_987_, lean_object* v_toBind_988_, lean_object* v_t_989_){
_start:
{
lean_object* v___f_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
lean_inc_ref(v_resTy_981_);
v___f_990_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0), 7, 6);
lean_closure_set(v___f_990_, 0, v_u_980_);
lean_closure_set(v___f_990_, 1, v_resTy_981_);
lean_closure_set(v___f_990_, 2, v_c_982_);
lean_closure_set(v___f_990_, 3, v_h_983_);
lean_closure_set(v___f_990_, 4, v_t_989_);
lean_closure_set(v___f_990_, 5, v_toPure_984_);
v___x_991_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_992_ = lean_apply_4(v_onAlt_985_, v___x_991_, v_resTy_981_, v___x_986_, v___x_987_);
v___x_993_ = lean_apply_4(v_toBind_988_, lean_box(0), lean_box(0), v___x_992_, v___f_990_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object* v___x_994_, uint8_t v_useSplitter_995_, lean_object* v_inst_996_, lean_object* v_____do__lift_997_){
_start:
{
uint8_t v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_998_ = 0;
v___x_999_ = 1;
v___x_1000_ = lean_box(v___x_998_);
v___x_1001_ = lean_box(v_useSplitter_995_);
v___x_1002_ = lean_box(v___x_998_);
v___x_1003_ = lean_box(v_useSplitter_995_);
v___x_1004_ = lean_box(v___x_999_);
v___x_1005_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1005_, 0, v___x_994_);
lean_closure_set(v___x_1005_, 1, v_____do__lift_997_);
lean_closure_set(v___x_1005_, 2, v___x_1000_);
lean_closure_set(v___x_1005_, 3, v___x_1001_);
lean_closure_set(v___x_1005_, 4, v___x_1002_);
lean_closure_set(v___x_1005_, 5, v___x_1003_);
lean_closure_set(v___x_1005_, 6, v___x_1004_);
v___x_1006_ = lean_apply_2(v_inst_996_, lean_box(0), v___x_1005_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object* v___x_1007_, lean_object* v_useSplitter_1008_, lean_object* v_inst_1009_, lean_object* v_____do__lift_1010_){
_start:
{
uint8_t v_useSplitter_boxed_1011_; lean_object* v_res_1012_; 
v_useSplitter_boxed_1011_ = lean_unbox(v_useSplitter_1008_);
v_res_1012_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(v___x_1007_, v_useSplitter_boxed_1011_, v_inst_1009_, v_____do__lift_1010_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object* v___x_1016_, uint8_t v_useSplitter_1017_, lean_object* v_inst_1018_, lean_object* v_onAlt_1019_, lean_object* v_resTy_1020_, lean_object* v_toBind_1021_, lean_object* v_h_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___f_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1023_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1024_ = lean_unsigned_to_nat(0u);
v___x_1025_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1026_ = lean_mk_empty_array_with_capacity(v___x_1016_);
v___x_1027_ = lean_array_push(v___x_1026_, v_h_1022_);
v___x_1028_ = lean_box(v_useSplitter_1017_);
lean_inc_ref(v___x_1027_);
v___f_1029_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1029_, 0, v___x_1027_);
lean_closure_set(v___f_1029_, 1, v___x_1028_);
lean_closure_set(v___f_1029_, 2, v_inst_1018_);
v___x_1030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1025_);
lean_ctor_set(v___x_1030_, 1, v___x_1027_);
lean_ctor_set(v___x_1030_, 2, v___x_1025_);
lean_ctor_set(v___x_1030_, 3, v___x_1025_);
lean_ctor_set(v___x_1030_, 4, v___x_1025_);
v___x_1031_ = lean_apply_4(v_onAlt_1019_, v___x_1023_, v_resTy_1020_, v___x_1024_, v___x_1030_);
v___x_1032_ = lean_apply_4(v_toBind_1021_, lean_box(0), lean_box(0), v___x_1031_, v___f_1029_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object* v___x_1033_, lean_object* v_useSplitter_1034_, lean_object* v_inst_1035_, lean_object* v_onAlt_1036_, lean_object* v_resTy_1037_, lean_object* v_toBind_1038_, lean_object* v_h_1039_){
_start:
{
uint8_t v_useSplitter_boxed_1040_; lean_object* v_res_1041_; 
v_useSplitter_boxed_1040_ = lean_unbox(v_useSplitter_1034_);
v_res_1041_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(v___x_1033_, v_useSplitter_boxed_1040_, v_inst_1035_, v_onAlt_1036_, v_resTy_1037_, v_toBind_1038_, v_h_1039_);
lean_dec(v___x_1033_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object* v___x_1042_, uint8_t v_useSplitter_1043_, lean_object* v_inst_1044_, lean_object* v_onAlt_1045_, lean_object* v_resTy_1046_, lean_object* v_toBind_1047_, lean_object* v_h_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___f_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1049_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1050_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1051_ = lean_mk_empty_array_with_capacity(v___x_1042_);
v___x_1052_ = lean_array_push(v___x_1051_, v_h_1048_);
v___x_1053_ = lean_box(v_useSplitter_1043_);
lean_inc_ref(v___x_1052_);
v___f_1054_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1054_, 0, v___x_1052_);
lean_closure_set(v___f_1054_, 1, v___x_1053_);
lean_closure_set(v___f_1054_, 2, v_inst_1044_);
v___x_1055_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1050_);
lean_ctor_set(v___x_1055_, 1, v___x_1052_);
lean_ctor_set(v___x_1055_, 2, v___x_1050_);
lean_ctor_set(v___x_1055_, 3, v___x_1050_);
lean_ctor_set(v___x_1055_, 4, v___x_1050_);
v___x_1056_ = lean_apply_4(v_onAlt_1045_, v___x_1049_, v_resTy_1046_, v___x_1042_, v___x_1055_);
v___x_1057_ = lean_apply_4(v_toBind_1047_, lean_box(0), lean_box(0), v___x_1056_, v___f_1054_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object* v___x_1058_, lean_object* v_useSplitter_1059_, lean_object* v_inst_1060_, lean_object* v_onAlt_1061_, lean_object* v_resTy_1062_, lean_object* v_toBind_1063_, lean_object* v_h_1064_){
_start:
{
uint8_t v_useSplitter_boxed_1065_; lean_object* v_res_1066_; 
v_useSplitter_boxed_1065_ = lean_unbox(v_useSplitter_1059_);
v_res_1066_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(v___x_1058_, v_useSplitter_boxed_1065_, v_inst_1060_, v_onAlt_1061_, v_resTy_1062_, v_toBind_1063_, v_h_1064_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object* v_u_1067_, lean_object* v_resTy_1068_, lean_object* v_c_1069_, lean_object* v_h_1070_, lean_object* v_t_1071_, lean_object* v_toPure_1072_, lean_object* v_e_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_1075_ = lean_box(0);
v___x_1076_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1076_, 0, v_u_1067_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = l_Lean_mkConst(v___x_1074_, v___x_1076_);
v___x_1078_ = l_Lean_mkApp5(v___x_1077_, v_resTy_1068_, v_c_1069_, v_h_1070_, v_t_1071_, v_e_1073_);
v___x_1079_ = lean_apply_2(v_toPure_1072_, lean_box(0), v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object* v_u_1080_, lean_object* v_resTy_1081_, lean_object* v_c_1082_, lean_object* v_h_1083_, lean_object* v_toPure_1084_, lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_n_1087_, uint8_t v___x_1088_, lean_object* v___f_1089_, uint8_t v___x_1090_, lean_object* v_toBind_1091_, lean_object* v_t_1092_){
_start:
{
lean_object* v___f_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_inc_ref(v_c_1082_);
v___f_1093_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1093_, 0, v_u_1080_);
lean_closure_set(v___f_1093_, 1, v_resTy_1081_);
lean_closure_set(v___f_1093_, 2, v_c_1082_);
lean_closure_set(v___f_1093_, 3, v_h_1083_);
lean_closure_set(v___f_1093_, 4, v_t_1092_);
lean_closure_set(v___f_1093_, 5, v_toPure_1084_);
v___x_1094_ = l_Lean_mkNot(v_c_1082_);
v___x_1095_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1085_, v_inst_1086_, v_n_1087_, v___x_1088_, v___x_1094_, v___f_1089_, v___x_1090_);
v___x_1096_ = lean_apply_4(v_toBind_1091_, lean_box(0), lean_box(0), v___x_1095_, v___f_1093_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object* v_u_1097_, lean_object* v_resTy_1098_, lean_object* v_c_1099_, lean_object* v_h_1100_, lean_object* v_toPure_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_, lean_object* v_n_1104_, lean_object* v___x_1105_, lean_object* v___f_1106_, lean_object* v___x_1107_, lean_object* v_toBind_1108_, lean_object* v_t_1109_){
_start:
{
uint8_t v___x_1659__boxed_1110_; uint8_t v___x_1661__boxed_1111_; lean_object* v_res_1112_; 
v___x_1659__boxed_1110_ = lean_unbox(v___x_1105_);
v___x_1661__boxed_1111_ = lean_unbox(v___x_1107_);
v_res_1112_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(v_u_1097_, v_resTy_1098_, v_c_1099_, v_h_1100_, v_toPure_1101_, v_inst_1102_, v_inst_1103_, v_n_1104_, v___x_1659__boxed_1110_, v___f_1106_, v___x_1661__boxed_1111_, v_toBind_1108_, v_t_1109_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object* v_u_1113_, lean_object* v_resTy_1114_, lean_object* v_c_1115_, lean_object* v_h_1116_, lean_object* v_toPure_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v___f_1120_, lean_object* v_toBind_1121_, lean_object* v___f_1122_, lean_object* v_n_1123_){
_start:
{
uint8_t v___x_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1124_ = 0;
v___x_1125_ = 0;
v___x_1126_ = lean_box(v___x_1124_);
v___x_1127_ = lean_box(v___x_1125_);
lean_inc(v_toBind_1121_);
lean_inc(v_n_1123_);
lean_inc_ref(v_inst_1119_);
lean_inc_ref(v_inst_1118_);
lean_inc_ref(v_c_1115_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1128_, 0, v_u_1113_);
lean_closure_set(v___f_1128_, 1, v_resTy_1114_);
lean_closure_set(v___f_1128_, 2, v_c_1115_);
lean_closure_set(v___f_1128_, 3, v_h_1116_);
lean_closure_set(v___f_1128_, 4, v_toPure_1117_);
lean_closure_set(v___f_1128_, 5, v_inst_1118_);
lean_closure_set(v___f_1128_, 6, v_inst_1119_);
lean_closure_set(v___f_1128_, 7, v_n_1123_);
lean_closure_set(v___f_1128_, 8, v___x_1126_);
lean_closure_set(v___f_1128_, 9, v___f_1120_);
lean_closure_set(v___f_1128_, 10, v___x_1127_);
lean_closure_set(v___f_1128_, 11, v_toBind_1121_);
v___x_1129_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1118_, v_inst_1119_, v_n_1123_, v___x_1124_, v_c_1115_, v___f_1122_, v___x_1125_);
v___x_1130_ = lean_apply_4(v_toBind_1121_, lean_box(0), lean_box(0), v___x_1129_, v___f_1128_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object* v___x_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_Core_mkFreshUserName(v___x_1131_, v___y_1134_, v___y_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object* v___x_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(v___x_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object* v_e_1152_, uint8_t v_useSplitter_1153_, lean_object* v_resTy_1154_, lean_object* v_toPure_1155_, lean_object* v_onAlt_1156_, lean_object* v_toBind_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_u_1161_){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_c_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v_h_1170_; 
v___x_1162_ = lean_unsigned_to_nat(1u);
v___x_1163_ = l_Lean_Expr_getAppNumArgs(v_e_1152_);
v___x_1164_ = lean_nat_sub(v___x_1163_, v___x_1162_);
v___x_1165_ = lean_nat_sub(v___x_1164_, v___x_1162_);
lean_dec(v___x_1164_);
v_c_1166_ = l_Lean_Expr_getRevArg_x21(v_e_1152_, v___x_1165_);
v___x_1167_ = lean_unsigned_to_nat(2u);
v___x_1168_ = lean_nat_sub(v___x_1163_, v___x_1167_);
lean_dec(v___x_1163_);
v___x_1169_ = lean_nat_sub(v___x_1168_, v___x_1162_);
lean_dec(v___x_1168_);
v_h_1170_ = l_Lean_Expr_getRevArg_x21(v_e_1152_, v___x_1169_);
if (v_useSplitter_1153_ == 0)
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_dec_ref(v_inst_1160_);
lean_dec_ref(v_inst_1159_);
lean_dec(v_inst_1158_);
v___x_1171_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1172_ = lean_unsigned_to_nat(0u);
v___x_1173_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1157_);
lean_inc(v_onAlt_1156_);
lean_inc_ref(v_resTy_1154_);
v___f_1174_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1174_, 0, v_u_1161_);
lean_closure_set(v___f_1174_, 1, v_resTy_1154_);
lean_closure_set(v___f_1174_, 2, v_c_1166_);
lean_closure_set(v___f_1174_, 3, v_h_1170_);
lean_closure_set(v___f_1174_, 4, v_toPure_1155_);
lean_closure_set(v___f_1174_, 5, v_onAlt_1156_);
lean_closure_set(v___f_1174_, 6, v___x_1162_);
lean_closure_set(v___f_1174_, 7, v___x_1173_);
lean_closure_set(v___f_1174_, 8, v_toBind_1157_);
v___x_1175_ = lean_apply_4(v_onAlt_1156_, v___x_1171_, v_resTy_1154_, v___x_1172_, v___x_1173_);
v___x_1176_ = lean_apply_4(v_toBind_1157_, lean_box(0), lean_box(0), v___x_1175_, v___f_1174_);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___f_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1177_ = lean_box(v_useSplitter_1153_);
lean_inc_n(v_toBind_1157_, 3);
lean_inc_ref_n(v_resTy_1154_, 2);
lean_inc(v_onAlt_1156_);
lean_inc_n(v_inst_1158_, 2);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1178_, 0, v___x_1162_);
lean_closure_set(v___f_1178_, 1, v___x_1177_);
lean_closure_set(v___f_1178_, 2, v_inst_1158_);
lean_closure_set(v___f_1178_, 3, v_onAlt_1156_);
lean_closure_set(v___f_1178_, 4, v_resTy_1154_);
lean_closure_set(v___f_1178_, 5, v_toBind_1157_);
v___x_1179_ = lean_box(v_useSplitter_1153_);
v___f_1180_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1180_, 0, v___x_1162_);
lean_closure_set(v___f_1180_, 1, v___x_1179_);
lean_closure_set(v___f_1180_, 2, v_inst_1158_);
lean_closure_set(v___f_1180_, 3, v_onAlt_1156_);
lean_closure_set(v___f_1180_, 4, v_resTy_1154_);
lean_closure_set(v___f_1180_, 5, v_toBind_1157_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1181_, 0, v_u_1161_);
lean_closure_set(v___f_1181_, 1, v_resTy_1154_);
lean_closure_set(v___f_1181_, 2, v_c_1166_);
lean_closure_set(v___f_1181_, 3, v_h_1170_);
lean_closure_set(v___f_1181_, 4, v_toPure_1155_);
lean_closure_set(v___f_1181_, 5, v_inst_1159_);
lean_closure_set(v___f_1181_, 6, v_inst_1160_);
lean_closure_set(v___f_1181_, 7, v___f_1180_);
lean_closure_set(v___f_1181_, 8, v_toBind_1157_);
lean_closure_set(v___f_1181_, 9, v___f_1178_);
v___f_1182_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1183_ = lean_apply_2(v_inst_1158_, lean_box(0), v___f_1182_);
v___x_1184_ = lean_apply_4(v_toBind_1157_, lean_box(0), lean_box(0), v___x_1183_, v___f_1181_);
return v___x_1184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object* v_e_1185_, lean_object* v_useSplitter_1186_, lean_object* v_resTy_1187_, lean_object* v_toPure_1188_, lean_object* v_onAlt_1189_, lean_object* v_toBind_1190_, lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_u_1194_){
_start:
{
uint8_t v_useSplitter_boxed_1195_; lean_object* v_res_1196_; 
v_useSplitter_boxed_1195_ = lean_unbox(v_useSplitter_1186_);
v_res_1196_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(v_e_1185_, v_useSplitter_boxed_1195_, v_resTy_1187_, v_toPure_1188_, v_onAlt_1189_, v_toBind_1190_, v_inst_1191_, v_inst_1192_, v_inst_1193_, v_u_1194_);
lean_dec_ref(v_e_1185_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object* v___x_1197_, lean_object* v_inst_1198_, lean_object* v_____do__lift_1199_){
_start:
{
uint8_t v___x_1200_; uint8_t v___x_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1200_ = 0;
v___x_1201_ = 1;
v___x_1202_ = 1;
v___x_1203_ = lean_box(v___x_1200_);
v___x_1204_ = lean_box(v___x_1201_);
v___x_1205_ = lean_box(v___x_1200_);
v___x_1206_ = lean_box(v___x_1201_);
v___x_1207_ = lean_box(v___x_1202_);
v___x_1208_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1208_, 0, v___x_1197_);
lean_closure_set(v___x_1208_, 1, v_____do__lift_1199_);
lean_closure_set(v___x_1208_, 2, v___x_1203_);
lean_closure_set(v___x_1208_, 3, v___x_1204_);
lean_closure_set(v___x_1208_, 4, v___x_1205_);
lean_closure_set(v___x_1208_, 5, v___x_1206_);
lean_closure_set(v___x_1208_, 6, v___x_1207_);
v___x_1209_ = lean_apply_2(v_inst_1198_, lean_box(0), v___x_1208_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object* v_inst_1210_, lean_object* v_onAlt_1211_, lean_object* v_resTy_1212_, lean_object* v_toBind_1213_, lean_object* v_h_1214_){
_start:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___f_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1215_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_unsigned_to_nat(1u);
v___x_1218_ = lean_mk_empty_array_with_capacity(v___x_1217_);
v___x_1219_ = lean_array_push(v___x_1218_, v_h_1214_);
lean_inc_ref_n(v___x_1219_, 2);
v___f_1220_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1220_, 0, v___x_1219_);
lean_closure_set(v___f_1220_, 1, v_inst_1210_);
v___x_1221_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1219_);
lean_ctor_set(v___x_1222_, 1, v___x_1219_);
lean_ctor_set(v___x_1222_, 2, v___x_1221_);
lean_ctor_set(v___x_1222_, 3, v___x_1221_);
lean_ctor_set(v___x_1222_, 4, v___x_1221_);
v___x_1223_ = lean_apply_4(v_onAlt_1211_, v___x_1215_, v_resTy_1212_, v___x_1216_, v___x_1222_);
v___x_1224_ = lean_apply_4(v_toBind_1213_, lean_box(0), lean_box(0), v___x_1223_, v___f_1220_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object* v___x_1225_, lean_object* v_inst_1226_, lean_object* v_onAlt_1227_, lean_object* v_resTy_1228_, lean_object* v_toBind_1229_, lean_object* v_h_1230_){
_start:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___f_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1231_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1232_ = lean_mk_empty_array_with_capacity(v___x_1225_);
v___x_1233_ = lean_array_push(v___x_1232_, v_h_1230_);
lean_inc_ref_n(v___x_1233_, 2);
v___f_1234_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1234_, 0, v___x_1233_);
lean_closure_set(v___f_1234_, 1, v_inst_1226_);
v___x_1235_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1236_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1236_, 0, v___x_1233_);
lean_ctor_set(v___x_1236_, 1, v___x_1233_);
lean_ctor_set(v___x_1236_, 2, v___x_1235_);
lean_ctor_set(v___x_1236_, 3, v___x_1235_);
lean_ctor_set(v___x_1236_, 4, v___x_1235_);
v___x_1237_ = lean_apply_4(v_onAlt_1227_, v___x_1231_, v_resTy_1228_, v___x_1225_, v___x_1236_);
v___x_1238_ = lean_apply_4(v_toBind_1229_, lean_box(0), lean_box(0), v___x_1237_, v___f_1234_);
return v___x_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object* v_inst_1239_, lean_object* v_onAlt_1240_, lean_object* v_resTy_1241_, lean_object* v_toBind_1242_, lean_object* v_e_1243_, lean_object* v_toPure_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v___f_1247_, lean_object* v_u_1248_){
_start:
{
lean_object* v___x_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_c_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v_h_1258_; lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1249_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_toBind_1242_, 2);
lean_inc_ref(v_resTy_1241_);
lean_inc(v_inst_1239_);
v___f_1250_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13), 6, 5);
lean_closure_set(v___f_1250_, 0, v___x_1249_);
lean_closure_set(v___f_1250_, 1, v_inst_1239_);
lean_closure_set(v___f_1250_, 2, v_onAlt_1240_);
lean_closure_set(v___f_1250_, 3, v_resTy_1241_);
lean_closure_set(v___f_1250_, 4, v_toBind_1242_);
v___x_1251_ = l_Lean_Expr_getAppNumArgs(v_e_1243_);
v___x_1252_ = lean_nat_sub(v___x_1251_, v___x_1249_);
v___x_1253_ = lean_nat_sub(v___x_1252_, v___x_1249_);
lean_dec(v___x_1252_);
v_c_1254_ = l_Lean_Expr_getRevArg_x21(v_e_1243_, v___x_1253_);
v___x_1255_ = lean_unsigned_to_nat(2u);
v___x_1256_ = lean_nat_sub(v___x_1251_, v___x_1255_);
lean_dec(v___x_1251_);
v___x_1257_ = lean_nat_sub(v___x_1256_, v___x_1249_);
lean_dec(v___x_1256_);
v_h_1258_ = l_Lean_Expr_getRevArg_x21(v_e_1243_, v___x_1257_);
v___f_1259_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1259_, 0, v_u_1248_);
lean_closure_set(v___f_1259_, 1, v_resTy_1241_);
lean_closure_set(v___f_1259_, 2, v_c_1254_);
lean_closure_set(v___f_1259_, 3, v_h_1258_);
lean_closure_set(v___f_1259_, 4, v_toPure_1244_);
lean_closure_set(v___f_1259_, 5, v_inst_1245_);
lean_closure_set(v___f_1259_, 6, v_inst_1246_);
lean_closure_set(v___f_1259_, 7, v___f_1250_);
lean_closure_set(v___f_1259_, 8, v_toBind_1242_);
lean_closure_set(v___f_1259_, 9, v___f_1247_);
v___f_1260_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1261_ = lean_apply_2(v_inst_1239_, lean_box(0), v___f_1260_);
v___x_1262_ = lean_apply_4(v_toBind_1242_, lean_box(0), lean_box(0), v___x_1261_, v___f_1259_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object* v_inst_1263_, lean_object* v_onAlt_1264_, lean_object* v_resTy_1265_, lean_object* v_toBind_1266_, lean_object* v_e_1267_, lean_object* v_toPure_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v___f_1271_, lean_object* v_u_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(v_inst_1263_, v_onAlt_1264_, v_resTy_1265_, v_toBind_1266_, v_e_1267_, v_toPure_1268_, v_inst_1269_, v_inst_1270_, v___f_1271_, v_u_1272_);
lean_dec_ref(v_e_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object* v_u_1274_, lean_object* v_resTy_1275_, lean_object* v_c_1276_, lean_object* v_t_1277_, lean_object* v_toPure_1278_, lean_object* v_e_1279_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1282_, 0, v_u_1274_);
lean_ctor_set(v___x_1282_, 1, v___x_1281_);
v___x_1283_ = l_Lean_mkConst(v___x_1280_, v___x_1282_);
v___x_1284_ = l_Lean_mkApp4(v___x_1283_, v_resTy_1275_, v_c_1276_, v_t_1277_, v_e_1279_);
v___x_1285_ = lean_apply_2(v_toPure_1278_, lean_box(0), v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object* v_u_1286_, lean_object* v_resTy_1287_, lean_object* v_c_1288_, lean_object* v_toPure_1289_, lean_object* v_onAlt_1290_, lean_object* v___x_1291_, lean_object* v___x_1292_, lean_object* v_toBind_1293_, lean_object* v_t_1294_){
_start:
{
lean_object* v___f_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_inc_ref(v_resTy_1287_);
v___f_1295_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12), 6, 5);
lean_closure_set(v___f_1295_, 0, v_u_1286_);
lean_closure_set(v___f_1295_, 1, v_resTy_1287_);
lean_closure_set(v___f_1295_, 2, v_c_1288_);
lean_closure_set(v___f_1295_, 3, v_t_1294_);
lean_closure_set(v___f_1295_, 4, v_toPure_1289_);
v___x_1296_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1297_ = lean_apply_4(v_onAlt_1290_, v___x_1296_, v_resTy_1287_, v___x_1291_, v___x_1292_);
v___x_1298_ = lean_apply_4(v_toBind_1293_, lean_box(0), lean_box(0), v___x_1297_, v___f_1295_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20(lean_object* v___x_1300_, lean_object* v_u_1301_, lean_object* v___x_1302_, lean_object* v_resTy_1303_, lean_object* v_c_1304_, lean_object* v_t_1305_, lean_object* v_toPure_1306_, lean_object* v_e_1307_){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1308_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20___closed__0));
v___x_1309_ = l_Lean_Name_mkStr2(v___x_1300_, v___x_1308_);
v___x_1310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_u_1301_);
lean_ctor_set(v___x_1310_, 1, v___x_1302_);
v___x_1311_ = l_Lean_mkConst(v___x_1309_, v___x_1310_);
v___x_1312_ = l_Lean_mkApp4(v___x_1311_, v_resTy_1303_, v_c_1304_, v_t_1305_, v_e_1307_);
v___x_1313_ = lean_apply_2(v_toPure_1306_, lean_box(0), v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object* v___x_1314_, lean_object* v_u_1315_, lean_object* v___x_1316_, lean_object* v_resTy_1317_, lean_object* v_c_1318_, lean_object* v_toPure_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_n_1322_, uint8_t v___x_1323_, lean_object* v_hFalse_1324_, lean_object* v___f_1325_, uint8_t v___x_1326_, lean_object* v_toBind_1327_, lean_object* v_t_1328_){
_start:
{
lean_object* v___f_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___f_1329_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20), 8, 7);
lean_closure_set(v___f_1329_, 0, v___x_1314_);
lean_closure_set(v___f_1329_, 1, v_u_1315_);
lean_closure_set(v___f_1329_, 2, v___x_1316_);
lean_closure_set(v___f_1329_, 3, v_resTy_1317_);
lean_closure_set(v___f_1329_, 4, v_c_1318_);
lean_closure_set(v___f_1329_, 5, v_t_1328_);
lean_closure_set(v___f_1329_, 6, v_toPure_1319_);
v___x_1330_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1320_, v_inst_1321_, v_n_1322_, v___x_1323_, v_hFalse_1324_, v___f_1325_, v___x_1326_);
v___x_1331_ = lean_apply_4(v_toBind_1327_, lean_box(0), lean_box(0), v___x_1330_, v___f_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object* v___x_1332_, lean_object* v_u_1333_, lean_object* v___x_1334_, lean_object* v_resTy_1335_, lean_object* v_c_1336_, lean_object* v_toPure_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_n_1340_, lean_object* v___x_1341_, lean_object* v_hFalse_1342_, lean_object* v___f_1343_, lean_object* v___x_1344_, lean_object* v_toBind_1345_, lean_object* v_t_1346_){
_start:
{
uint8_t v___x_1992__boxed_1347_; uint8_t v___x_1994__boxed_1348_; lean_object* v_res_1349_; 
v___x_1992__boxed_1347_ = lean_unbox(v___x_1341_);
v___x_1994__boxed_1348_ = lean_unbox(v___x_1344_);
v_res_1349_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(v___x_1332_, v_u_1333_, v___x_1334_, v_resTy_1335_, v_c_1336_, v_toPure_1337_, v_inst_1338_, v_inst_1339_, v_n_1340_, v___x_1992__boxed_1347_, v_hFalse_1342_, v___f_1343_, v___x_1994__boxed_1348_, v_toBind_1345_, v_t_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16(lean_object* v___x_1350_, lean_object* v_u_1351_, lean_object* v___x_1352_, lean_object* v_resTy_1353_, lean_object* v_c_1354_, lean_object* v_toPure_1355_, lean_object* v_inst_1356_, lean_object* v_inst_1357_, lean_object* v_n_1358_, lean_object* v___f_1359_, lean_object* v_toBind_1360_, lean_object* v_hTrue_1361_, lean_object* v___f_1362_, lean_object* v_hFalse_1363_){
_start:
{
uint8_t v___x_1364_; uint8_t v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___f_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1364_ = 0;
v___x_1365_ = 0;
v___x_1366_ = lean_box(v___x_1364_);
v___x_1367_ = lean_box(v___x_1365_);
lean_inc(v_toBind_1360_);
lean_inc(v_n_1358_);
lean_inc_ref(v_inst_1357_);
lean_inc_ref(v_inst_1356_);
v___f_1368_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed), 15, 14);
lean_closure_set(v___f_1368_, 0, v___x_1350_);
lean_closure_set(v___f_1368_, 1, v_u_1351_);
lean_closure_set(v___f_1368_, 2, v___x_1352_);
lean_closure_set(v___f_1368_, 3, v_resTy_1353_);
lean_closure_set(v___f_1368_, 4, v_c_1354_);
lean_closure_set(v___f_1368_, 5, v_toPure_1355_);
lean_closure_set(v___f_1368_, 6, v_inst_1356_);
lean_closure_set(v___f_1368_, 7, v_inst_1357_);
lean_closure_set(v___f_1368_, 8, v_n_1358_);
lean_closure_set(v___f_1368_, 9, v___x_1366_);
lean_closure_set(v___f_1368_, 10, v_hFalse_1363_);
lean_closure_set(v___f_1368_, 11, v___f_1359_);
lean_closure_set(v___f_1368_, 12, v___x_1367_);
lean_closure_set(v___f_1368_, 13, v_toBind_1360_);
v___x_1369_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1356_, v_inst_1357_, v_n_1358_, v___x_1364_, v_hTrue_1361_, v___f_1362_, v___x_1365_);
v___x_1370_ = lean_apply_4(v_toBind_1360_, lean_box(0), lean_box(0), v___x_1369_, v___f_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18(lean_object* v___x_1372_, lean_object* v_u_1373_, lean_object* v___x_1374_, lean_object* v_resTy_1375_, lean_object* v_c_1376_, lean_object* v_toPure_1377_, lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_n_1380_, lean_object* v___f_1381_, lean_object* v_toBind_1382_, lean_object* v___f_1383_, lean_object* v_inst_1384_, lean_object* v_hTrue_1385_){
_start:
{
lean_object* v___f_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_inc(v_toBind_1382_);
lean_inc_ref(v_c_1376_);
lean_inc(v___x_1374_);
lean_inc_ref(v___x_1372_);
v___f_1386_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16), 14, 13);
lean_closure_set(v___f_1386_, 0, v___x_1372_);
lean_closure_set(v___f_1386_, 1, v_u_1373_);
lean_closure_set(v___f_1386_, 2, v___x_1374_);
lean_closure_set(v___f_1386_, 3, v_resTy_1375_);
lean_closure_set(v___f_1386_, 4, v_c_1376_);
lean_closure_set(v___f_1386_, 5, v_toPure_1377_);
lean_closure_set(v___f_1386_, 6, v_inst_1378_);
lean_closure_set(v___f_1386_, 7, v_inst_1379_);
lean_closure_set(v___f_1386_, 8, v_n_1380_);
lean_closure_set(v___f_1386_, 9, v___f_1381_);
lean_closure_set(v___f_1386_, 10, v_toBind_1382_);
lean_closure_set(v___f_1386_, 11, v_hTrue_1385_);
lean_closure_set(v___f_1386_, 12, v___f_1383_);
v___x_1387_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0));
v___x_1388_ = l_Lean_Name_mkStr2(v___x_1372_, v___x_1387_);
v___x_1389_ = l_Lean_mkConst(v___x_1388_, v___x_1374_);
v___x_1390_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_1390_, 0, v_c_1376_);
lean_closure_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = lean_apply_2(v_inst_1384_, lean_box(0), v___x_1390_);
v___x_1392_ = lean_apply_4(v_toBind_1382_, lean_box(0), lean_box(0), v___x_1391_, v___f_1386_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1397_ = lean_box(0);
v___x_1398_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1));
v___x_1399_ = l_Lean_mkConst(v___x_1398_, v___x_1397_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19(lean_object* v_u_1400_, lean_object* v_resTy_1401_, lean_object* v_c_1402_, lean_object* v_toPure_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_, lean_object* v___f_1406_, lean_object* v_toBind_1407_, lean_object* v___f_1408_, lean_object* v_inst_1409_, lean_object* v_n_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___f_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1411_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10));
v___x_1412_ = lean_box(0);
lean_inc(v_inst_1409_);
lean_inc(v_toBind_1407_);
lean_inc_ref(v_c_1402_);
v___f_1413_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18), 14, 13);
lean_closure_set(v___f_1413_, 0, v___x_1411_);
lean_closure_set(v___f_1413_, 1, v_u_1400_);
lean_closure_set(v___f_1413_, 2, v___x_1412_);
lean_closure_set(v___f_1413_, 3, v_resTy_1401_);
lean_closure_set(v___f_1413_, 4, v_c_1402_);
lean_closure_set(v___f_1413_, 5, v_toPure_1403_);
lean_closure_set(v___f_1413_, 6, v_inst_1404_);
lean_closure_set(v___f_1413_, 7, v_inst_1405_);
lean_closure_set(v___f_1413_, 8, v_n_1410_);
lean_closure_set(v___f_1413_, 9, v___f_1406_);
lean_closure_set(v___f_1413_, 10, v_toBind_1407_);
lean_closure_set(v___f_1413_, 11, v___f_1408_);
lean_closure_set(v___f_1413_, 12, v_inst_1409_);
v___x_1414_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2, &l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2);
v___x_1415_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_1415_, 0, v_c_1402_);
lean_closure_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = lean_apply_2(v_inst_1409_, lean_box(0), v___x_1415_);
v___x_1417_ = lean_apply_4(v_toBind_1407_, lean_box(0), lean_box(0), v___x_1416_, v___f_1413_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(lean_object* v_e_1418_, uint8_t v_useSplitter_1419_, lean_object* v_resTy_1420_, lean_object* v_toPure_1421_, lean_object* v_onAlt_1422_, lean_object* v_toBind_1423_, lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_u_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v_c_1432_; 
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = l_Lean_Expr_getAppNumArgs(v_e_1418_);
v___x_1430_ = lean_nat_sub(v___x_1429_, v___x_1428_);
lean_dec(v___x_1429_);
v___x_1431_ = lean_nat_sub(v___x_1430_, v___x_1428_);
lean_dec(v___x_1430_);
v_c_1432_ = l_Lean_Expr_getRevArg_x21(v_e_1418_, v___x_1431_);
if (v_useSplitter_1419_ == 0)
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___f_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
lean_dec_ref(v_inst_1426_);
lean_dec_ref(v_inst_1425_);
lean_dec(v_inst_1424_);
v___x_1433_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1423_);
lean_inc(v_onAlt_1422_);
lean_inc_ref(v_resTy_1420_);
v___f_1436_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14), 9, 8);
lean_closure_set(v___f_1436_, 0, v_u_1427_);
lean_closure_set(v___f_1436_, 1, v_resTy_1420_);
lean_closure_set(v___f_1436_, 2, v_c_1432_);
lean_closure_set(v___f_1436_, 3, v_toPure_1421_);
lean_closure_set(v___f_1436_, 4, v_onAlt_1422_);
lean_closure_set(v___f_1436_, 5, v___x_1428_);
lean_closure_set(v___f_1436_, 6, v___x_1435_);
lean_closure_set(v___f_1436_, 7, v_toBind_1423_);
v___x_1437_ = lean_apply_4(v_onAlt_1422_, v___x_1433_, v_resTy_1420_, v___x_1434_, v___x_1435_);
v___x_1438_ = lean_apply_4(v_toBind_1423_, lean_box(0), lean_box(0), v___x_1437_, v___f_1436_);
return v___x_1438_;
}
else
{
lean_object* v___x_1439_; lean_object* v___f_1440_; lean_object* v___x_1441_; lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___f_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1439_ = lean_box(v_useSplitter_1419_);
lean_inc_n(v_toBind_1423_, 3);
lean_inc_ref_n(v_resTy_1420_, 2);
lean_inc(v_onAlt_1422_);
lean_inc_n(v_inst_1424_, 3);
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1440_, 0, v___x_1428_);
lean_closure_set(v___f_1440_, 1, v___x_1439_);
lean_closure_set(v___f_1440_, 2, v_inst_1424_);
lean_closure_set(v___f_1440_, 3, v_onAlt_1422_);
lean_closure_set(v___f_1440_, 4, v_resTy_1420_);
lean_closure_set(v___f_1440_, 5, v_toBind_1423_);
v___x_1441_ = lean_box(v_useSplitter_1419_);
v___f_1442_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1442_, 0, v___x_1428_);
lean_closure_set(v___f_1442_, 1, v___x_1441_);
lean_closure_set(v___f_1442_, 2, v_inst_1424_);
lean_closure_set(v___f_1442_, 3, v_onAlt_1422_);
lean_closure_set(v___f_1442_, 4, v_resTy_1420_);
lean_closure_set(v___f_1442_, 5, v_toBind_1423_);
v___f_1443_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19), 11, 10);
lean_closure_set(v___f_1443_, 0, v_u_1427_);
lean_closure_set(v___f_1443_, 1, v_resTy_1420_);
lean_closure_set(v___f_1443_, 2, v_c_1432_);
lean_closure_set(v___f_1443_, 3, v_toPure_1421_);
lean_closure_set(v___f_1443_, 4, v_inst_1425_);
lean_closure_set(v___f_1443_, 5, v_inst_1426_);
lean_closure_set(v___f_1443_, 6, v___f_1442_);
lean_closure_set(v___f_1443_, 7, v_toBind_1423_);
lean_closure_set(v___f_1443_, 8, v___f_1440_);
lean_closure_set(v___f_1443_, 9, v_inst_1424_);
v___f_1444_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1445_ = lean_apply_2(v_inst_1424_, lean_box(0), v___f_1444_);
v___x_1446_ = lean_apply_4(v_toBind_1423_, lean_box(0), lean_box(0), v___x_1445_, v___f_1443_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22___boxed(lean_object* v_e_1447_, lean_object* v_useSplitter_1448_, lean_object* v_resTy_1449_, lean_object* v_toPure_1450_, lean_object* v_onAlt_1451_, lean_object* v_toBind_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_u_1456_){
_start:
{
uint8_t v_useSplitter_boxed_1457_; lean_object* v_res_1458_; 
v_useSplitter_boxed_1457_ = lean_unbox(v_useSplitter_1448_);
v_res_1458_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(v_e_1447_, v_useSplitter_boxed_1457_, v_resTy_1449_, v_toPure_1450_, v_onAlt_1451_, v_toBind_1452_, v_inst_1453_, v_inst_1454_, v_inst_1455_, v_u_1456_);
lean_dec_ref(v_e_1447_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21(lean_object* v_onAlt_1459_, lean_object* v_idx_1460_, lean_object* v_expAltType_1461_, lean_object* v_altFVars_1462_, lean_object* v___alt_1463_){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1464_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2));
v___x_1465_ = lean_unsigned_to_nat(1u);
v___x_1466_ = lean_nat_add(v_idx_1460_, v___x_1465_);
v___x_1467_ = lean_name_append_index_after(v___x_1464_, v___x_1466_);
v___x_1468_ = lean_apply_4(v_onAlt_1459_, v___x_1467_, v_expAltType_1461_, v_idx_1460_, v_altFVars_1462_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21___boxed(lean_object* v_onAlt_1469_, lean_object* v_idx_1470_, lean_object* v_expAltType_1471_, lean_object* v_altFVars_1472_, lean_object* v___alt_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21(v_onAlt_1469_, v_idx_1470_, v_expAltType_1471_, v_altFVars_1472_, v___alt_1473_);
lean_dec_ref(v___alt_1473_);
return v_res_1474_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(lean_object* v_toMatcherInfo_1475_, lean_object* v_i_1476_, lean_object* v_a_1477_, lean_object* v_x_1478_){
_start:
{
uint8_t v___x_1479_; 
v___x_1479_ = l_Lean_Expr_isFVar(v_a_1477_);
if (v___x_1479_ == 0)
{
return v___x_1479_;
}
else
{
lean_object* v_discrInfos_1480_; lean_object* v___x_1481_; uint8_t v___x_1482_; 
v_discrInfos_1480_ = lean_ctor_get(v_toMatcherInfo_1475_, 4);
v___x_1481_ = lean_array_get_size(v_discrInfos_1480_);
v___x_1482_ = lean_nat_dec_lt(v_i_1476_, v___x_1481_);
if (v___x_1482_ == 0)
{
return v___x_1479_;
}
else
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_array_fget_borrowed(v_discrInfos_1480_, v_i_1476_);
if (lean_obj_tag(v___x_1483_) == 0)
{
return v___x_1479_;
}
else
{
uint8_t v___x_1484_; 
v___x_1484_ = 0;
return v___x_1484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23___boxed(lean_object* v_toMatcherInfo_1485_, lean_object* v_i_1486_, lean_object* v_a_1487_, lean_object* v_x_1488_){
_start:
{
uint8_t v_res_1489_; lean_object* v_r_1490_; 
v_res_1489_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(v_toMatcherInfo_1485_, v_i_1486_, v_a_1487_, v_x_1488_);
lean_dec_ref(v_a_1487_);
lean_dec(v_i_1486_);
lean_dec_ref(v_toMatcherInfo_1485_);
v_r_1490_ = lean_box(v_res_1489_);
return v_r_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24(lean_object* v_mask_1491_, lean_object* v_absMotiveBody_1492_, lean_object* v_toPure_1493_, lean_object* v_xs_1494_, lean_object* v___body_1495_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1496_ = l_Lean_Array_mask___redArg(v_mask_1491_, v_xs_1494_);
v___x_1497_ = lean_expr_instantiate_rev(v_absMotiveBody_1492_, v___x_1496_);
lean_dec(v___x_1496_);
v___x_1498_ = lean_apply_2(v_toPure_1493_, lean_box(0), v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24___boxed(lean_object* v_mask_1499_, lean_object* v_absMotiveBody_1500_, lean_object* v_toPure_1501_, lean_object* v_xs_1502_, lean_object* v___body_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24(v_mask_1499_, v_absMotiveBody_1500_, v_toPure_1501_, v_xs_1502_, v___body_1503_);
lean_dec_ref(v___body_1503_);
lean_dec_ref(v_absMotiveBody_1500_);
lean_dec_ref(v_mask_1499_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(lean_object* v_toFunctor_1505_, lean_object* v_mask_1506_, lean_object* v_toPure_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_inst_1510_, lean_object* v_inst_1511_, lean_object* v_inst_1512_, lean_object* v_matcherApp_1513_, uint8_t v_useSplitter_1514_, lean_object* v___f_1515_, lean_object* v___f_1516_, lean_object* v_absMotiveBody_1517_){
_start:
{
lean_object* v_map_1518_; lean_object* v___f_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_map_1518_ = lean_ctor_get(v_toFunctor_1505_, 0);
lean_inc(v_map_1518_);
lean_dec_ref(v_toFunctor_1505_);
lean_inc(v_toPure_1507_);
v___f_1519_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24___boxed), 5, 3);
lean_closure_set(v___f_1519_, 0, v_mask_1506_);
lean_closure_set(v___f_1519_, 1, v_absMotiveBody_1517_);
lean_closure_set(v___f_1519_, 2, v_toPure_1507_);
v___x_1520_ = lean_apply_1(v_toPure_1507_, lean_box(0));
lean_inc(v___x_1520_);
v___x_1521_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_1508_, v_inst_1509_, v_inst_1510_, v_inst_1511_, v_inst_1512_, v_matcherApp_1513_, v_useSplitter_1514_, v_useSplitter_1514_, v___x_1520_, v___f_1519_, v___f_1515_, v___x_1520_);
v___x_1522_ = lean_apply_4(v_map_1518_, lean_box(0), lean_box(0), v___f_1516_, v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25___boxed(lean_object* v_toFunctor_1523_, lean_object* v_mask_1524_, lean_object* v_toPure_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_inst_1530_, lean_object* v_matcherApp_1531_, lean_object* v_useSplitter_1532_, lean_object* v___f_1533_, lean_object* v___f_1534_, lean_object* v_absMotiveBody_1535_){
_start:
{
uint8_t v_useSplitter_boxed_1536_; lean_object* v_res_1537_; 
v_useSplitter_boxed_1536_ = lean_unbox(v_useSplitter_1532_);
v_res_1537_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(v_toFunctor_1523_, v_mask_1524_, v_toPure_1525_, v_inst_1526_, v_inst_1527_, v_inst_1528_, v_inst_1529_, v_inst_1530_, v_matcherApp_1531_, v_useSplitter_boxed_1536_, v___f_1533_, v___f_1534_, v_absMotiveBody_1535_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_info_1544_, lean_object* v_resTy_1545_, lean_object* v_onAlt_1546_, uint8_t v_useSplitter_1547_){
_start:
{
switch(lean_obj_tag(v_info_1544_))
{
case 0:
{
lean_object* v_toApplicative_1548_; lean_object* v_toBind_1549_; lean_object* v_toPure_1550_; lean_object* v_e_1551_; lean_object* v___x_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_toApplicative_1548_ = lean_ctor_get(v_inst_1541_, 0);
lean_dec_ref(v_inst_1543_);
lean_dec_ref(v_inst_1542_);
v_toBind_1549_ = lean_ctor_get(v_inst_1541_, 1);
lean_inc_n(v_toBind_1549_, 2);
v_toPure_1550_ = lean_ctor_get(v_toApplicative_1548_, 1);
lean_inc(v_toPure_1550_);
v_e_1551_ = lean_ctor_get(v_info_1544_, 0);
lean_inc_ref(v_e_1551_);
lean_dec_ref_known(v_info_1544_, 1);
v___x_1552_ = lean_box(v_useSplitter_1547_);
lean_inc(v_inst_1539_);
lean_inc_ref(v_resTy_1545_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1553_, 0, v_e_1551_);
lean_closure_set(v___f_1553_, 1, v___x_1552_);
lean_closure_set(v___f_1553_, 2, v_resTy_1545_);
lean_closure_set(v___f_1553_, 3, v_toPure_1550_);
lean_closure_set(v___f_1553_, 4, v_onAlt_1546_);
lean_closure_set(v___f_1553_, 5, v_toBind_1549_);
lean_closure_set(v___f_1553_, 6, v_inst_1539_);
lean_closure_set(v___f_1553_, 7, v_inst_1540_);
lean_closure_set(v___f_1553_, 8, v_inst_1541_);
v___x_1554_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1554_, 0, v_resTy_1545_);
v___x_1555_ = lean_apply_2(v_inst_1539_, lean_box(0), v___x_1554_);
v___x_1556_ = lean_apply_4(v_toBind_1549_, lean_box(0), lean_box(0), v___x_1555_, v___f_1553_);
return v___x_1556_;
}
case 1:
{
lean_object* v_toApplicative_1557_; lean_object* v_toBind_1558_; lean_object* v_toPure_1559_; lean_object* v_e_1560_; lean_object* v___f_1561_; lean_object* v___f_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_toApplicative_1557_ = lean_ctor_get(v_inst_1541_, 0);
lean_dec_ref(v_inst_1543_);
lean_dec_ref(v_inst_1542_);
v_toBind_1558_ = lean_ctor_get(v_inst_1541_, 1);
lean_inc_n(v_toBind_1558_, 3);
v_toPure_1559_ = lean_ctor_get(v_toApplicative_1557_, 1);
lean_inc(v_toPure_1559_);
v_e_1560_ = lean_ctor_get(v_info_1544_, 0);
lean_inc_ref(v_e_1560_);
lean_dec_ref_known(v_info_1544_, 1);
lean_inc_ref_n(v_resTy_1545_, 2);
lean_inc(v_onAlt_1546_);
lean_inc_n(v_inst_1539_, 2);
v___f_1561_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11), 5, 4);
lean_closure_set(v___f_1561_, 0, v_inst_1539_);
lean_closure_set(v___f_1561_, 1, v_onAlt_1546_);
lean_closure_set(v___f_1561_, 2, v_resTy_1545_);
lean_closure_set(v___f_1561_, 3, v_toBind_1558_);
v___f_1562_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed), 10, 9);
lean_closure_set(v___f_1562_, 0, v_inst_1539_);
lean_closure_set(v___f_1562_, 1, v_onAlt_1546_);
lean_closure_set(v___f_1562_, 2, v_resTy_1545_);
lean_closure_set(v___f_1562_, 3, v_toBind_1558_);
lean_closure_set(v___f_1562_, 4, v_e_1560_);
lean_closure_set(v___f_1562_, 5, v_toPure_1559_);
lean_closure_set(v___f_1562_, 6, v_inst_1540_);
lean_closure_set(v___f_1562_, 7, v_inst_1541_);
lean_closure_set(v___f_1562_, 8, v___f_1561_);
v___x_1563_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1563_, 0, v_resTy_1545_);
v___x_1564_ = lean_apply_2(v_inst_1539_, lean_box(0), v___x_1563_);
v___x_1565_ = lean_apply_4(v_toBind_1558_, lean_box(0), lean_box(0), v___x_1564_, v___f_1562_);
return v___x_1565_;
}
case 2:
{
lean_object* v_toApplicative_1566_; lean_object* v_toBind_1567_; lean_object* v_toPure_1568_; lean_object* v_e_1569_; lean_object* v___x_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v_toApplicative_1566_ = lean_ctor_get(v_inst_1541_, 0);
lean_dec_ref(v_inst_1543_);
lean_dec_ref(v_inst_1542_);
v_toBind_1567_ = lean_ctor_get(v_inst_1541_, 1);
lean_inc_n(v_toBind_1567_, 2);
v_toPure_1568_ = lean_ctor_get(v_toApplicative_1566_, 1);
lean_inc(v_toPure_1568_);
v_e_1569_ = lean_ctor_get(v_info_1544_, 0);
lean_inc_ref(v_e_1569_);
lean_dec_ref_known(v_info_1544_, 1);
v___x_1570_ = lean_box(v_useSplitter_1547_);
lean_inc(v_inst_1539_);
lean_inc_ref(v_resTy_1545_);
v___f_1571_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22___boxed), 10, 9);
lean_closure_set(v___f_1571_, 0, v_e_1569_);
lean_closure_set(v___f_1571_, 1, v___x_1570_);
lean_closure_set(v___f_1571_, 2, v_resTy_1545_);
lean_closure_set(v___f_1571_, 3, v_toPure_1568_);
lean_closure_set(v___f_1571_, 4, v_onAlt_1546_);
lean_closure_set(v___f_1571_, 5, v_toBind_1567_);
lean_closure_set(v___f_1571_, 6, v_inst_1539_);
lean_closure_set(v___f_1571_, 7, v_inst_1540_);
lean_closure_set(v___f_1571_, 8, v_inst_1541_);
v___x_1572_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1572_, 0, v_resTy_1545_);
v___x_1573_ = lean_apply_2(v_inst_1539_, lean_box(0), v___x_1572_);
v___x_1574_ = lean_apply_4(v_toBind_1567_, lean_box(0), lean_box(0), v___x_1573_, v___f_1571_);
return v___x_1574_;
}
default: 
{
lean_object* v_toApplicative_1575_; lean_object* v_matcherApp_1576_; lean_object* v_toBind_1577_; lean_object* v_toFunctor_1578_; lean_object* v_toPure_1579_; lean_object* v_toMatcherInfo_1580_; lean_object* v_discrs_1581_; lean_object* v___f_1582_; lean_object* v___f_1583_; lean_object* v___f_1584_; lean_object* v___x_1585_; size_t v_sz_1586_; size_t v___x_1587_; lean_object* v_mask_1588_; lean_object* v___x_1589_; lean_object* v___f_1590_; lean_object* v_maskedDiscrs_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v_toApplicative_1575_ = lean_ctor_get(v_inst_1541_, 0);
v_matcherApp_1576_ = lean_ctor_get(v_info_1544_, 0);
lean_inc_ref(v_matcherApp_1576_);
lean_dec_ref_known(v_info_1544_, 1);
v_toBind_1577_ = lean_ctor_get(v_inst_1541_, 1);
lean_inc(v_toBind_1577_);
v_toFunctor_1578_ = lean_ctor_get(v_toApplicative_1575_, 0);
lean_inc_ref(v_toFunctor_1578_);
v_toPure_1579_ = lean_ctor_get(v_toApplicative_1575_, 1);
lean_inc(v_toPure_1579_);
v_toMatcherInfo_1580_ = lean_ctor_get(v_matcherApp_1576_, 0);
v_discrs_1581_ = lean_ctor_get(v_matcherApp_1576_, 5);
lean_inc_ref_n(v_discrs_1581_, 2);
v___f_1582_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21___boxed), 5, 1);
lean_closure_set(v___f_1582_, 0, v_onAlt_1546_);
v___f_1583_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0));
lean_inc_ref(v_toMatcherInfo_1580_);
v___f_1584_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23___boxed), 4, 1);
lean_closure_set(v___f_1584_, 0, v_toMatcherInfo_1580_);
v___x_1585_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_1586_ = lean_array_size(v_discrs_1581_);
v___x_1587_ = ((size_t)0ULL);
v_mask_1588_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1585_, v_discrs_1581_, v___f_1584_, v_sz_1586_, v___x_1587_, v_discrs_1581_);
v___x_1589_ = lean_box(v_useSplitter_1547_);
lean_inc(v_inst_1539_);
lean_inc(v_mask_1588_);
v___f_1590_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25___boxed), 13, 12);
lean_closure_set(v___f_1590_, 0, v_toFunctor_1578_);
lean_closure_set(v___f_1590_, 1, v_mask_1588_);
lean_closure_set(v___f_1590_, 2, v_toPure_1579_);
lean_closure_set(v___f_1590_, 3, v_inst_1539_);
lean_closure_set(v___f_1590_, 4, v_inst_1540_);
lean_closure_set(v___f_1590_, 5, v_inst_1541_);
lean_closure_set(v___f_1590_, 6, v_inst_1542_);
lean_closure_set(v___f_1590_, 7, v_inst_1543_);
lean_closure_set(v___f_1590_, 8, v_matcherApp_1576_);
lean_closure_set(v___f_1590_, 9, v___x_1589_);
lean_closure_set(v___f_1590_, 10, v___f_1582_);
lean_closure_set(v___f_1590_, 11, v___f_1583_);
v_maskedDiscrs_1591_ = l_Lean_Array_mask___redArg(v_mask_1588_, v_discrs_1581_);
lean_dec(v_mask_1588_);
v___x_1592_ = lean_alloc_closure((void*)(l_Lean_Expr_abstractM___boxed), 7, 2);
lean_closure_set(v___x_1592_, 0, v_resTy_1545_);
lean_closure_set(v___x_1592_, 1, v_maskedDiscrs_1591_);
v___x_1593_ = lean_apply_2(v_inst_1539_, lean_box(0), v___x_1592_);
v___x_1594_ = lean_apply_4(v_toBind_1577_, lean_box(0), lean_box(0), v___x_1593_, v___f_1590_);
return v___x_1594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_info_1600_, lean_object* v_resTy_1601_, lean_object* v_onAlt_1602_, lean_object* v_useSplitter_1603_){
_start:
{
uint8_t v_useSplitter_boxed_1604_; lean_object* v_res_1605_; 
v_useSplitter_boxed_1604_ = lean_unbox(v_useSplitter_1603_);
v_res_1605_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1595_, v_inst_1596_, v_inst_1597_, v_inst_1598_, v_inst_1599_, v_info_1600_, v_resTy_1601_, v_onAlt_1602_, v_useSplitter_boxed_1604_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object* v_n_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_info_1615_, lean_object* v_resTy_1616_, lean_object* v_onAlt_1617_, uint8_t v_useSplitter_1618_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1607_, v_inst_1608_, v_inst_1609_, v_inst_1610_, v_inst_1611_, v_info_1615_, v_resTy_1616_, v_onAlt_1617_, v_useSplitter_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object* v_n_1620_, lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_info_1629_, lean_object* v_resTy_1630_, lean_object* v_onAlt_1631_, lean_object* v_useSplitter_1632_){
_start:
{
uint8_t v_useSplitter_boxed_1633_; lean_object* v_res_1634_; 
v_useSplitter_boxed_1633_ = lean_unbox(v_useSplitter_1632_);
v_res_1634_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(v_n_1620_, v_inst_1621_, v_inst_1622_, v_inst_1623_, v_inst_1624_, v_inst_1625_, v_inst_1626_, v_inst_1627_, v_inst_1628_, v_info_1629_, v_resTy_1630_, v_onAlt_1631_, v_useSplitter_boxed_1633_);
lean_dec(v_inst_1628_);
lean_dec(v_inst_1627_);
lean_dec_ref(v_inst_1626_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object* v_info_1635_, lean_object* v_e_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
if (lean_obj_tag(v_info_1635_) == 3)
{
lean_object* v_matcherApp_1645_; lean_object* v_toMatcherInfo_1646_; lean_object* v___x_1647_; 
v_matcherApp_1645_ = lean_ctor_get(v_info_1635_, 0);
lean_inc_ref(v_matcherApp_1645_);
lean_dec_ref_known(v_info_1635_, 1);
v_toMatcherInfo_1646_ = lean_ctor_get(v_matcherApp_1645_, 0);
lean_inc_ref(v_toMatcherInfo_1646_);
lean_dec_ref(v_matcherApp_1645_);
v___x_1647_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_toMatcherInfo_1646_, v_e_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_);
return v___x_1647_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec_ref(v_e_1636_);
lean_dec_ref(v_info_1635_);
v___x_1648_ = lean_box(0);
v___x_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
return v___x_1649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object* v_info_1650_, lean_object* v_e_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(v_info_1650_, v_e_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec_ref(v_a_1653_);
lean_dec(v_a_1652_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object* v_declName_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v___x_1664_; lean_object* v_env_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1664_ = lean_st_ref_get(v___y_1662_);
v_env_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc_ref(v_env_1665_);
lean_dec(v___x_1664_);
v___x_1666_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1665_, v_declName_1661_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object* v_declName_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1668_, v___y_1669_);
lean_dec(v___y_1669_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; lean_object* v_env_1679_; lean_object* v___x_1680_; lean_object* v_mctx_1681_; lean_object* v_lctx_1682_; lean_object* v_options_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1678_ = lean_st_ref_get(v___y_1676_);
v_env_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_ref(v_env_1679_);
lean_dec(v___x_1678_);
v___x_1680_ = lean_st_ref_get(v___y_1674_);
v_mctx_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc_ref(v_mctx_1681_);
lean_dec(v___x_1680_);
v_lctx_1682_ = lean_ctor_get(v___y_1673_, 2);
v_options_1683_ = lean_ctor_get(v___y_1675_, 1);
lean_inc_ref(v_options_1683_);
lean_inc_ref(v_lctx_1682_);
v___x_1684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1684_, 0, v_env_1679_);
lean_ctor_set(v___x_1684_, 1, v_mctx_1681_);
lean_ctor_set(v___x_1684_, 2, v_lctx_1682_);
lean_ctor_set(v___x_1684_, 3, v_options_1683_);
v___x_1685_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v_msgData_1672_);
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec_ref(v___y_1688_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_){
_start:
{
lean_object* v_ref_1700_; lean_object* v___x_1701_; lean_object* v_a_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1710_; 
v_ref_1700_ = lean_ctor_get(v___y_1697_, 4);
v___x_1701_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_);
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1701_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1704_ = v___x_1701_;
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_a_1702_);
lean_dec(v___x_1701_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
lean_inc(v_ref_1700_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_ref_1700_);
lean_ctor_set(v___x_1706_, 1, v_a_1702_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set_tag(v___x_1704_, 1);
lean_ctor_set(v___x_1704_, 0, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_1718_, lean_object* v_msg_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_toCold_1725_; lean_object* v_options_1726_; lean_object* v_currRecDepth_1727_; lean_object* v_maxRecDepth_1728_; lean_object* v_ref_1729_; lean_object* v_currNamespace_1730_; lean_object* v_openDecls_1731_; lean_object* v_initHeartbeats_1732_; lean_object* v_maxHeartbeats_1733_; lean_object* v_currMacroScope_1734_; uint8_t v_diag_1735_; uint8_t v_suppressElabErrors_1736_; lean_object* v_ref_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v_toCold_1725_ = lean_ctor_get(v___y_1722_, 0);
v_options_1726_ = lean_ctor_get(v___y_1722_, 1);
v_currRecDepth_1727_ = lean_ctor_get(v___y_1722_, 2);
v_maxRecDepth_1728_ = lean_ctor_get(v___y_1722_, 3);
v_ref_1729_ = lean_ctor_get(v___y_1722_, 4);
v_currNamespace_1730_ = lean_ctor_get(v___y_1722_, 5);
v_openDecls_1731_ = lean_ctor_get(v___y_1722_, 6);
v_initHeartbeats_1732_ = lean_ctor_get(v___y_1722_, 7);
v_maxHeartbeats_1733_ = lean_ctor_get(v___y_1722_, 8);
v_currMacroScope_1734_ = lean_ctor_get(v___y_1722_, 9);
v_diag_1735_ = lean_ctor_get_uint8(v___y_1722_, sizeof(void*)*10);
v_suppressElabErrors_1736_ = lean_ctor_get_uint8(v___y_1722_, sizeof(void*)*10 + 1);
v_ref_1737_ = l_Lean_replaceRef(v_ref_1718_, v_ref_1729_);
lean_inc(v_currMacroScope_1734_);
lean_inc(v_maxHeartbeats_1733_);
lean_inc(v_initHeartbeats_1732_);
lean_inc(v_openDecls_1731_);
lean_inc(v_currNamespace_1730_);
lean_inc(v_maxRecDepth_1728_);
lean_inc(v_currRecDepth_1727_);
lean_inc_ref(v_options_1726_);
lean_inc_ref(v_toCold_1725_);
v___x_1738_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1738_, 0, v_toCold_1725_);
lean_ctor_set(v___x_1738_, 1, v_options_1726_);
lean_ctor_set(v___x_1738_, 2, v_currRecDepth_1727_);
lean_ctor_set(v___x_1738_, 3, v_maxRecDepth_1728_);
lean_ctor_set(v___x_1738_, 4, v_ref_1737_);
lean_ctor_set(v___x_1738_, 5, v_currNamespace_1730_);
lean_ctor_set(v___x_1738_, 6, v_openDecls_1731_);
lean_ctor_set(v___x_1738_, 7, v_initHeartbeats_1732_);
lean_ctor_set(v___x_1738_, 8, v_maxHeartbeats_1733_);
lean_ctor_set(v___x_1738_, 9, v_currMacroScope_1734_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*10, v_diag_1735_);
lean_ctor_set_uint8(v___x_1738_, sizeof(void*)*10 + 1, v_suppressElabErrors_1736_);
v___x_1739_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1719_, v___y_1720_, v___y_1721_, v___x_1738_, v___y_1723_);
lean_dec_ref_known(v___x_1738_, 10);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1740_, lean_object* v_msg_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1740_, v_msg_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v_ref_1740_);
return v_res_1747_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1753_, 0, v___x_1752_);
lean_ctor_set(v___x_1753_, 1, v___x_1752_);
lean_ctor_set(v___x_1753_, 2, v___x_1752_);
lean_ctor_set(v___x_1753_, 3, v___x_1752_);
lean_ctor_set(v___x_1753_, 4, v___x_1751_);
lean_ctor_set(v___x_1753_, 5, v___x_1751_);
lean_ctor_set(v___x_1753_, 6, v___x_1751_);
lean_ctor_set(v___x_1753_, 7, v___x_1751_);
lean_ctor_set(v___x_1753_, 8, v___x_1751_);
lean_ctor_set(v___x_1753_, 9, v___x_1751_);
lean_ctor_set(v___x_1753_, 10, v___x_1751_);
return v___x_1753_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = lean_unsigned_to_nat(32u);
v___x_1755_ = lean_mk_empty_array_with_capacity(v___x_1754_);
v___x_1756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1757_ = ((size_t)5ULL);
v___x_1758_ = lean_unsigned_to_nat(0u);
v___x_1759_ = lean_unsigned_to_nat(32u);
v___x_1760_ = lean_mk_empty_array_with_capacity(v___x_1759_);
v___x_1761_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_1762_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1762_, 0, v___x_1761_);
lean_ctor_set(v___x_1762_, 1, v___x_1760_);
lean_ctor_set(v___x_1762_, 2, v___x_1758_);
lean_ctor_set(v___x_1762_, 3, v___x_1758_);
lean_ctor_set_usize(v___x_1762_, 4, v___x_1757_);
return v___x_1762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1763_ = lean_box(1);
v___x_1764_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_1765_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v___x_1764_);
lean_ctor_set(v___x_1766_, 2, v___x_1763_);
return v___x_1766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
return v___x_1781_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_1784_ = l_Lean_stringToMessageData(v___x_1783_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1786_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_1787_ = l_Lean_stringToMessageData(v___x_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_1788_, lean_object* v_declHint_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v___x_1792_; lean_object* v_env_1793_; uint8_t v___x_1794_; 
v___x_1792_ = lean_st_ref_get(v___y_1790_);
v_env_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc_ref(v_env_1793_);
lean_dec(v___x_1792_);
v___x_1794_ = l_Lean_Name_isAnonymous(v_declHint_1789_);
if (v___x_1794_ == 0)
{
uint8_t v_isExporting_1795_; 
v_isExporting_1795_ = lean_ctor_get_uint8(v_env_1793_, sizeof(void*)*8);
if (v_isExporting_1795_ == 0)
{
lean_object* v___x_1796_; 
lean_dec_ref(v_env_1793_);
lean_dec(v_declHint_1789_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v_msg_1788_);
return v___x_1796_;
}
else
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
lean_inc_ref(v_env_1793_);
v___x_1797_ = l_Lean_Environment_setExporting(v_env_1793_, v___x_1794_);
lean_inc(v_declHint_1789_);
lean_inc_ref(v___x_1797_);
v___x_1798_ = l_Lean_Environment_contains(v___x_1797_, v_declHint_1789_, v_isExporting_1795_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; 
lean_dec_ref(v___x_1797_);
lean_dec_ref(v_env_1793_);
lean_dec(v_declHint_1789_);
v___x_1799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1799_, 0, v_msg_1788_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v_c_1805_; lean_object* v___x_1806_; 
v___x_1800_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_1801_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_1802_ = l_Lean_Options_empty;
v___x_1803_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1797_);
lean_ctor_set(v___x_1803_, 1, v___x_1800_);
lean_ctor_set(v___x_1803_, 2, v___x_1801_);
lean_ctor_set(v___x_1803_, 3, v___x_1802_);
lean_inc(v_declHint_1789_);
v___x_1804_ = l_Lean_MessageData_ofConstName(v_declHint_1789_, v___x_1794_);
v_c_1805_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1805_, 0, v___x_1803_);
lean_ctor_set(v_c_1805_, 1, v___x_1804_);
v___x_1806_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1793_, v_declHint_1789_);
if (lean_obj_tag(v___x_1806_) == 0)
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
lean_dec_ref(v_env_1793_);
lean_dec(v_declHint_1789_);
v___x_1807_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
lean_ctor_set(v___x_1808_, 1, v_c_1805_);
v___x_1809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_1810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1810_, 0, v___x_1808_);
lean_ctor_set(v___x_1810_, 1, v___x_1809_);
v___x_1811_ = l_Lean_MessageData_note(v___x_1810_);
v___x_1812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1812_, 0, v_msg_1788_);
lean_ctor_set(v___x_1812_, 1, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1812_);
return v___x_1813_;
}
else
{
lean_object* v_val_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1849_; 
v_val_1814_ = lean_ctor_get(v___x_1806_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1816_ = v___x_1806_;
v_isShared_1817_ = v_isSharedCheck_1849_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_val_1814_);
lean_dec(v___x_1806_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1849_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v_mod_1821_; uint8_t v___x_1822_; 
v___x_1818_ = lean_box(0);
v___x_1819_ = l_Lean_Environment_header(v_env_1793_);
lean_dec_ref(v_env_1793_);
v___x_1820_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1819_);
v_mod_1821_ = lean_array_get(v___x_1818_, v___x_1820_, v_val_1814_);
lean_dec(v_val_1814_);
lean_dec_ref(v___x_1820_);
v___x_1822_ = l_Lean_isPrivateName(v_declHint_1789_);
lean_dec(v_declHint_1789_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_1824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v_c_1805_);
v___x_1825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_1826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1824_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
v___x_1827_ = l_Lean_MessageData_ofName(v_mod_1821_);
v___x_1828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
v___x_1829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_1830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1828_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = l_Lean_MessageData_note(v___x_1830_);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v_msg_1788_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set_tag(v___x_1816_, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1832_);
v___x_1834_ = v___x_1816_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1836_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
lean_ctor_set(v___x_1837_, 1, v_c_1805_);
v___x_1838_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_MessageData_ofName(v_mod_1821_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1839_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
v___x_1842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = l_Lean_MessageData_note(v___x_1843_);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_msg_1788_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set_tag(v___x_1816_, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1845_);
v___x_1847_ = v___x_1816_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1850_; 
lean_dec_ref(v_env_1793_);
lean_dec(v_declHint_1789_);
v___x_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1850_, 0, v_msg_1788_);
return v___x_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1851_, lean_object* v_declHint_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1851_, v_declHint_1852_, v___y_1853_);
lean_dec(v___y_1853_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object* v_msg_1856_, lean_object* v_declHint_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v___x_1863_; lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1873_; 
v___x_1863_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1856_, v_declHint_1857_, v___y_1861_);
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1866_ = v___x_1863_;
v_isShared_1867_ = v_isSharedCheck_1873_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1873_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v___x_1868_ = l_Lean_unknownIdentifierMessageTag;
v___x_1869_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
lean_ctor_set(v___x_1869_, 1, v_a_1864_);
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1869_);
v___x_1871_ = v___x_1866_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1874_, lean_object* v_declHint_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1874_, v_declHint_1875_, v___y_1876_, v___y_1877_, v___y_1878_, v___y_1879_);
lean_dec(v___y_1879_);
lean_dec_ref(v___y_1878_);
lean_dec(v___y_1877_);
lean_dec_ref(v___y_1876_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1882_, lean_object* v_msg_1883_, lean_object* v_declHint_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v_a_1891_; lean_object* v___x_1892_; 
v___x_1890_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1883_, v_declHint_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref(v___x_1890_);
v___x_1892_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1882_, v_a_1891_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1893_, lean_object* v_msg_1894_, lean_object* v_declHint_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1893_, v_msg_1894_, v_declHint_1895_, v___y_1896_, v___y_1897_, v___y_1898_, v___y_1899_);
lean_dec(v___y_1899_);
lean_dec_ref(v___y_1898_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v_ref_1893_);
return v_res_1901_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_1904_ = l_Lean_stringToMessageData(v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2));
v___x_1907_ = l_Lean_stringToMessageData(v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1908_, lean_object* v_constName_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v___x_1915_; uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1915_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1916_ = 0;
lean_inc(v_constName_1909_);
v___x_1917_ = l_Lean_MessageData_ofConstName(v_constName_1909_, v___x_1916_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1915_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1908_, v___x_1920_, v_constName_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1922_, lean_object* v_constName_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1922_, v_constName_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v_ref_1922_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_){
_start:
{
lean_object* v_ref_1936_; lean_object* v___x_1937_; 
v_ref_1936_ = lean_ctor_get(v___y_1933_, 4);
v___x_1937_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1936_, v_constName_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object* v_constName_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; lean_object* v_env_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; 
v___x_1951_ = lean_st_ref_get(v___y_1949_);
v_env_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc_ref(v_env_1952_);
lean_dec(v___x_1951_);
v___x_1953_ = 0;
lean_inc(v_constName_1945_);
v___x_1954_ = l_Lean_Environment_find_x3f(v_env_1952_, v_constName_1945_, v___x_1953_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v___x_1955_; 
v___x_1955_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
return v___x_1955_;
}
else
{
lean_object* v_val_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1963_; 
lean_dec(v_constName_1945_);
v_val_1956_ = lean_ctor_get(v___x_1954_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1958_ = v___x_1954_;
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_val_1956_);
lean_dec(v___x_1954_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1963_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1961_; 
if (v_isShared_1959_ == 0)
{
lean_ctor_set_tag(v___x_1958_, 0);
v___x_1961_ = v___x_1958_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1962_; 
v_reuseFailAlloc_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1962_, 0, v_val_1956_);
v___x_1961_ = v_reuseFailAlloc_1962_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
return v___x_1961_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object* v_msg_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v___x_1977_; lean_object* v_toApplicative_1978_; lean_object* v_toFunctor_1979_; lean_object* v_toSeq_1980_; lean_object* v_toSeqLeft_1981_; lean_object* v_toSeqRight_1982_; lean_object* v___f_1983_; lean_object* v___f_1984_; lean_object* v___f_1985_; lean_object* v___f_1986_; lean_object* v___x_1987_; lean_object* v___f_1988_; lean_object* v___f_1989_; lean_object* v___f_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v_toApplicative_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2025_; 
v___x_1977_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_1978_ = lean_ctor_get(v___x_1977_, 0);
v_toFunctor_1979_ = lean_ctor_get(v_toApplicative_1978_, 0);
v_toSeq_1980_ = lean_ctor_get(v_toApplicative_1978_, 2);
v_toSeqLeft_1981_ = lean_ctor_get(v_toApplicative_1978_, 3);
v_toSeqRight_1982_ = lean_ctor_get(v_toApplicative_1978_, 4);
v___f_1983_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_1984_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1979_, 2);
v___f_1985_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1985_, 0, v_toFunctor_1979_);
v___f_1986_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1986_, 0, v_toFunctor_1979_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___f_1985_);
lean_ctor_set(v___x_1987_, 1, v___f_1986_);
lean_inc(v_toSeqRight_1982_);
v___f_1988_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1988_, 0, v_toSeqRight_1982_);
lean_inc(v_toSeqLeft_1981_);
v___f_1989_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1989_, 0, v_toSeqLeft_1981_);
lean_inc(v_toSeq_1980_);
v___f_1990_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1990_, 0, v_toSeq_1980_);
v___x_1991_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1987_);
lean_ctor_set(v___x_1991_, 1, v___f_1983_);
lean_ctor_set(v___x_1991_, 2, v___f_1990_);
lean_ctor_set(v___x_1991_, 3, v___f_1989_);
lean_ctor_set(v___x_1991_, 4, v___f_1988_);
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v___f_1984_);
v___x_1993_ = l_StateRefT_x27_instMonad___redArg(v___x_1992_);
v_toApplicative_1994_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2025_ == 0)
{
lean_object* v_unused_2026_; 
v_unused_2026_ = lean_ctor_get(v___x_1993_, 1);
lean_dec(v_unused_2026_);
v___x_1996_ = v___x_1993_;
v_isShared_1997_ = v_isSharedCheck_2025_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_toApplicative_1994_);
lean_dec(v___x_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2025_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_toFunctor_1998_; lean_object* v_toSeq_1999_; lean_object* v_toSeqLeft_2000_; lean_object* v_toSeqRight_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2023_; 
v_toFunctor_1998_ = lean_ctor_get(v_toApplicative_1994_, 0);
v_toSeq_1999_ = lean_ctor_get(v_toApplicative_1994_, 2);
v_toSeqLeft_2000_ = lean_ctor_get(v_toApplicative_1994_, 3);
v_toSeqRight_2001_ = lean_ctor_get(v_toApplicative_1994_, 4);
v_isSharedCheck_2023_ = !lean_is_exclusive(v_toApplicative_1994_);
if (v_isSharedCheck_2023_ == 0)
{
lean_object* v_unused_2024_; 
v_unused_2024_ = lean_ctor_get(v_toApplicative_1994_, 1);
lean_dec(v_unused_2024_);
v___x_2003_ = v_toApplicative_1994_;
v_isShared_2004_ = v_isSharedCheck_2023_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_toSeqRight_2001_);
lean_inc(v_toSeqLeft_2000_);
lean_inc(v_toSeq_1999_);
lean_inc(v_toFunctor_1998_);
lean_dec(v_toApplicative_1994_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2023_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___f_2005_; lean_object* v___f_2006_; lean_object* v___f_2007_; lean_object* v___f_2008_; lean_object* v___x_2009_; lean_object* v___f_2010_; lean_object* v___f_2011_; lean_object* v___f_2012_; lean_object* v___x_2014_; 
v___f_2005_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_2006_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_1998_);
v___f_2007_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2007_, 0, v_toFunctor_1998_);
v___f_2008_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2008_, 0, v_toFunctor_1998_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___f_2007_);
lean_ctor_set(v___x_2009_, 1, v___f_2008_);
v___f_2010_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2010_, 0, v_toSeqRight_2001_);
v___f_2011_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2011_, 0, v_toSeqLeft_2000_);
v___f_2012_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2012_, 0, v_toSeq_1999_);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 4, v___f_2010_);
lean_ctor_set(v___x_2003_, 3, v___f_2011_);
lean_ctor_set(v___x_2003_, 2, v___f_2012_);
lean_ctor_set(v___x_2003_, 1, v___f_2005_);
lean_ctor_set(v___x_2003_, 0, v___x_2009_);
v___x_2014_ = v___x_2003_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2009_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v___f_2005_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v___f_2012_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v___f_2011_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v___f_2010_);
v___x_2014_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
lean_object* v___x_2016_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 1, v___f_2006_);
lean_ctor_set(v___x_1996_, 0, v___x_2014_);
v___x_2016_ = v___x_1996_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v___f_2006_);
v___x_2016_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2730__overap_2019_; lean_object* v___x_2020_; 
v___x_2017_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2018_ = l_instInhabitedOfMonad___redArg(v___x_2016_, v___x_2017_);
v___x_2730__overap_2019_ = lean_panic_fn_borrowed(v___x_2018_, v_msg_1971_);
lean_dec(v___x_2018_);
lean_inc(v___y_1975_);
lean_inc_ref(v___y_1974_);
lean_inc(v___y_1973_);
lean_inc_ref(v___y_1972_);
v___x_2020_ = lean_apply_5(v___x_2730__overap_2019_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, lean_box(0));
return v___x_2020_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object* v_msg_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
lean_dec(v___y_2031_);
lean_dec_ref(v___y_2030_);
lean_dec(v___y_2029_);
lean_dec_ref(v___y_2028_);
return v_res_2033_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2037_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2));
v___x_2038_ = lean_unsigned_to_nat(53u);
v___x_2039_ = lean_unsigned_to_nat(62u);
v___x_2040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1));
v___x_2041_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0));
v___x_2042_ = l_mkPanicMessageWithDecl(v___x_2041_, v___x_2040_, v___x_2039_, v___x_2038_, v___x_2037_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t v_sz_2043_, size_t v_i_2044_, lean_object* v_bs_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_usize_dec_lt(v_i_2044_, v_sz_2043_);
if (v___x_2051_ == 0)
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2052_, 0, v_bs_2045_);
return v___x_2052_;
}
else
{
lean_object* v_v_2053_; lean_object* v___x_2054_; 
v_v_2053_ = lean_array_uget_borrowed(v_bs_2045_, v_i_2044_);
lean_inc(v_v_2053_);
v___x_2054_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_2053_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v_bs_x27_2057_; lean_object* v_a_2059_; 
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v___x_2056_ = lean_unsigned_to_nat(0u);
v_bs_x27_2057_ = lean_array_uset(v_bs_2045_, v_i_2044_, v___x_2056_);
if (lean_obj_tag(v_a_2055_) == 6)
{
lean_object* v_val_2064_; lean_object* v_numFields_2065_; uint8_t v___x_2066_; lean_object* v___x_2067_; 
v_val_2064_ = lean_ctor_get(v_a_2055_, 0);
lean_inc_ref(v_val_2064_);
lean_dec_ref_known(v_a_2055_, 1);
v_numFields_2065_ = lean_ctor_get(v_val_2064_, 4);
lean_inc(v_numFields_2065_);
lean_dec_ref(v_val_2064_);
v___x_2066_ = 0;
v___x_2067_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2067_, 0, v_numFields_2065_);
lean_ctor_set(v___x_2067_, 1, v___x_2056_);
lean_ctor_set_uint8(v___x_2067_, sizeof(void*)*2, v___x_2066_);
v_a_2059_ = v___x_2067_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v_a_2055_);
v___x_2068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
v___x_2069_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_2068_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v_a_2059_ = v_a_2070_;
goto v___jp_2058_;
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec_ref(v_bs_x27_2057_);
v_a_2071_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2069_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2069_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
v___jp_2058_:
{
size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = ((size_t)1ULL);
v___x_2061_ = lean_usize_add(v_i_2044_, v___x_2060_);
v___x_2062_ = lean_array_uset(v_bs_x27_2057_, v_i_2044_, v_a_2059_);
v_i_2044_ = v___x_2061_;
v_bs_2045_ = v___x_2062_;
goto _start;
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec_ref(v_bs_2045_);
v_a_2079_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2054_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2054_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object* v_sz_2087_, lean_object* v_i_2088_, lean_object* v_bs_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
size_t v_sz_boxed_2095_; size_t v_i_boxed_2096_; lean_object* v_res_2097_; 
v_sz_boxed_2095_ = lean_unbox_usize(v_sz_2087_);
lean_dec(v_sz_2087_);
v_i_boxed_2096_ = lean_unbox_usize(v_i_2088_);
lean_dec(v_i_2088_);
v_res_2097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_2095_, v_i_boxed_2096_, v_bs_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
return v_res_2097_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2098_; lean_object* v_dummy_2099_; 
v___x_2098_ = lean_box(0);
v_dummy_2099_ = l_Lean_Expr_sort___override(v___x_2098_);
return v_dummy_2099_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = lean_box(0);
v___x_2101_ = lean_unsigned_to_nat(16u);
v___x_2102_ = lean_mk_array(v___x_2101_, v___x_2100_);
return v___x_2102_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2103_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2103_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object* v_e_2108_, uint8_t v_alsoCasesOn_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
uint8_t v___x_2118_; 
v___x_2118_ = l_Lean_Expr_isApp(v_e_2108_);
if (v___x_2118_ == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
lean_dec_ref(v_e_2108_);
v___x_2119_ = lean_box(0);
v___x_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
return v___x_2120_;
}
else
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_Expr_getAppFn(v_e_2108_);
if (lean_obj_tag(v___x_2121_) == 4)
{
lean_object* v_declName_2122_; lean_object* v_us_2123_; lean_object* v___x_2124_; lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2278_; 
v_declName_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc_n(v_declName_2122_, 2);
v_us_2123_ = lean_ctor_get(v___x_2121_, 1);
lean_inc(v_us_2123_);
lean_dec_ref_known(v___x_2121_, 2);
v___x_2124_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2122_, v___y_2113_);
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2278_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2278_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_a_2125_) == 1)
{
lean_object* v_val_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2171_; 
v_val_2130_ = lean_ctor_get(v_a_2125_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_a_2125_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2132_ = v_a_2125_;
v_isShared_2133_ = v_isSharedCheck_2171_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_val_2130_);
lean_dec(v_a_2125_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2171_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_dummy_2134_; lean_object* v_nargs_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v_args_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; uint8_t v___x_2142_; 
v_dummy_2134_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
v_nargs_2135_ = l_Lean_Expr_getAppNumArgs(v_e_2108_);
lean_inc(v_nargs_2135_);
v___x_2136_ = lean_mk_array(v_nargs_2135_, v_dummy_2134_);
v___x_2137_ = lean_unsigned_to_nat(1u);
v___x_2138_ = lean_nat_sub(v_nargs_2135_, v___x_2137_);
lean_dec(v_nargs_2135_);
v_args_2139_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2108_, v___x_2136_, v___x_2138_);
v___x_2140_ = lean_array_get_size(v_args_2139_);
v___x_2141_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2130_);
v___x_2142_ = lean_nat_dec_lt(v___x_2140_, v___x_2141_);
lean_dec(v___x_2141_);
if (v___x_2142_ == 0)
{
lean_object* v_numParams_2143_; lean_object* v_numDiscrs_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
v_numParams_2143_ = lean_ctor_get(v_val_2130_, 0);
v_numDiscrs_2144_ = lean_ctor_get(v_val_2130_, 1);
v___x_2145_ = lean_array_mk(v_us_2123_);
v___x_2146_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2143_);
v___x_2147_ = l_Array_extract___redArg(v_args_2139_, v___x_2146_, v_numParams_2143_);
v___x_2148_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2130_);
v___x_2149_ = lean_array_get(v___x_2129_, v_args_2139_, v___x_2148_);
lean_dec(v___x_2148_);
v___x_2150_ = lean_nat_add(v_numParams_2143_, v___x_2137_);
v___x_2151_ = lean_nat_add(v___x_2150_, v_numDiscrs_2144_);
lean_inc(v___x_2151_);
lean_inc_ref_n(v_args_2139_, 2);
v___x_2152_ = l_Array_toSubarray___redArg(v_args_2139_, v___x_2150_, v___x_2151_);
v___x_2153_ = l_Subarray_copy___redArg(v___x_2152_);
v___x_2154_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2130_);
v___x_2155_ = lean_nat_add(v___x_2151_, v___x_2154_);
lean_dec(v___x_2154_);
lean_inc(v___x_2155_);
v___x_2156_ = l_Array_toSubarray___redArg(v_args_2139_, v___x_2151_, v___x_2155_);
v___x_2157_ = l_Subarray_copy___redArg(v___x_2156_);
v___x_2158_ = l_Array_toSubarray___redArg(v_args_2139_, v___x_2155_, v___x_2140_);
v___x_2159_ = l_Subarray_copy___redArg(v___x_2158_);
v___x_2160_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2160_, 0, v_val_2130_);
lean_ctor_set(v___x_2160_, 1, v_declName_2122_);
lean_ctor_set(v___x_2160_, 2, v___x_2145_);
lean_ctor_set(v___x_2160_, 3, v___x_2147_);
lean_ctor_set(v___x_2160_, 4, v___x_2149_);
lean_ctor_set(v___x_2160_, 5, v___x_2153_);
lean_ctor_set(v___x_2160_, 6, v___x_2157_);
lean_ctor_set(v___x_2160_, 7, v___x_2159_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 0, v___x_2160_);
v___x_2162_ = v___x_2132_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2166_; 
v_reuseFailAlloc_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2166_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2166_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
lean_object* v___x_2164_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2162_);
v___x_2164_ = v___x_2127_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2169_; 
lean_dec_ref(v_args_2139_);
lean_del_object(v___x_2132_);
lean_dec(v_val_2130_);
lean_dec(v_us_2123_);
lean_dec(v_declName_2122_);
v___x_2167_ = lean_box(0);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2167_);
v___x_2169_ = v___x_2127_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v___x_2167_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
else
{
lean_object* v___x_2172_; 
lean_del_object(v___x_2127_);
lean_dec(v_a_2125_);
v___x_2172_ = lean_st_ref_get(v___y_2113_);
if (v_alsoCasesOn_2109_ == 0)
{
lean_dec(v___x_2172_);
lean_dec(v_us_2123_);
lean_dec(v_declName_2122_);
lean_dec_ref(v_e_2108_);
goto v___jp_2115_;
}
else
{
lean_object* v_env_2173_; uint8_t v___x_2174_; 
v_env_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc_ref(v_env_2173_);
lean_dec(v___x_2172_);
lean_inc(v_declName_2122_);
v___x_2174_ = l_Lean_isCasesOnRecursor(v_env_2173_, v_declName_2122_);
if (v___x_2174_ == 0)
{
lean_dec(v_us_2123_);
lean_dec(v_declName_2122_);
lean_dec_ref(v_e_2108_);
goto v___jp_2115_;
}
else
{
lean_object* v_indName_2175_; lean_object* v___x_2176_; 
v_indName_2175_ = l_Lean_Name_getPrefix(v_declName_2122_);
v___x_2176_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_2175_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2269_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2269_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2269_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2269_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2269_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
if (lean_obj_tag(v_a_2177_) == 5)
{
lean_object* v_val_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2264_; 
v_val_2181_ = lean_ctor_get(v_a_2177_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_a_2177_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2183_ = v_a_2177_;
v_isShared_2184_ = v_isSharedCheck_2264_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_val_2181_);
lean_dec(v_a_2177_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2264_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_toConstantVal_2185_; lean_object* v_numParams_2186_; lean_object* v_numIndices_2187_; lean_object* v_ctors_2188_; lean_object* v_nargs_2189_; lean_object* v_dummy_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v_args_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v_toConstantVal_2185_ = lean_ctor_get(v_val_2181_, 0);
lean_inc_ref(v_toConstantVal_2185_);
v_numParams_2186_ = lean_ctor_get(v_val_2181_, 1);
lean_inc(v_numParams_2186_);
v_numIndices_2187_ = lean_ctor_get(v_val_2181_, 2);
lean_inc(v_numIndices_2187_);
v_ctors_2188_ = lean_ctor_get(v_val_2181_, 4);
lean_inc(v_ctors_2188_);
v_nargs_2189_ = l_Lean_Expr_getAppNumArgs(v_e_2108_);
v_dummy_2190_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
lean_inc(v_nargs_2189_);
v___x_2191_ = lean_mk_array(v_nargs_2189_, v_dummy_2190_);
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = lean_nat_sub(v_nargs_2189_, v___x_2192_);
lean_dec(v_nargs_2189_);
v_args_2194_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2108_, v___x_2191_, v___x_2193_);
v___x_2195_ = lean_nat_add(v_numParams_2186_, v___x_2192_);
v___x_2196_ = lean_nat_add(v___x_2195_, v_numIndices_2187_);
v___x_2197_ = lean_nat_add(v___x_2196_, v___x_2192_);
lean_dec(v___x_2196_);
v___x_2198_ = l_Lean_InductiveVal_numCtors(v_val_2181_);
lean_dec_ref(v_val_2181_);
v___x_2199_ = lean_nat_add(v___x_2197_, v___x_2198_);
lean_dec(v___x_2198_);
v___x_2200_ = lean_array_get_size(v_args_2194_);
v___x_2201_ = lean_nat_dec_le(v___x_2199_, v___x_2200_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; lean_object* v___x_2204_; 
lean_dec(v___x_2199_);
lean_dec(v___x_2197_);
lean_dec(v___x_2195_);
lean_dec_ref(v_args_2194_);
lean_dec(v_ctors_2188_);
lean_dec(v_numIndices_2187_);
lean_dec(v_numParams_2186_);
lean_dec_ref(v_toConstantVal_2185_);
lean_del_object(v___x_2183_);
lean_dec(v_us_2123_);
lean_dec(v_declName_2122_);
v___x_2202_ = lean_box(0);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2202_);
v___x_2204_ = v___x_2179_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
else
{
lean_object* v___x_2206_; lean_object* v_params_2207_; lean_object* v_motive_2208_; lean_object* v_discrs_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v_discrInfos_2212_; lean_object* v_alts_2213_; lean_object* v___y_2215_; lean_object* v___y_2216_; lean_object* v_lower_2255_; lean_object* v_upper_2256_; uint8_t v___x_2263_; 
lean_del_object(v___x_2179_);
v___x_2206_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2186_);
lean_inc_ref_n(v_args_2194_, 3);
v_params_2207_ = l_Array_toSubarray___redArg(v_args_2194_, v___x_2206_, v_numParams_2186_);
v_motive_2208_ = lean_array_get(v___x_2129_, v_args_2194_, v_numParams_2186_);
lean_dec(v_numParams_2186_);
lean_inc(v___x_2197_);
v_discrs_2209_ = l_Array_toSubarray___redArg(v_args_2194_, v___x_2195_, v___x_2197_);
v___x_2210_ = lean_nat_add(v_numIndices_2187_, v___x_2192_);
lean_dec(v_numIndices_2187_);
v___x_2211_ = lean_box(0);
v_discrInfos_2212_ = lean_mk_array(v___x_2210_, v___x_2211_);
lean_inc(v___x_2199_);
v_alts_2213_ = l_Array_toSubarray___redArg(v_args_2194_, v___x_2197_, v___x_2199_);
v___x_2263_ = lean_nat_dec_le(v___x_2199_, v___x_2206_);
if (v___x_2263_ == 0)
{
v_lower_2255_ = v___x_2199_;
v_upper_2256_ = v___x_2200_;
goto v___jp_2254_;
}
else
{
lean_dec(v___x_2199_);
v_lower_2255_ = v___x_2206_;
v_upper_2256_ = v___x_2200_;
goto v___jp_2254_;
}
v___jp_2214_:
{
lean_object* v___x_2217_; size_t v_sz_2218_; size_t v___x_2219_; lean_object* v___x_2220_; 
v___x_2217_ = lean_array_mk(v_ctors_2188_);
v_sz_2218_ = lean_array_size(v___x_2217_);
v___x_2219_ = ((size_t)0ULL);
v___x_2220_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_2218_, v___x_2219_, v___x_2217_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2245_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2245_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2245_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_start_2225_; lean_object* v_stop_2226_; lean_object* v_start_2227_; lean_object* v_stop_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
v_start_2225_ = lean_ctor_get(v_params_2207_, 1);
lean_inc(v_start_2225_);
v_stop_2226_ = lean_ctor_get(v_params_2207_, 2);
lean_inc(v_stop_2226_);
v_start_2227_ = lean_ctor_get(v_discrs_2209_, 1);
lean_inc(v_start_2227_);
v_stop_2228_ = lean_ctor_get(v_discrs_2209_, 2);
lean_inc(v_stop_2228_);
v___x_2229_ = lean_nat_sub(v_stop_2226_, v_start_2225_);
lean_dec(v_start_2225_);
lean_dec(v_stop_2226_);
v___x_2230_ = lean_nat_sub(v_stop_2228_, v_start_2227_);
lean_dec(v_start_2227_);
lean_dec(v_stop_2228_);
v___x_2231_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2);
v___x_2232_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2229_);
lean_ctor_set(v___x_2232_, 1, v___x_2230_);
lean_ctor_set(v___x_2232_, 2, v_a_2221_);
lean_ctor_set(v___x_2232_, 3, v___y_2216_);
lean_ctor_set(v___x_2232_, 4, v_discrInfos_2212_);
lean_ctor_set(v___x_2232_, 5, v___x_2231_);
v___x_2233_ = lean_array_mk(v_us_2123_);
v___x_2234_ = l_Subarray_copy___redArg(v_params_2207_);
v___x_2235_ = l_Subarray_copy___redArg(v_discrs_2209_);
v___x_2236_ = l_Subarray_copy___redArg(v_alts_2213_);
v___x_2237_ = l_Subarray_copy___redArg(v___y_2215_);
v___x_2238_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2232_);
lean_ctor_set(v___x_2238_, 1, v_declName_2122_);
lean_ctor_set(v___x_2238_, 2, v___x_2233_);
lean_ctor_set(v___x_2238_, 3, v___x_2234_);
lean_ctor_set(v___x_2238_, 4, v_motive_2208_);
lean_ctor_set(v___x_2238_, 5, v___x_2235_);
lean_ctor_set(v___x_2238_, 6, v___x_2236_);
lean_ctor_set(v___x_2238_, 7, v___x_2237_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set_tag(v___x_2183_, 1);
lean_ctor_set(v___x_2183_, 0, v___x_2238_);
v___x_2240_ = v___x_2183_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
lean_object* v___x_2242_; 
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2240_);
v___x_2242_ = v___x_2223_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2240_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec_ref(v_alts_2213_);
lean_dec_ref(v_discrInfos_2212_);
lean_dec_ref(v_discrs_2209_);
lean_dec(v_motive_2208_);
lean_dec_ref(v_params_2207_);
lean_del_object(v___x_2183_);
lean_dec(v_us_2123_);
lean_dec(v_declName_2122_);
v_a_2246_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2220_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2220_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
v___jp_2254_:
{
lean_object* v_levelParams_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; 
v_levelParams_2257_ = lean_ctor_get(v_toConstantVal_2185_, 1);
lean_inc(v_levelParams_2257_);
lean_dec_ref(v_toConstantVal_2185_);
v___x_2258_ = l_Array_toSubarray___redArg(v_args_2194_, v_lower_2255_, v_upper_2256_);
v___x_2259_ = l_List_lengthTR___redArg(v_levelParams_2257_);
lean_dec(v_levelParams_2257_);
v___x_2260_ = l_List_lengthTR___redArg(v_us_2123_);
v___x_2261_ = lean_nat_dec_eq(v___x_2259_, v___x_2260_);
lean_dec(v___x_2260_);
lean_dec(v___x_2259_);
if (v___x_2261_ == 0)
{
lean_object* v___x_2262_; 
v___x_2262_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3));
v___y_2215_ = v___x_2258_;
v___y_2216_ = v___x_2262_;
goto v___jp_2214_;
}
else
{
v___y_2215_ = v___x_2258_;
v___y_2216_ = v___x_2211_;
goto v___jp_2214_;
}
}
}
}
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2267_; 
lean_dec(v_a_2177_);
lean_dec(v_us_2123_);
lean_dec(v_declName_2122_);
lean_dec_ref(v_e_2108_);
v___x_2265_ = lean_box(0);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2265_);
v___x_2267_ = v___x_2179_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v___x_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
}
}
else
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2277_; 
lean_dec(v_us_2123_);
lean_dec(v_declName_2122_);
lean_dec_ref(v_e_2108_);
v_a_2270_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2272_ = v___x_2176_;
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2176_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2277_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2275_; 
if (v_isShared_2273_ == 0)
{
v___x_2275_ = v___x_2272_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_a_2270_);
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
}
}
}
else
{
lean_dec_ref(v___x_2121_);
lean_dec_ref(v_e_2108_);
goto v___jp_2115_;
}
}
v___jp_2115_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = lean_box(0);
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object* v_e_2279_, lean_object* v_alsoCasesOn_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2286_; lean_object* v_res_2287_; 
v_alsoCasesOn_boxed_2286_ = lean_unbox(v_alsoCasesOn_2280_);
v_res_2287_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_2279_, v_alsoCasesOn_boxed_2286_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object* v_e_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v___x_2294_; uint8_t v___x_2295_; 
v___x_2294_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2295_ = l_Lean_Expr_isAppOf(v_e_2288_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; uint8_t v___x_2297_; 
v___x_2296_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2297_ = l_Lean_Expr_isAppOf(v_e_2288_, v___x_2296_);
if (v___x_2297_ == 0)
{
lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2298_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_2299_ = l_Lean_Expr_isAppOf(v_e_2288_, v___x_2298_);
if (v___x_2299_ == 0)
{
uint8_t v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = 1;
v___x_2301_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_2288_, v___x_2300_, v_a_2289_, v_a_2290_, v_a_2291_, v_a_2292_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2322_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2304_ = v___x_2301_;
v_isShared_2305_ = v_isSharedCheck_2322_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2301_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2322_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
if (lean_obj_tag(v_a_2302_) == 1)
{
lean_object* v_val_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2317_; 
v_val_2306_ = lean_ctor_get(v_a_2302_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_a_2302_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2308_ = v_a_2302_;
v_isShared_2309_ = v_isSharedCheck_2317_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_val_2306_);
lean_dec(v_a_2302_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2317_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v___x_2312_; 
v___x_2310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2310_, 0, v_val_2306_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2310_);
v___x_2312_ = v___x_2308_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v___x_2310_);
v___x_2312_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2314_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2312_);
v___x_2314_ = v___x_2304_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v___x_2312_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2320_; 
lean_dec(v_a_2302_);
v___x_2318_ = lean_box(0);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 0, v___x_2318_);
v___x_2320_ = v___x_2304_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
v_a_2323_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2301_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2301_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
else
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_e_2288_);
v___x_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
return v___x_2333_;
}
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2334_, 0, v_e_2288_);
v___x_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
return v___x_2336_;
}
}
else
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v_e_2288_);
v___x_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
v___x_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
return v___x_2339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object* v_e_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object* v_declName_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2347_, v___y_2351_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object* v_declName_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2361_, lean_object* v_constName_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2369_, lean_object* v_constName_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2369_, v_constName_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2377_, lean_object* v_ref_2378_, lean_object* v_constName_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2378_, v_constName_2379_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2386_, lean_object* v_ref_2387_, lean_object* v_constName_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2386_, v_ref_2387_, v_constName_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_ref_2387_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2395_, lean_object* v_ref_2396_, lean_object* v_msg_2397_, lean_object* v_declHint_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2396_, v_msg_2397_, v_declHint_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2405_, lean_object* v_ref_2406_, lean_object* v_msg_2407_, lean_object* v_declHint_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2405_, v_ref_2406_, v_msg_2407_, v_declHint_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v_ref_2406_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_2415_, lean_object* v_declHint_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2415_, v_declHint_2416_, v___y_2420_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_2423_, lean_object* v_declHint_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_2423_, v_declHint_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2431_, lean_object* v_ref_2432_, lean_object* v_msg_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_2432_, v_msg_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2440_, lean_object* v_ref_2441_, lean_object* v_msg_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2440_, v_ref_2441_, v_msg_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v_ref_2441_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_2449_, lean_object* v_msg_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2457_, lean_object* v_msg_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_2457_, v_msg_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
return v_res_2464_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1(void){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0));
v___x_2467_ = l_Lean_stringToMessageData(v___x_2466_);
return v___x_2467_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3(void){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__2));
v___x_2470_ = l_Lean_stringToMessageData(v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object* v_idx_2474_, lean_object* v_e_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v___y_2482_; lean_object* v___y_2501_; lean_object* v___y_2502_; uint8_t v___y_2533_; lean_object* v___x_2554_; uint8_t v___x_2555_; 
v___x_2554_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2555_ = l_Lean_Expr_isAppOf(v_e_2475_, v___x_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2556_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2557_ = l_Lean_Expr_isAppOf(v_e_2475_, v___x_2556_);
v___y_2533_ = v___x_2557_;
goto v___jp_2532_;
}
else
{
v___y_2533_ = v___x_2555_;
goto v___jp_2532_;
}
v___jp_2481_:
{
lean_object* v___x_2483_; 
lean_inc_ref(v___y_2482_);
v___x_2483_ = l_Lean_Meta_findLocalDeclWithType_x3f(v___y_2482_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
if (lean_obj_tag(v_a_2484_) == 1)
{
lean_object* v_val_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
lean_dec_ref(v___y_2482_);
v_val_2485_ = lean_ctor_get(v_a_2484_, 0);
lean_inc(v_val_2485_);
lean_dec_ref_known(v_a_2484_, 1);
v___x_2486_ = l_Lean_mkFVar(v_val_2485_);
v___x_2487_ = l_Lean_Meta_rwIfWith(v___x_2486_, v_e_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
return v___x_2487_;
}
else
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec(v_a_2484_);
lean_dec_ref(v_e_2475_);
v___x_2488_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1);
v___x_2489_ = l_Lean_MessageData_ofExpr(v___y_2482_);
v___x_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2488_);
lean_ctor_set(v___x_2490_, 1, v___x_2489_);
v___x_2491_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2490_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
return v___x_2491_;
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_e_2475_);
v_a_2492_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2483_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2483_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
v___jp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_box(0);
lean_inc(v___y_2502_);
v___x_2504_ = l_Lean_mkConst(v___y_2502_, v___x_2503_);
v___x_2505_ = l_Lean_Meta_mkEq(v___y_2501_, v___x_2504_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; lean_object* v___x_2507_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc_n(v_a_2506_, 2);
lean_dec_ref_known(v___x_2505_, 1);
v___x_2507_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_a_2506_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v_a_2508_; 
v_a_2508_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_a_2508_);
lean_dec_ref_known(v___x_2507_, 1);
if (lean_obj_tag(v_a_2508_) == 1)
{
lean_object* v_val_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
lean_dec(v_a_2506_);
v_val_2509_ = lean_ctor_get(v_a_2508_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v_a_2508_, 1);
v___x_2510_ = l_Lean_mkFVar(v_val_2509_);
v___x_2511_ = l_Lean_Meta_rwIfWith(v___x_2510_, v_e_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
return v___x_2511_;
}
else
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
lean_dec(v_a_2508_);
lean_dec_ref(v_e_2475_);
v___x_2512_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3);
v___x_2513_ = l_Lean_MessageData_ofExpr(v_a_2506_);
v___x_2514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2512_);
lean_ctor_set(v___x_2514_, 1, v___x_2513_);
v___x_2515_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2514_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
return v___x_2515_;
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_a_2506_);
lean_dec_ref(v_e_2475_);
v_a_2516_ = lean_ctor_get(v___x_2507_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2507_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2507_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2507_);
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
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v_e_2475_);
v_a_2524_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2505_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2505_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
v___jp_2532_:
{
if (v___y_2533_ == 0)
{
lean_object* v___x_2534_; uint8_t v___x_2535_; 
v___x_2534_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_2535_ = l_Lean_Expr_isAppOf(v_e_2475_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lean_Meta_rwMatcher(v_idx_2474_, v_e_2475_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
return v___x_2536_;
}
else
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v_c_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2537_ = lean_unsigned_to_nat(1u);
v___x_2538_ = l_Lean_Expr_getAppNumArgs(v_e_2475_);
v___x_2539_ = lean_nat_sub(v___x_2538_, v___x_2537_);
lean_dec(v___x_2538_);
v___x_2540_ = lean_nat_sub(v___x_2539_, v___x_2537_);
lean_dec(v___x_2539_);
v_c_2541_ = l_Lean_Expr_getRevArg_x21(v_e_2475_, v___x_2540_);
v___x_2542_ = lean_unsigned_to_nat(0u);
v___x_2543_ = lean_nat_dec_eq(v_idx_2474_, v___x_2542_);
lean_dec(v_idx_2474_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; 
v___x_2544_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4));
v___y_2501_ = v_c_2541_;
v___y_2502_ = v___x_2544_;
goto v___jp_2500_;
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1));
v___y_2501_ = v_c_2541_;
v___y_2502_ = v___x_2545_;
goto v___jp_2500_;
}
}
}
else
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v_c_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2546_ = lean_unsigned_to_nat(1u);
v___x_2547_ = l_Lean_Expr_getAppNumArgs(v_e_2475_);
v___x_2548_ = lean_nat_sub(v___x_2547_, v___x_2546_);
lean_dec(v___x_2547_);
v___x_2549_ = lean_nat_sub(v___x_2548_, v___x_2546_);
lean_dec(v___x_2548_);
v_c_2550_ = l_Lean_Expr_getRevArg_x21(v_e_2475_, v___x_2549_);
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_nat_dec_eq(v_idx_2474_, v___x_2551_);
lean_dec(v_idx_2474_);
if (v___x_2552_ == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = l_Lean_mkNot(v_c_2550_);
v___y_2482_ = v___x_2553_;
goto v___jp_2481_;
}
else
{
v___y_2482_ = v_c_2550_;
goto v___jp_2481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object* v_idx_2558_, lean_object* v_e_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(v_idx_2558_, v_e_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
return v_res_2565_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Array(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default = _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default);
l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo = _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* initialize_Lean_Data_Array(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherApp_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_VCGen_Split(builtin);
}
#ifdef __cplusplus
}
#endif
