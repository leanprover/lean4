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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_instMonadEIO___redArg();
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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___impl___boxed(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__22 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__22_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__24 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__24_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__26 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__26_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
lean_object* v_e_7_; lean_object* v___x_8_; 
v_e_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_e_7_);
lean_dec_ref(v_t_5_);
v___x_8_ = lean_apply_1(v_k_6_, v_e_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim___redArg(lean_object* v_t_21_, lean_object* v_ite_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_21_, v_ite_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_ite_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_25_, v_ite_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim___redArg(lean_object* v_t_29_, lean_object* v_dite_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_29_, v_dite_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_dite_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_33_, v_dite_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_cond_elim___redArg(lean_object* v_t_37_, lean_object* v_cond_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_37_, v_cond_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_cond_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_cond_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_41_, v_cond_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim___redArg(lean_object* v_t_45_, lean_object* v_matcher_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_45_, v_matcher_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_matcher_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_49_, v_matcher_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_box(0);
v___x_57_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1));
v___x_58_ = l_Lean_Expr_const___override(v___x_57_, v___x_56_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2, &l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2);
v___x_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default(void){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3, &l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default;
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
lean_object* v_zero_65_; uint8_t v_isZero_66_; 
v_zero_65_ = lean_unsigned_to_nat(0u);
v_isZero_66_ = lean_nat_dec_eq(v_x_63_, v_zero_65_);
if (v_isZero_66_ == 1)
{
lean_dec(v_x_63_);
return v_x_64_;
}
else
{
lean_object* v_one_67_; lean_object* v_n_68_; 
v_one_67_ = lean_unsigned_to_nat(1u);
v_n_68_ = lean_nat_sub(v_x_63_, v_one_67_);
lean_dec(v_x_63_);
if (lean_obj_tag(v_x_64_) == 1)
{
lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_80_; 
v_val_69_ = lean_ctor_get(v_x_64_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v_x_64_);
if (v_isSharedCheck_80_ == 0)
{
v___x_71_ = v_x_64_;
v_isShared_72_ = v_isSharedCheck_80_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_dec(v_x_64_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_80_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
if (lean_obj_tag(v_val_69_) == 6)
{
lean_object* v_body_73_; lean_object* v___x_75_; 
v_body_73_ = lean_ctor_get(v_val_69_, 2);
lean_inc_ref(v_body_73_);
lean_dec_ref_known(v_val_69_, 3);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v_body_73_);
v___x_75_ = v___x_71_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_body_73_);
v___x_75_ = v_reuseFailAlloc_77_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
v_x_63_ = v_n_68_;
v_x_64_ = v___x_75_;
goto _start;
}
}
else
{
lean_object* v___x_78_; 
lean_del_object(v___x_71_);
lean_dec(v_val_69_);
v___x_78_ = lean_box(0);
v_x_63_ = v_n_68_;
v_x_64_ = v___x_78_;
goto _start;
}
}
}
else
{
lean_object* v___x_81_; 
lean_dec(v_x_64_);
v___x_81_ = lean_box(0);
v_x_63_ = v_n_68_;
v_x_64_ = v___x_81_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_resTy(lean_object* v_info_83_){
_start:
{
lean_object* v_e_85_; 
if (lean_obj_tag(v_info_83_) == 3)
{
lean_object* v_matcherApp_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_108_; 
v_matcherApp_91_ = lean_ctor_get(v_info_83_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v_info_83_);
if (v_isSharedCheck_108_ == 0)
{
v___x_93_ = v_info_83_;
v_isShared_94_ = v_isSharedCheck_108_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_matcherApp_91_);
lean_dec(v_info_83_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_108_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v_toMatcherInfo_95_; lean_object* v_motive_96_; lean_object* v_discrInfos_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v_toMatcherInfo_95_ = lean_ctor_get(v_matcherApp_91_, 0);
lean_inc_ref(v_toMatcherInfo_95_);
v_motive_96_ = lean_ctor_get(v_matcherApp_91_, 4);
lean_inc_ref_n(v_motive_96_, 2);
lean_dec_ref(v_matcherApp_91_);
v_discrInfos_97_ = lean_ctor_get(v_toMatcherInfo_95_, 4);
lean_inc_ref(v_discrInfos_97_);
lean_dec_ref(v_toMatcherInfo_95_);
v___x_98_ = lean_array_get_size(v_discrInfos_97_);
lean_dec_ref(v_discrInfos_97_);
if (v_isShared_94_ == 0)
{
lean_ctor_set_tag(v___x_93_, 1);
lean_ctor_set(v___x_93_, 0, v_motive_96_);
v___x_100_ = v___x_93_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_motive_96_);
v___x_100_ = v_reuseFailAlloc_107_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(v___x_98_, v___x_100_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_dec_ref(v_motive_96_);
return v___x_101_;
}
else
{
lean_object* v_val_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_val_102_ = lean_ctor_get(v___x_101_, 0);
v___x_103_ = l_Lean_Expr_looseBVarRange(v_val_102_);
v___x_104_ = l_Lean_Expr_looseBVarRange(v_motive_96_);
lean_dec_ref(v_motive_96_);
v___x_105_ = lean_nat_dec_eq(v___x_103_, v___x_104_);
lean_dec(v___x_104_);
lean_dec(v___x_103_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; 
lean_dec_ref_known(v___x_101_, 1);
v___x_106_ = lean_box(0);
return v___x_106_;
}
else
{
return v___x_101_;
}
}
}
}
}
else
{
lean_object* v_e_109_; 
v_e_109_ = lean_ctor_get(v_info_83_, 0);
lean_inc_ref(v_e_109_);
lean_dec_ref(v_info_83_);
v_e_85_ = v_e_109_;
goto v___jp_84_;
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_86_ = l_Lean_Expr_getAppNumArgs(v_e_85_);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_sub(v___x_86_, v___x_87_);
lean_dec(v___x_86_);
v___x_89_ = l_Lean_Expr_getRevArg_x21(v_e_85_, v___x_88_);
lean_dec_ref(v_e_85_);
v___x_90_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
return v___x_90_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object* v_matcherApp_110_, size_t v_sz_111_, size_t v_i_112_, lean_object* v_bs_113_){
_start:
{
uint8_t v___x_114_; 
v___x_114_ = lean_usize_dec_lt(v_i_112_, v_sz_111_);
if (v___x_114_ == 0)
{
return v_bs_113_;
}
else
{
lean_object* v_v_115_; lean_object* v_alts_116_; lean_object* v___x_117_; lean_object* v_bs_x27_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; size_t v___x_123_; size_t v___x_124_; lean_object* v___x_125_; 
v_v_115_ = lean_array_uget(v_bs_113_, v_i_112_);
v_alts_116_ = lean_ctor_get(v_matcherApp_110_, 6);
v___x_117_ = lean_unsigned_to_nat(0u);
v_bs_x27_118_ = lean_array_uset(v_bs_113_, v_i_112_, v___x_117_);
v___x_119_ = l_Lean_instInhabitedExpr;
v___x_120_ = lean_usize_to_nat(v_i_112_);
v___x_121_ = lean_array_get_borrowed(v___x_119_, v_alts_116_, v___x_120_);
lean_dec(v___x_120_);
lean_inc(v___x_121_);
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_v_115_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = ((size_t)1ULL);
v___x_124_ = lean_usize_add(v_i_112_, v___x_123_);
v___x_125_ = lean_array_uset(v_bs_x27_118_, v_i_112_, v___x_122_);
v_i_112_ = v___x_124_;
v_bs_113_ = v___x_125_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_110_ = stack[0].m_obj;
size_t v_sz_111_ = stack[1].m_num;
size_t v_i_112_ = stack[2].m_num;
lean_object* v_bs_113_ = stack[3].m_obj;
lean_object* v_res_127_;
v_res_127_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_110_, v_sz_111_, v_i_112_, v_bs_113_);
stack->m_obj
 = v_res_127_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object* v_matcherApp_128_, lean_object* v_sz_129_, lean_object* v_i_130_, lean_object* v_bs_131_){
_start:
{
size_t v_sz_boxed_132_; size_t v_i_boxed_133_; lean_object* v_res_134_; 
v_sz_boxed_132_ = lean_unbox_usize(v_sz_129_);
lean_dec(v_sz_129_);
v_i_boxed_133_ = lean_unbox_usize(v_i_130_);
lean_dec(v_i_130_);
v_res_134_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_128_, v_sz_boxed_132_, v_i_boxed_133_, v_bs_131_);
lean_dec_ref(v_matcherApp_128_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object* v_info_135_){
_start:
{
switch(lean_obj_tag(v_info_135_))
{
case 0:
{
lean_object* v_e_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_e_136_ = lean_ctor_get(v_info_135_, 0);
lean_inc_ref(v_e_136_);
lean_dec_ref_known(v_info_135_, 1);
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_unsigned_to_nat(3u);
v___x_139_ = l_Lean_Expr_getAppNumArgs(v_e_136_);
v___x_140_ = lean_nat_sub(v___x_139_, v___x_138_);
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = lean_nat_sub(v___x_140_, v___x_141_);
lean_dec(v___x_140_);
v___x_143_ = l_Lean_Expr_getRevArg_x21(v_e_136_, v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_137_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = lean_unsigned_to_nat(4u);
v___x_146_ = lean_nat_sub(v___x_139_, v___x_145_);
lean_dec(v___x_139_);
v___x_147_ = lean_nat_sub(v___x_146_, v___x_141_);
lean_dec(v___x_146_);
v___x_148_ = l_Lean_Expr_getRevArg_x21(v_e_136_, v___x_147_);
lean_dec_ref(v_e_136_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_137_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = lean_unsigned_to_nat(2u);
v___x_151_ = lean_mk_empty_array_with_capacity(v___x_150_);
v___x_152_ = lean_array_push(v___x_151_, v___x_144_);
v___x_153_ = lean_array_push(v___x_152_, v___x_149_);
return v___x_153_;
}
case 1:
{
lean_object* v_e_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_e_154_ = lean_ctor_get(v_info_135_, 0);
lean_inc_ref(v_e_154_);
lean_dec_ref_known(v_info_135_, 1);
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = lean_unsigned_to_nat(3u);
v___x_157_ = l_Lean_Expr_getAppNumArgs(v_e_154_);
v___x_158_ = lean_nat_sub(v___x_157_, v___x_156_);
v___x_159_ = lean_nat_sub(v___x_158_, v___x_155_);
lean_dec(v___x_158_);
v___x_160_ = l_Lean_Expr_getRevArg_x21(v_e_154_, v___x_159_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_155_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_unsigned_to_nat(4u);
v___x_163_ = lean_nat_sub(v___x_157_, v___x_162_);
lean_dec(v___x_157_);
v___x_164_ = lean_nat_sub(v___x_163_, v___x_155_);
lean_dec(v___x_163_);
v___x_165_ = l_Lean_Expr_getRevArg_x21(v_e_154_, v___x_164_);
lean_dec_ref(v_e_154_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_155_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_unsigned_to_nat(2u);
v___x_168_ = lean_mk_empty_array_with_capacity(v___x_167_);
v___x_169_ = lean_array_push(v___x_168_, v___x_161_);
v___x_170_ = lean_array_push(v___x_169_, v___x_166_);
return v___x_170_;
}
case 2:
{
lean_object* v_e_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_e_171_ = lean_ctor_get(v_info_135_, 0);
lean_inc_ref(v_e_171_);
lean_dec_ref_known(v_info_135_, 1);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_unsigned_to_nat(2u);
v___x_174_ = l_Lean_Expr_getAppNumArgs(v_e_171_);
v___x_175_ = lean_nat_sub(v___x_174_, v___x_173_);
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_nat_sub(v___x_175_, v___x_176_);
lean_dec(v___x_175_);
v___x_178_ = l_Lean_Expr_getRevArg_x21(v_e_171_, v___x_177_);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_172_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_unsigned_to_nat(3u);
v___x_181_ = lean_nat_sub(v___x_174_, v___x_180_);
lean_dec(v___x_174_);
v___x_182_ = lean_nat_sub(v___x_181_, v___x_176_);
lean_dec(v___x_181_);
v___x_183_ = l_Lean_Expr_getRevArg_x21(v_e_171_, v___x_182_);
lean_dec_ref(v_e_171_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_172_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = lean_mk_empty_array_with_capacity(v___x_173_);
v___x_186_ = lean_array_push(v___x_185_, v___x_179_);
v___x_187_ = lean_array_push(v___x_186_, v___x_184_);
return v___x_187_;
}
default: 
{
lean_object* v_matcherApp_188_; lean_object* v___x_189_; size_t v_sz_190_; size_t v___x_191_; lean_object* v___x_192_; 
v_matcherApp_188_ = lean_ctor_get(v_info_135_, 0);
lean_inc_ref_n(v_matcherApp_188_, 2);
lean_dec_ref_known(v_info_135_, 1);
v___x_189_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_188_);
v_sz_190_ = lean_array_size(v___x_189_);
v___x_191_ = ((size_t)0ULL);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_188_, v_sz_190_, v___x_191_, v___x_189_);
lean_dec_ref(v_matcherApp_188_);
return v___x_192_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object* v_matcherApp_193_, lean_object* v_as_194_, size_t v_sz_195_, size_t v_i_196_, lean_object* v_bs_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_193_, v_sz_195_, v_i_196_, v_bs_197_);
return v___x_198_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_matcherApp_193_ = stack[0].m_obj;
lean_object* v_as_194_ = stack[1].m_obj;
size_t v_sz_195_ = stack[2].m_num;
size_t v_i_196_ = stack[3].m_num;
lean_object* v_bs_197_ = stack[4].m_obj;
lean_object* v_res_199_;
v_res_199_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(v_matcherApp_193_, v_as_194_, v_sz_195_, v_i_196_, v_bs_197_);
stack->m_obj
 = v_res_199_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object* v_matcherApp_200_, lean_object* v_as_201_, lean_object* v_sz_202_, lean_object* v_i_203_, lean_object* v_bs_204_){
_start:
{
size_t v_sz_boxed_205_; size_t v_i_boxed_206_; lean_object* v_res_207_; 
v_sz_boxed_205_ = lean_unbox_usize(v_sz_202_);
lean_dec(v_sz_202_);
v_i_boxed_206_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_res_207_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(v_matcherApp_200_, v_as_201_, v_sz_boxed_205_, v_i_boxed_206_, v_bs_204_);
lean_dec_ref(v_as_201_);
lean_dec_ref(v_matcherApp_200_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_expr(lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_208_) == 3)
{
lean_object* v_matcherApp_209_; lean_object* v___x_210_; 
v_matcherApp_209_ = lean_ctor_get(v_x_208_, 0);
lean_inc_ref(v_matcherApp_209_);
lean_dec_ref_known(v_x_208_, 1);
v___x_210_ = l_Lean_Meta_MatcherApp_toExpr(v_matcherApp_209_);
return v___x_210_;
}
else
{
lean_object* v_e_211_; 
v_e_211_ = lean_ctor_get(v_x_208_, 0);
lean_inc_ref(v_e_211_);
lean_dec_ref(v_x_208_);
return v_e_211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0(lean_object* v___x_215_, lean_object* v_resTy_216_, lean_object* v_c_217_, lean_object* v_dec_218_, lean_object* v_t_219_, lean_object* v_e_220_, lean_object* v_k_221_, lean_object* v_u_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_223_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_224_, 0, v_u_222_);
lean_ctor_set(v___x_224_, 1, v___x_215_);
v___x_225_ = l_Lean_mkConst(v___x_223_, v___x_224_);
lean_inc_ref(v_e_220_);
lean_inc_ref(v_t_219_);
lean_inc_ref(v_dec_218_);
lean_inc_ref(v_c_217_);
v___x_226_ = l_Lean_mkApp5(v___x_225_, v_resTy_216_, v_c_217_, v_dec_218_, v_t_219_, v_e_220_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
v___x_228_ = lean_unsigned_to_nat(4u);
v___x_229_ = lean_mk_empty_array_with_capacity(v___x_228_);
v___x_230_ = lean_array_push(v___x_229_, v_c_217_);
v___x_231_ = lean_array_push(v___x_230_, v_dec_218_);
v___x_232_ = lean_array_push(v___x_231_, v_t_219_);
v___x_233_ = lean_array_push(v___x_232_, v_e_220_);
v___x_234_ = lean_apply_2(v_k_221_, v___x_227_, v___x_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1(lean_object* v___x_235_, lean_object* v_resTy_236_, lean_object* v_c_237_, lean_object* v_dec_238_, lean_object* v_t_239_, lean_object* v_k_240_, lean_object* v_inst_241_, lean_object* v_toBind_242_, lean_object* v_e_243_){
_start:
{
lean_object* v___f_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
lean_inc_ref(v_resTy_236_);
v___f_244_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0), 8, 7);
lean_closure_set(v___f_244_, 0, v___x_235_);
lean_closure_set(v___f_244_, 1, v_resTy_236_);
lean_closure_set(v___f_244_, 2, v_c_237_);
lean_closure_set(v___f_244_, 3, v_dec_238_);
lean_closure_set(v___f_244_, 4, v_t_239_);
lean_closure_set(v___f_244_, 5, v_e_243_);
lean_closure_set(v___f_244_, 6, v_k_240_);
v___x_245_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_245_, 0, v_resTy_236_);
v___x_246_ = lean_apply_2(v_inst_241_, lean_box(0), v___x_245_);
v___x_247_ = lean_apply_4(v_toBind_242_, lean_box(0), lean_box(0), v___x_246_, v___f_244_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2(lean_object* v___x_251_, lean_object* v_resTy_252_, lean_object* v_c_253_, lean_object* v_dec_254_, lean_object* v_k_255_, lean_object* v_inst_256_, lean_object* v_toBind_257_, lean_object* v_inst_258_, lean_object* v_inst_259_, lean_object* v_t_260_){
_start:
{
lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
lean_inc_ref(v_resTy_252_);
v___f_261_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1), 9, 8);
lean_closure_set(v___f_261_, 0, v___x_251_);
lean_closure_set(v___f_261_, 1, v_resTy_252_);
lean_closure_set(v___f_261_, 2, v_c_253_);
lean_closure_set(v___f_261_, 3, v_dec_254_);
lean_closure_set(v___f_261_, 4, v_t_260_);
lean_closure_set(v___f_261_, 5, v_k_255_);
lean_closure_set(v___f_261_, 6, v_inst_256_);
lean_closure_set(v___f_261_, 7, v_toBind_257_);
v___x_262_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_263_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_258_, v_inst_259_, v___x_262_, v_resTy_252_, v___f_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3(lean_object* v___x_267_, lean_object* v_resTy_268_, lean_object* v_c_269_, lean_object* v_k_270_, lean_object* v_inst_271_, lean_object* v_toBind_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_dec_275_){
_start:
{
lean_object* v___f_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_inc_ref(v_inst_274_);
lean_inc_ref(v_inst_273_);
lean_inc_ref(v_resTy_268_);
v___f_276_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2), 10, 9);
lean_closure_set(v___f_276_, 0, v___x_267_);
lean_closure_set(v___f_276_, 1, v_resTy_268_);
lean_closure_set(v___f_276_, 2, v_c_269_);
lean_closure_set(v___f_276_, 3, v_dec_275_);
lean_closure_set(v___f_276_, 4, v_k_270_);
lean_closure_set(v___f_276_, 5, v_inst_271_);
lean_closure_set(v___f_276_, 6, v_toBind_272_);
lean_closure_set(v___f_276_, 7, v_inst_273_);
lean_closure_set(v___f_276_, 8, v_inst_274_);
v___x_277_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_278_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_273_, v_inst_274_, v___x_277_, v_resTy_268_, v___f_276_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_box(0);
v___x_286_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3));
v___x_287_ = l_Lean_mkConst(v___x_286_, v___x_285_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4(lean_object* v_resTy_288_, lean_object* v_k_289_, lean_object* v_inst_290_, lean_object* v_toBind_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_c_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_295_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_296_ = lean_box(0);
lean_inc_ref(v_inst_293_);
lean_inc_ref(v_inst_292_);
lean_inc_ref(v_c_294_);
v___f_297_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3), 9, 8);
lean_closure_set(v___f_297_, 0, v___x_296_);
lean_closure_set(v___f_297_, 1, v_resTy_288_);
lean_closure_set(v___f_297_, 2, v_c_294_);
lean_closure_set(v___f_297_, 3, v_k_289_);
lean_closure_set(v___f_297_, 4, v_inst_290_);
lean_closure_set(v___f_297_, 5, v_toBind_291_);
lean_closure_set(v___f_297_, 6, v_inst_292_);
lean_closure_set(v___f_297_, 7, v_inst_293_);
v___x_298_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_299_ = l_Lean_Expr_app___override(v___x_298_, v_c_294_);
v___x_300_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_292_, v_inst_293_, v___x_295_, v___x_299_, v___f_297_);
return v___x_300_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(lean_object* v_c_301_, lean_object* v_resTy_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_mkArrow(v_c_301_, v_resTy_302_, v___y_305_, v___y_306_);
return v___x_308_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_301_ = stack[0].m_obj;
lean_object* v_resTy_302_ = stack[1].m_obj;
lean_object* v___y_303_ = stack[2].m_obj;
lean_object* v___y_304_ = stack[3].m_obj;
lean_object* v___y_305_ = stack[4].m_obj;
lean_object* v___y_306_ = stack[5].m_obj;
lean_object* v_res_309_;
v_res_309_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(v_c_301_, v_resTy_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
stack->m_obj
 = v_res_309_;
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
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(lean_object* v___x_382_, lean_object* v_resTy_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_mkArrow(v___x_382_, v_resTy_383_, v___y_386_, v___y_387_);
return v___x_389_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_382_ = stack[0].m_obj;
lean_object* v_resTy_383_ = stack[1].m_obj;
lean_object* v___y_384_ = stack[2].m_obj;
lean_object* v___y_385_ = stack[3].m_obj;
lean_object* v___y_386_ = stack[4].m_obj;
lean_object* v___y_387_ = stack[5].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(v___x_382_, v_resTy_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(lean_object* v___x_391_, lean_object* v_resTy_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(v___x_391_, v_resTy_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(lean_object* v___x_399_, lean_object* v_resTy_400_, lean_object* v_c_401_, lean_object* v_dec_402_, lean_object* v_k_403_, lean_object* v_inst_404_, lean_object* v_toBind_405_, lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_tTy_408_){
_start:
{
lean_object* v___f_409_; lean_object* v___x_410_; lean_object* v___f_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
lean_inc(v_toBind_405_);
lean_inc(v_inst_404_);
lean_inc_ref(v_c_401_);
lean_inc_ref(v_resTy_400_);
v___f_409_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9), 11, 10);
lean_closure_set(v___f_409_, 0, v___x_399_);
lean_closure_set(v___f_409_, 1, v_resTy_400_);
lean_closure_set(v___f_409_, 2, v_c_401_);
lean_closure_set(v___f_409_, 3, v_dec_402_);
lean_closure_set(v___f_409_, 4, v_k_403_);
lean_closure_set(v___f_409_, 5, v_inst_404_);
lean_closure_set(v___f_409_, 6, v_toBind_405_);
lean_closure_set(v___f_409_, 7, v_inst_406_);
lean_closure_set(v___f_409_, 8, v_inst_407_);
lean_closure_set(v___f_409_, 9, v_tTy_408_);
v___x_410_ = l_Lean_mkNot(v_c_401_);
v___f_411_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed), 7, 2);
lean_closure_set(v___f_411_, 0, v___x_410_);
lean_closure_set(v___f_411_, 1, v_resTy_400_);
v___x_412_ = lean_apply_2(v_inst_404_, lean_box(0), v___f_411_);
v___x_413_ = lean_apply_4(v_toBind_405_, lean_box(0), lean_box(0), v___x_412_, v___f_409_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(lean_object* v___x_414_, lean_object* v_resTy_415_, lean_object* v_c_416_, lean_object* v_k_417_, lean_object* v_inst_418_, lean_object* v_toBind_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v___f_422_, lean_object* v_dec_423_){
_start:
{
lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_inc(v_toBind_419_);
lean_inc(v_inst_418_);
v___f_424_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11), 10, 9);
lean_closure_set(v___f_424_, 0, v___x_414_);
lean_closure_set(v___f_424_, 1, v_resTy_415_);
lean_closure_set(v___f_424_, 2, v_c_416_);
lean_closure_set(v___f_424_, 3, v_dec_423_);
lean_closure_set(v___f_424_, 4, v_k_417_);
lean_closure_set(v___f_424_, 5, v_inst_418_);
lean_closure_set(v___f_424_, 6, v_toBind_419_);
lean_closure_set(v___f_424_, 7, v_inst_420_);
lean_closure_set(v___f_424_, 8, v_inst_421_);
v___x_425_ = lean_apply_2(v_inst_418_, lean_box(0), v___f_422_);
v___x_426_ = lean_apply_4(v_toBind_419_, lean_box(0), lean_box(0), v___x_425_, v___f_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(lean_object* v_resTy_427_, lean_object* v_k_428_, lean_object* v_inst_429_, lean_object* v_toBind_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_c_433_){
_start:
{
lean_object* v___f_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___f_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
lean_inc_ref(v_resTy_427_);
lean_inc_ref_n(v_c_433_, 2);
v___f_434_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed), 7, 2);
lean_closure_set(v___f_434_, 0, v_c_433_);
lean_closure_set(v___f_434_, 1, v_resTy_427_);
v___x_435_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_436_ = lean_box(0);
lean_inc_ref(v_inst_432_);
lean_inc_ref(v_inst_431_);
v___f_437_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12), 10, 9);
lean_closure_set(v___f_437_, 0, v___x_436_);
lean_closure_set(v___f_437_, 1, v_resTy_427_);
lean_closure_set(v___f_437_, 2, v_c_433_);
lean_closure_set(v___f_437_, 3, v_k_428_);
lean_closure_set(v___f_437_, 4, v_inst_429_);
lean_closure_set(v___f_437_, 5, v_toBind_430_);
lean_closure_set(v___f_437_, 6, v_inst_431_);
lean_closure_set(v___f_437_, 7, v_inst_432_);
lean_closure_set(v___f_437_, 8, v___f_434_);
v___x_438_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_439_ = l_Lean_Expr_app___override(v___x_438_, v_c_433_);
v___x_440_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_431_, v_inst_432_, v___x_435_, v___x_439_, v___f_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object* v___x_444_, lean_object* v_resTy_445_, lean_object* v_c_446_, lean_object* v_t_447_, lean_object* v_e_448_, lean_object* v_k_449_, lean_object* v_u_450_){
_start:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_451_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_452_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_452_, 0, v_u_450_);
lean_ctor_set(v___x_452_, 1, v___x_444_);
v___x_453_ = l_Lean_mkConst(v___x_451_, v___x_452_);
lean_inc_ref(v_e_448_);
lean_inc_ref(v_t_447_);
lean_inc_ref(v_c_446_);
v___x_454_ = l_Lean_mkApp4(v___x_453_, v_resTy_445_, v_c_446_, v_t_447_, v_e_448_);
v___x_455_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
v___x_456_ = lean_unsigned_to_nat(3u);
v___x_457_ = lean_mk_empty_array_with_capacity(v___x_456_);
v___x_458_ = lean_array_push(v___x_457_, v_c_446_);
v___x_459_ = lean_array_push(v___x_458_, v_t_447_);
v___x_460_ = lean_array_push(v___x_459_, v_e_448_);
v___x_461_ = lean_apply_2(v_k_449_, v___x_455_, v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object* v___x_462_, lean_object* v_resTy_463_, lean_object* v_c_464_, lean_object* v_t_465_, lean_object* v_k_466_, lean_object* v_inst_467_, lean_object* v_toBind_468_, lean_object* v_e_469_){
_start:
{
lean_object* v___f_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
lean_inc_ref(v_resTy_463_);
v___f_470_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14), 7, 6);
lean_closure_set(v___f_470_, 0, v___x_462_);
lean_closure_set(v___f_470_, 1, v_resTy_463_);
lean_closure_set(v___f_470_, 2, v_c_464_);
lean_closure_set(v___f_470_, 3, v_t_465_);
lean_closure_set(v___f_470_, 4, v_e_469_);
lean_closure_set(v___f_470_, 5, v_k_466_);
v___x_471_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_471_, 0, v_resTy_463_);
v___x_472_ = lean_apply_2(v_inst_467_, lean_box(0), v___x_471_);
v___x_473_ = lean_apply_4(v_toBind_468_, lean_box(0), lean_box(0), v___x_472_, v___f_470_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object* v___x_474_, lean_object* v_resTy_475_, lean_object* v_c_476_, lean_object* v_k_477_, lean_object* v_inst_478_, lean_object* v_toBind_479_, lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_t_482_){
_start:
{
lean_object* v___f_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
lean_inc_ref(v_resTy_475_);
v___f_483_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15), 8, 7);
lean_closure_set(v___f_483_, 0, v___x_474_);
lean_closure_set(v___f_483_, 1, v_resTy_475_);
lean_closure_set(v___f_483_, 2, v_c_476_);
lean_closure_set(v___f_483_, 3, v_t_482_);
lean_closure_set(v___f_483_, 4, v_k_477_);
lean_closure_set(v___f_483_, 5, v_inst_478_);
lean_closure_set(v___f_483_, 6, v_toBind_479_);
v___x_484_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_485_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_480_, v_inst_481_, v___x_484_, v_resTy_475_, v___f_483_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object* v___x_486_, lean_object* v_resTy_487_, lean_object* v_k_488_, lean_object* v_inst_489_, lean_object* v_toBind_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_c_493_){
_start:
{
lean_object* v___f_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
lean_inc_ref(v_inst_492_);
lean_inc_ref(v_inst_491_);
lean_inc_ref(v_resTy_487_);
v___f_494_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16), 9, 8);
lean_closure_set(v___f_494_, 0, v___x_486_);
lean_closure_set(v___f_494_, 1, v_resTy_487_);
lean_closure_set(v___f_494_, 2, v_c_493_);
lean_closure_set(v___f_494_, 3, v_k_488_);
lean_closure_set(v___f_494_, 4, v_inst_489_);
lean_closure_set(v___f_494_, 5, v_toBind_490_);
lean_closure_set(v___f_494_, 6, v_inst_491_);
lean_closure_set(v___f_494_, 7, v_inst_492_);
v___x_495_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_496_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_491_, v_inst_492_, v___x_495_, v_resTy_487_, v___f_494_);
return v___x_496_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object* v_resTy_497_, lean_object* v_motiveArgs_498_, lean_object* v_x_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
uint8_t v___x_505_; uint8_t v___x_506_; uint8_t v___x_507_; lean_object* v___x_508_; 
v___x_505_ = 0;
v___x_506_ = 1;
v___x_507_ = 1;
v___x_508_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_498_, v_resTy_497_, v___x_505_, v___x_506_, v___x_505_, v___x_506_, v___x_507_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_508_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18_0interp(lean_interpreter_value* stack)
{
lean_object* v_resTy_497_ = stack[0].m_obj;
lean_object* v_motiveArgs_498_ = stack[1].m_obj;
lean_object* v_x_499_ = stack[2].m_obj;
lean_object* v___y_500_ = stack[3].m_obj;
lean_object* v___y_501_ = stack[4].m_obj;
lean_object* v___y_502_ = stack[5].m_obj;
lean_object* v___y_503_ = stack[6].m_obj;
lean_object* v_res_509_;
v_res_509_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(v_resTy_497_, v_motiveArgs_498_, v_x_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
stack->m_obj
 = v_res_509_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed(lean_object* v_resTy_510_, lean_object* v_motiveArgs_511_, lean_object* v_x_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(v_resTy_510_, v_motiveArgs_511_, v_x_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v_x_512_);
lean_dec_ref(v_motiveArgs_511_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object* v_i_522_, lean_object* v_a_523_, lean_object* v_x_524_){
_start:
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_525_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1));
v___x_526_ = lean_unsigned_to_nat(1u);
v___x_527_ = lean_nat_add(v_i_522_, v___x_526_);
v___x_528_ = lean_name_append_index_after(v___x_525_, v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v_a_523_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___boxed(lean_object* v_i_530_, lean_object* v_a_531_, lean_object* v_x_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(v_i_530_, v_a_531_, v_x_532_);
lean_dec(v_i_530_);
return v_res_533_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object* v_i_534_, lean_object* v___x_535_, lean_object* v_discrs_536_, lean_object* v_prior_537_, lean_object* v_next_538_, lean_object* v_acc_539_, lean_object* v_h_540_, lean_object* v_G_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_a_548_; uint8_t v___x_552_; 
v___x_552_ = lean_nat_dec_lt(v_next_538_, v_i_534_);
if (v___x_552_ == 0)
{
lean_object* v___x_553_; 
lean_dec_ref(v_G_541_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v_acc_539_);
return v___x_553_;
}
else
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = lean_array_get_borrowed(v___x_535_, v_discrs_536_, v_next_538_);
v___x_555_ = l_Lean_Expr_isFVar(v___x_554_);
if (v___x_555_ == 0)
{
v_a_548_ = v_acc_539_;
goto v___jp_547_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_array_get_borrowed(v___x_535_, v_prior_537_, v_next_538_);
lean_inc(v___x_554_);
v___x_557_ = l_Lean_Expr_replaceFVar(v_acc_539_, v___x_554_, v___x_556_);
lean_dec_ref(v_acc_539_);
v_a_548_ = v___x_557_;
goto v___jp_547_;
}
}
v___jp_547_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_add(v_next_538_, v___x_549_);
lean_inc(v___y_545_);
lean_inc_ref(v___y_544_);
lean_inc(v___y_543_);
lean_inc_ref(v___y_542_);
v___x_551_ = lean_apply_9(v_G_541_, v___x_550_, v_a_548_, lean_box(0), lean_box(0), v___y_542_, v___y_543_, v___y_544_, v___y_545_, lean_box(0));
return v___x_551_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_i_534_ = stack[0].m_obj;
lean_object* v___x_535_ = stack[1].m_obj;
lean_object* v_discrs_536_ = stack[2].m_obj;
lean_object* v_prior_537_ = stack[3].m_obj;
lean_object* v_next_538_ = stack[4].m_obj;
lean_object* v_acc_539_ = stack[5].m_obj;
lean_object* v_G_541_ = stack[7].m_obj;
lean_object* v___y_542_ = stack[8].m_obj;
lean_object* v___y_543_ = stack[9].m_obj;
lean_object* v___y_544_ = stack[10].m_obj;
lean_object* v___y_545_ = stack[11].m_obj;
lean_object* v_res_558_;
v_res_558_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(v_i_534_, v___x_535_, v_discrs_536_, v_prior_537_, v_next_538_, v_acc_539_, lean_box(0), v_G_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
stack->m_obj
 = v_res_558_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed(lean_object* v_i_559_, lean_object* v___x_560_, lean_object* v_discrs_561_, lean_object* v_prior_562_, lean_object* v_next_563_, lean_object* v_acc_564_, lean_object* v_h_565_, lean_object* v_G_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(v_i_559_, v___x_560_, v_discrs_561_, v_prior_562_, v_next_563_, v_acc_564_, v_h_565_, v_G_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v_next_563_);
lean_dec_ref(v_prior_562_);
lean_dec_ref(v_discrs_561_);
lean_dec_ref(v___x_560_);
lean_dec(v_i_559_);
return v_res_572_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object* v_a_573_, lean_object* v___f_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v___x_580_; 
lean_inc(v___y_578_);
lean_inc_ref(v___y_577_);
lean_inc(v___y_576_);
lean_inc_ref(v___y_575_);
v___x_580_ = lean_infer_type(v_a_573_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_582_; lean_object* v___x_2423__overap_583_; lean_object* v___x_584_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
lean_inc(v_a_581_);
lean_dec_ref_known(v___x_580_, 1);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_2423__overap_583_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_574_, v___x_582_, v_a_581_, lean_box(0));
v___x_584_ = lean_apply_5(v___x_2423__overap_583_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, lean_box(0));
return v___x_584_;
}
else
{
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec_ref(v___f_574_);
return v___x_580_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_573_ = stack[0].m_obj;
lean_object* v___f_574_ = stack[1].m_obj;
lean_object* v___y_575_ = stack[2].m_obj;
lean_object* v___y_576_ = stack[3].m_obj;
lean_object* v___y_577_ = stack[4].m_obj;
lean_object* v___y_578_ = stack[5].m_obj;
lean_object* v_res_585_;
v_res_585_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(v_a_573_, v___f_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
stack->m_obj
 = v_res_585_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed(lean_object* v_a_586_, lean_object* v___f_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(v_a_586_, v___f_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object* v_i_594_, lean_object* v___x_595_, lean_object* v_discrs_596_, lean_object* v_a_597_, lean_object* v_inst_598_, lean_object* v_prior_599_){
_start:
{
lean_object* v___f_600_; lean_object* v___f_601_; lean_object* v___x_602_; 
v___f_600_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed), 13, 4);
lean_closure_set(v___f_600_, 0, v_i_594_);
lean_closure_set(v___f_600_, 1, v___x_595_);
lean_closure_set(v___f_600_, 2, v_discrs_596_);
lean_closure_set(v___f_600_, 3, v_prior_599_);
v___f_601_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed), 7, 2);
lean_closure_set(v___f_601_, 0, v_a_597_);
lean_closure_set(v___f_601_, 1, v___f_600_);
v___x_602_ = lean_apply_2(v_inst_598_, lean_box(0), v___f_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object* v___x_606_, lean_object* v_discrs_607_, lean_object* v_inst_608_, lean_object* v_i_609_, lean_object* v_a_610_, lean_object* v_x_611_){
_start:
{
lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_inc(v_i_609_);
v___f_612_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22), 6, 5);
lean_closure_set(v___f_612_, 0, v_i_609_);
lean_closure_set(v___f_612_, 1, v___x_606_);
lean_closure_set(v___f_612_, 2, v_discrs_607_);
lean_closure_set(v___f_612_, 3, v_a_610_);
lean_closure_set(v___f_612_, 4, v_inst_608_);
v___x_613_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__1));
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_add(v_i_609_, v___x_614_);
lean_dec(v_i_609_);
v___x_616_ = lean_name_append_index_after(v___x_613_, v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___f_612_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object* v_toMatcherInfo_620_, lean_object* v_matcherName_621_, lean_object* v_matcherLevels_622_, lean_object* v_params_623_, lean_object* v_motive_624_, lean_object* v_discrs_625_, lean_object* v_alts_626_, lean_object* v_k_627_, lean_object* v_____do__lift_628_){
_start:
{
lean_object* v___x_629_; lean_object* v_abstractMatcherApp_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_629_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
lean_inc_ref(v_discrs_625_);
v_abstractMatcherApp_630_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_abstractMatcherApp_630_, 0, v_toMatcherInfo_620_);
lean_ctor_set(v_abstractMatcherApp_630_, 1, v_matcherName_621_);
lean_ctor_set(v_abstractMatcherApp_630_, 2, v_matcherLevels_622_);
lean_ctor_set(v_abstractMatcherApp_630_, 3, v_params_623_);
lean_ctor_set(v_abstractMatcherApp_630_, 4, v_motive_624_);
lean_ctor_set(v_abstractMatcherApp_630_, 5, v_discrs_625_);
lean_ctor_set(v_abstractMatcherApp_630_, 6, v_____do__lift_628_);
lean_ctor_set(v_abstractMatcherApp_630_, 7, v___x_629_);
v___x_631_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_631_, 0, v_abstractMatcherApp_630_);
v___x_632_ = l_Array_append___redArg(v_discrs_625_, v_alts_626_);
v___x_633_ = lean_apply_2(v_k_627_, v___x_631_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed(lean_object* v_toMatcherInfo_634_, lean_object* v_matcherName_635_, lean_object* v_matcherLevels_636_, lean_object* v_params_637_, lean_object* v_motive_638_, lean_object* v_discrs_639_, lean_object* v_alts_640_, lean_object* v_k_641_, lean_object* v_____do__lift_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(v_toMatcherInfo_634_, v_matcherName_635_, v_matcherLevels_636_, v_params_637_, v_motive_638_, v_discrs_639_, v_alts_640_, v_k_641_, v_____do__lift_642_);
lean_dec_ref(v_alts_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object* v_toMatcherInfo_645_, lean_object* v_matcherName_646_, lean_object* v_matcherLevels_647_, lean_object* v_params_648_, lean_object* v_motive_649_, lean_object* v_discrs_650_, lean_object* v_k_651_, lean_object* v___x_652_, lean_object* v_inst_653_, lean_object* v_toBind_654_, lean_object* v_alts_655_){
_start:
{
lean_object* v___f_656_; lean_object* v___x_657_; size_t v_sz_658_; size_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
lean_inc_ref(v_alts_655_);
v___f_656_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed), 9, 8);
lean_closure_set(v___f_656_, 0, v_toMatcherInfo_645_);
lean_closure_set(v___f_656_, 1, v_matcherName_646_);
lean_closure_set(v___f_656_, 2, v_matcherLevels_647_);
lean_closure_set(v___f_656_, 3, v_params_648_);
lean_closure_set(v___f_656_, 4, v_motive_649_);
lean_closure_set(v___f_656_, 5, v_discrs_650_);
lean_closure_set(v___f_656_, 6, v_alts_655_);
lean_closure_set(v___f_656_, 7, v_k_651_);
v___x_657_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___closed__0));
v_sz_658_ = lean_array_size(v_alts_655_);
v___x_659_ = ((size_t)0ULL);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_652_, v___x_657_, v_sz_658_, v___x_659_, v_alts_655_);
v___x_661_ = lean_apply_2(v_inst_653_, lean_box(0), v___x_660_);
v___x_662_ = lean_apply_4(v_toBind_654_, lean_box(0), lean_box(0), v___x_661_, v___f_656_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object* v___f_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v___f_685_, lean_object* v_origAltTypes_686_){
_start:
{
lean_object* v___x_687_; size_t v_sz_688_; size_t v___x_689_; lean_object* v_altNamesTypes_690_; uint8_t v___x_691_; lean_object* v___x_692_; 
v___x_687_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_688_ = lean_array_size(v_origAltTypes_686_);
v___x_689_ = ((size_t)0ULL);
lean_inc_ref(v_origAltTypes_686_);
v_altNamesTypes_690_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_687_, v_origAltTypes_686_, v___f_682_, v_sz_688_, v___x_689_, v_origAltTypes_686_);
lean_dec_ref(v_origAltTypes_686_);
v___x_691_ = 0;
v___x_692_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_683_, v_inst_684_, v_altNamesTypes_690_, v___f_685_, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object* v_toMatcherInfo_693_, lean_object* v_matcherName_694_, lean_object* v_params_695_, lean_object* v_motive_696_, lean_object* v_discrs_697_, lean_object* v_k_698_, lean_object* v___x_699_, lean_object* v_inst_700_, lean_object* v_toBind_701_, lean_object* v___f_702_, lean_object* v_inst_703_, lean_object* v_inst_704_, lean_object* v_alts_705_, lean_object* v_matcherLevels_706_){
_start:
{
lean_object* v___f_707_; lean_object* v___f_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v_matcherPartial_711_; lean_object* v_matcherPartial_712_; lean_object* v_matcherPartial_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
lean_inc(v_toBind_701_);
lean_inc(v_inst_700_);
lean_inc_ref(v_discrs_697_);
lean_inc_ref(v_motive_696_);
lean_inc_ref(v_params_695_);
lean_inc_ref(v_matcherLevels_706_);
lean_inc(v_matcherName_694_);
v___f_707_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25), 11, 10);
lean_closure_set(v___f_707_, 0, v_toMatcherInfo_693_);
lean_closure_set(v___f_707_, 1, v_matcherName_694_);
lean_closure_set(v___f_707_, 2, v_matcherLevels_706_);
lean_closure_set(v___f_707_, 3, v_params_695_);
lean_closure_set(v___f_707_, 4, v_motive_696_);
lean_closure_set(v___f_707_, 5, v_discrs_697_);
lean_closure_set(v___f_707_, 6, v_k_698_);
lean_closure_set(v___f_707_, 7, v___x_699_);
lean_closure_set(v___f_707_, 8, v_inst_700_);
lean_closure_set(v___f_707_, 9, v_toBind_701_);
v___f_708_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26), 5, 4);
lean_closure_set(v___f_708_, 0, v___f_702_);
lean_closure_set(v___f_708_, 1, v_inst_703_);
lean_closure_set(v___f_708_, 2, v_inst_704_);
lean_closure_set(v___f_708_, 3, v___f_707_);
v___x_709_ = lean_array_to_list(v_matcherLevels_706_);
v___x_710_ = l_Lean_mkConst(v_matcherName_694_, v___x_709_);
v_matcherPartial_711_ = l_Lean_mkAppN(v___x_710_, v_params_695_);
lean_dec_ref(v_params_695_);
v_matcherPartial_712_ = l_Lean_Expr_app___override(v_matcherPartial_711_, v_motive_696_);
v_matcherPartial_713_ = l_Lean_mkAppN(v_matcherPartial_712_, v_discrs_697_);
lean_dec_ref(v_discrs_697_);
v___x_714_ = lean_array_get_size(v_alts_705_);
v___x_715_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_715_, 0, v___x_714_);
lean_closure_set(v___x_715_, 1, v_matcherPartial_713_);
v___x_716_ = lean_apply_2(v_inst_700_, lean_box(0), v___x_715_);
v___x_717_ = lean_apply_4(v_toBind_701_, lean_box(0), lean_box(0), v___x_716_, v___f_708_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object* v_toMatcherInfo_718_, lean_object* v_matcherName_719_, lean_object* v_params_720_, lean_object* v_motive_721_, lean_object* v_discrs_722_, lean_object* v_k_723_, lean_object* v___x_724_, lean_object* v_inst_725_, lean_object* v_toBind_726_, lean_object* v___f_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_alts_730_, lean_object* v_matcherLevels_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(v_toMatcherInfo_718_, v_matcherName_719_, v_params_720_, v_motive_721_, v_discrs_722_, v_k_723_, v___x_724_, v_inst_725_, v_toBind_726_, v___f_727_, v_inst_728_, v_inst_729_, v_alts_730_, v_matcherLevels_731_);
lean_dec_ref(v_alts_730_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28(lean_object* v___f_733_, lean_object* v_matcherLevels_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_apply_1(v___f_733_, v_matcherLevels_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30(lean_object* v_matcherLevels_736_, lean_object* v_val_737_, lean_object* v_toPure_738_, lean_object* v_toBind_739_, lean_object* v___f_740_, lean_object* v_uElim_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_array_set(v_matcherLevels_736_, v_val_737_, v_uElim_741_);
v___x_743_ = lean_apply_2(v_toPure_738_, lean_box(0), v___x_742_);
v___x_744_ = lean_apply_4(v_toBind_739_, lean_box(0), lean_box(0), v___x_743_, v___f_740_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30___boxed(lean_object* v_matcherLevels_745_, lean_object* v_val_746_, lean_object* v_toPure_747_, lean_object* v_toBind_748_, lean_object* v___f_749_, lean_object* v_uElim_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30(v_matcherLevels_745_, v_val_746_, v_toPure_747_, v_toBind_748_, v___f_749_, v_uElim_750_);
lean_dec(v_val_746_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__29(lean_object* v_toMatcherInfo_752_, lean_object* v_matcherName_753_, lean_object* v_params_754_, lean_object* v_discrs_755_, lean_object* v_k_756_, lean_object* v___x_757_, lean_object* v_inst_758_, lean_object* v_toBind_759_, lean_object* v___f_760_, lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_alts_763_, lean_object* v_toPure_764_, lean_object* v_matcherLevels_765_, lean_object* v_resTy_766_, lean_object* v_motive_767_){
_start:
{
lean_object* v_uElimPos_x3f_768_; lean_object* v___f_769_; 
v_uElimPos_x3f_768_ = lean_ctor_get(v_toMatcherInfo_752_, 3);
lean_inc(v_uElimPos_x3f_768_);
lean_inc(v_toBind_759_);
lean_inc(v_inst_758_);
v___f_769_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed), 14, 13);
lean_closure_set(v___f_769_, 0, v_toMatcherInfo_752_);
lean_closure_set(v___f_769_, 1, v_matcherName_753_);
lean_closure_set(v___f_769_, 2, v_params_754_);
lean_closure_set(v___f_769_, 3, v_motive_767_);
lean_closure_set(v___f_769_, 4, v_discrs_755_);
lean_closure_set(v___f_769_, 5, v_k_756_);
lean_closure_set(v___f_769_, 6, v___x_757_);
lean_closure_set(v___f_769_, 7, v_inst_758_);
lean_closure_set(v___f_769_, 8, v_toBind_759_);
lean_closure_set(v___f_769_, 9, v___f_760_);
lean_closure_set(v___f_769_, 10, v_inst_761_);
lean_closure_set(v___f_769_, 11, v_inst_762_);
lean_closure_set(v___f_769_, 12, v_alts_763_);
if (lean_obj_tag(v_uElimPos_x3f_768_) == 0)
{
lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
lean_dec_ref(v_resTy_766_);
lean_dec(v_inst_758_);
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28), 2, 1);
lean_closure_set(v___f_770_, 0, v___f_769_);
v___x_771_ = lean_apply_2(v_toPure_764_, lean_box(0), v_matcherLevels_765_);
v___x_772_ = lean_apply_4(v_toBind_759_, lean_box(0), lean_box(0), v___x_771_, v___f_770_);
return v___x_772_;
}
else
{
lean_object* v_val_773_; lean_object* v___f_774_; lean_object* v___f_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_val_773_ = lean_ctor_get(v_uElimPos_x3f_768_, 0);
lean_inc(v_val_773_);
lean_dec_ref_known(v_uElimPos_x3f_768_, 1);
v___f_774_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28), 2, 1);
lean_closure_set(v___f_774_, 0, v___f_769_);
lean_inc(v_toBind_759_);
v___f_775_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30___boxed), 6, 5);
lean_closure_set(v___f_775_, 0, v_matcherLevels_765_);
lean_closure_set(v___f_775_, 1, v_val_773_);
lean_closure_set(v___f_775_, 2, v_toPure_764_);
lean_closure_set(v___f_775_, 3, v_toBind_759_);
lean_closure_set(v___f_775_, 4, v___f_774_);
v___x_776_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_776_, 0, v_resTy_766_);
v___x_777_ = lean_apply_2(v_inst_758_, lean_box(0), v___x_776_);
v___x_778_ = lean_apply_4(v_toBind_759_, lean_box(0), lean_box(0), v___x_777_, v___f_775_);
return v___x_778_;
}
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(lean_object* v_toMatcherInfo_779_, lean_object* v_matcherName_780_, lean_object* v_params_781_, lean_object* v_k_782_, lean_object* v___x_783_, lean_object* v_inst_784_, lean_object* v_toBind_785_, lean_object* v___f_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_alts_789_, lean_object* v_toPure_790_, lean_object* v_matcherLevels_791_, lean_object* v_resTy_792_, lean_object* v___x_793_, lean_object* v_motive_794_, lean_object* v___f_795_, lean_object* v_discrs_796_){
_start:
{
lean_object* v___f_797_; uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_inc(v_toBind_785_);
lean_inc(v_inst_784_);
lean_inc_ref(v___x_783_);
v___f_797_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__29), 16, 15);
lean_closure_set(v___f_797_, 0, v_toMatcherInfo_779_);
lean_closure_set(v___f_797_, 1, v_matcherName_780_);
lean_closure_set(v___f_797_, 2, v_params_781_);
lean_closure_set(v___f_797_, 3, v_discrs_796_);
lean_closure_set(v___f_797_, 4, v_k_782_);
lean_closure_set(v___f_797_, 5, v___x_783_);
lean_closure_set(v___f_797_, 6, v_inst_784_);
lean_closure_set(v___f_797_, 7, v_toBind_785_);
lean_closure_set(v___f_797_, 8, v___f_786_);
lean_closure_set(v___f_797_, 9, v_inst_787_);
lean_closure_set(v___f_797_, 10, v_inst_788_);
lean_closure_set(v___f_797_, 11, v_alts_789_);
lean_closure_set(v___f_797_, 12, v_toPure_790_);
lean_closure_set(v___f_797_, 13, v_matcherLevels_791_);
lean_closure_set(v___f_797_, 14, v_resTy_792_);
v___x_798_ = 0;
v___x_799_ = l_Lean_Meta_lambdaTelescope___redArg(v___x_793_, v___x_783_, v_motive_794_, v___f_795_, v___x_798_);
v___x_800_ = lean_apply_2(v_inst_784_, lean_box(0), v___x_799_);
v___x_801_ = lean_apply_4(v_toBind_785_, lean_box(0), lean_box(0), v___x_800_, v___f_797_);
return v___x_801_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMatcherInfo_779_ = stack[0].m_obj;
lean_object* v_matcherName_780_ = stack[1].m_obj;
lean_object* v_params_781_ = stack[2].m_obj;
lean_object* v_k_782_ = stack[3].m_obj;
lean_object* v___x_783_ = stack[4].m_obj;
lean_object* v_inst_784_ = stack[5].m_obj;
lean_object* v_toBind_785_ = stack[6].m_obj;
lean_object* v___f_786_ = stack[7].m_obj;
lean_object* v_inst_787_ = stack[8].m_obj;
lean_object* v_inst_788_ = stack[9].m_obj;
lean_object* v_alts_789_ = stack[10].m_obj;
lean_object* v_toPure_790_ = stack[11].m_obj;
lean_object* v_matcherLevels_791_ = stack[12].m_obj;
lean_object* v_resTy_792_ = stack[13].m_obj;
lean_object* v___x_793_ = stack[14].m_obj;
lean_object* v_motive_794_ = stack[15].m_obj;
lean_object* v___f_795_ = stack[16].m_obj;
lean_object* v_discrs_796_ = stack[17].m_obj;
lean_object* v_res_802_;
v_res_802_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(v_toMatcherInfo_779_, v_matcherName_780_, v_params_781_, v_k_782_, v___x_783_, v_inst_784_, v_toBind_785_, v___f_786_, v_inst_787_, v_inst_788_, v_alts_789_, v_toPure_790_, v_matcherLevels_791_, v_resTy_792_, v___x_793_, v_motive_794_, v___f_795_, v_discrs_796_);
stack->m_obj
 = v_res_802_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_803_ = _args[0];
lean_object* v_matcherName_804_ = _args[1];
lean_object* v_params_805_ = _args[2];
lean_object* v_k_806_ = _args[3];
lean_object* v___x_807_ = _args[4];
lean_object* v_inst_808_ = _args[5];
lean_object* v_toBind_809_ = _args[6];
lean_object* v___f_810_ = _args[7];
lean_object* v_inst_811_ = _args[8];
lean_object* v_inst_812_ = _args[9];
lean_object* v_alts_813_ = _args[10];
lean_object* v_toPure_814_ = _args[11];
lean_object* v_matcherLevels_815_ = _args[12];
lean_object* v_resTy_816_ = _args[13];
lean_object* v___x_817_ = _args[14];
lean_object* v_motive_818_ = _args[15];
lean_object* v___f_819_ = _args[16];
lean_object* v_discrs_820_ = _args[17];
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(v_toMatcherInfo_803_, v_matcherName_804_, v_params_805_, v_k_806_, v___x_807_, v_inst_808_, v_toBind_809_, v___f_810_, v_inst_811_, v_inst_812_, v_alts_813_, v_toPure_814_, v_matcherLevels_815_, v_resTy_816_, v___x_817_, v_motive_818_, v___f_819_, v_discrs_820_);
return v_res_821_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0(void){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_instMonadEIO___redArg();
return v___x_822_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0);
v___x_824_ = l_StateRefT_x27_instMonad___redArg(v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = lean_unsigned_to_nat(0u);
v___x_833_ = l_Lean_Level_ofNat(v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8);
v___x_835_ = l_Lean_mkSort(v___x_834_);
return v___x_835_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_box(0);
v___x_840_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__11));
v___x_841_ = l_Lean_mkConst(v___x_840_, v___x_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_info_846_, lean_object* v_resTy_847_, lean_object* v_k_848_){
_start:
{
lean_object* v___x_849_; lean_object* v_toApplicative_850_; lean_object* v_toFunctor_851_; lean_object* v_toSeq_852_; lean_object* v_toSeqLeft_853_; lean_object* v_toSeqRight_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___x_859_; lean_object* v___f_860_; lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_toApplicative_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_947_; 
v___x_849_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_850_ = lean_ctor_get(v___x_849_, 0);
v_toFunctor_851_ = lean_ctor_get(v_toApplicative_850_, 0);
v_toSeq_852_ = lean_ctor_get(v_toApplicative_850_, 2);
v_toSeqLeft_853_ = lean_ctor_get(v_toApplicative_850_, 3);
v_toSeqRight_854_ = lean_ctor_get(v_toApplicative_850_, 4);
v___f_855_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_856_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_851_, 2);
v___f_857_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_857_, 0, v_toFunctor_851_);
v___f_858_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_858_, 0, v_toFunctor_851_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___f_857_);
lean_ctor_set(v___x_859_, 1, v___f_858_);
lean_inc(v_toSeqRight_854_);
v___f_860_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_860_, 0, v_toSeqRight_854_);
lean_inc(v_toSeqLeft_853_);
v___f_861_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_861_, 0, v_toSeqLeft_853_);
lean_inc(v_toSeq_852_);
v___f_862_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_862_, 0, v_toSeq_852_);
v___x_863_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_863_, 0, v___x_859_);
lean_ctor_set(v___x_863_, 1, v___f_855_);
lean_ctor_set(v___x_863_, 2, v___f_862_);
lean_ctor_set(v___x_863_, 3, v___f_861_);
lean_ctor_set(v___x_863_, 4, v___f_860_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___f_856_);
v___x_865_ = l_StateRefT_x27_instMonad___redArg(v___x_864_);
v_toApplicative_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; 
v_unused_948_ = lean_ctor_get(v___x_865_, 1);
lean_dec(v_unused_948_);
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_947_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_toApplicative_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_947_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_toFunctor_870_; lean_object* v_toSeq_871_; lean_object* v_toSeqLeft_872_; lean_object* v_toSeqRight_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_945_; 
v_toFunctor_870_ = lean_ctor_get(v_toApplicative_866_, 0);
v_toSeq_871_ = lean_ctor_get(v_toApplicative_866_, 2);
v_toSeqLeft_872_ = lean_ctor_get(v_toApplicative_866_, 3);
v_toSeqRight_873_ = lean_ctor_get(v_toApplicative_866_, 4);
v_isSharedCheck_945_ = !lean_is_exclusive(v_toApplicative_866_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v_toApplicative_866_, 1);
lean_dec(v_unused_946_);
v___x_875_ = v_toApplicative_866_;
v_isShared_876_ = v_isSharedCheck_945_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_toSeqRight_873_);
lean_inc(v_toSeqLeft_872_);
lean_inc(v_toSeq_871_);
lean_inc(v_toFunctor_870_);
lean_dec(v_toApplicative_866_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_945_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___f_880_; lean_object* v___x_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___x_886_; 
v___f_877_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_870_);
v___f_879_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_879_, 0, v_toFunctor_870_);
v___f_880_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_880_, 0, v_toFunctor_870_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v___f_879_);
lean_ctor_set(v___x_881_, 1, v___f_880_);
v___f_882_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_882_, 0, v_toSeqRight_873_);
v___f_883_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_883_, 0, v_toSeqLeft_872_);
v___f_884_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_884_, 0, v_toSeq_871_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v___f_882_);
lean_ctor_set(v___x_875_, 3, v___f_883_);
lean_ctor_set(v___x_875_, 2, v___f_884_);
lean_ctor_set(v___x_875_, 1, v___f_877_);
lean_ctor_set(v___x_875_, 0, v___x_881_);
v___x_886_ = v___x_875_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v___f_877_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v___f_884_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v___f_883_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v___f_882_);
v___x_886_ = v_reuseFailAlloc_944_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___f_878_);
lean_ctor_set(v___x_868_, 0, v___x_886_);
v___x_888_ = v___x_868_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___f_878_);
v___x_888_ = v_reuseFailAlloc_943_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v_toApplicative_889_; lean_object* v_toFunctor_890_; lean_object* v_toSeq_891_; lean_object* v_toSeqLeft_892_; lean_object* v_toSeqRight_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___x_896_; lean_object* v___f_897_; lean_object* v___f_898_; lean_object* v___f_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_toApplicative_889_ = lean_ctor_get(v___x_849_, 0);
v_toFunctor_890_ = lean_ctor_get(v_toApplicative_889_, 0);
v_toSeq_891_ = lean_ctor_get(v_toApplicative_889_, 2);
v_toSeqLeft_892_ = lean_ctor_get(v_toApplicative_889_, 3);
v_toSeqRight_893_ = lean_ctor_get(v_toApplicative_889_, 4);
lean_inc_ref_n(v_toFunctor_890_, 2);
v___f_894_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_894_, 0, v_toFunctor_890_);
v___f_895_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_895_, 0, v_toFunctor_890_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___f_894_);
lean_ctor_set(v___x_896_, 1, v___f_895_);
lean_inc(v_toSeqRight_893_);
v___f_897_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_897_, 0, v_toSeqRight_893_);
lean_inc(v_toSeqLeft_892_);
v___f_898_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_898_, 0, v_toSeqLeft_892_);
lean_inc(v_toSeq_891_);
v___f_899_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_899_, 0, v_toSeq_891_);
v___x_900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_900_, 0, v___x_896_);
lean_ctor_set(v___x_900_, 1, v___f_855_);
lean_ctor_set(v___x_900_, 2, v___f_899_);
lean_ctor_set(v___x_900_, 3, v___f_898_);
lean_ctor_set(v___x_900_, 4, v___f_897_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_900_);
lean_ctor_set(v___x_901_, 1, v___f_856_);
v___x_902_ = l_StateRefT_x27_instMonad___redArg(v___x_901_);
v___x_903_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_903_, 0, lean_box(0));
lean_closure_set(v___x_903_, 1, lean_box(0));
lean_closure_set(v___x_903_, 2, v___x_902_);
v___x_904_ = l_instMonadControlTOfPure___redArg(v___x_903_);
switch(lean_obj_tag(v_info_846_))
{
case 0:
{
lean_object* v_toBind_905_; lean_object* v___f_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec_ref_known(v_info_846_, 1);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_888_);
v_toBind_905_ = lean_ctor_get(v_inst_845_, 1);
lean_inc_ref(v_inst_845_);
lean_inc_ref(v_inst_844_);
lean_inc(v_toBind_905_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4), 7, 6);
lean_closure_set(v___f_906_, 0, v_resTy_847_);
lean_closure_set(v___f_906_, 1, v_k_848_);
lean_closure_set(v___f_906_, 2, v_inst_843_);
lean_closure_set(v___f_906_, 3, v_toBind_905_);
lean_closure_set(v___f_906_, 4, v_inst_844_);
lean_closure_set(v___f_906_, 5, v_inst_845_);
v___x_907_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_908_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_909_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_844_, v_inst_845_, v___x_907_, v___x_908_, v___f_906_);
return v___x_909_;
}
case 1:
{
lean_object* v_toBind_910_; lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref_known(v_info_846_, 1);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_888_);
v_toBind_910_ = lean_ctor_get(v_inst_845_, 1);
lean_inc_ref(v_inst_845_);
lean_inc_ref(v_inst_844_);
lean_inc(v_toBind_910_);
v___f_911_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13), 7, 6);
lean_closure_set(v___f_911_, 0, v_resTy_847_);
lean_closure_set(v___f_911_, 1, v_k_848_);
lean_closure_set(v___f_911_, 2, v_inst_843_);
lean_closure_set(v___f_911_, 3, v_toBind_910_);
lean_closure_set(v___f_911_, 4, v_inst_844_);
lean_closure_set(v___f_911_, 5, v_inst_845_);
v___x_912_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_913_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_914_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_844_, v_inst_845_, v___x_912_, v___x_913_, v___f_911_);
return v___x_914_;
}
case 2:
{
lean_object* v_toBind_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___f_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec_ref_known(v_info_846_, 1);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_888_);
v_toBind_915_ = lean_ctor_get(v_inst_845_, 1);
v___x_916_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_917_ = lean_box(0);
lean_inc_ref(v_inst_845_);
lean_inc_ref(v_inst_844_);
lean_inc(v_toBind_915_);
v___f_918_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17), 8, 7);
lean_closure_set(v___f_918_, 0, v___x_917_);
lean_closure_set(v___f_918_, 1, v_resTy_847_);
lean_closure_set(v___f_918_, 2, v_k_848_);
lean_closure_set(v___f_918_, 3, v_inst_843_);
lean_closure_set(v___f_918_, 4, v_toBind_915_);
lean_closure_set(v___f_918_, 5, v_inst_844_);
lean_closure_set(v___f_918_, 6, v_inst_845_);
v___x_919_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12);
v___x_920_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_844_, v_inst_845_, v___x_916_, v___x_919_, v___f_918_);
return v___x_920_;
}
default: 
{
lean_object* v_toApplicative_921_; lean_object* v_matcherApp_922_; lean_object* v_toBind_923_; lean_object* v_toPure_924_; lean_object* v_toMatcherInfo_925_; lean_object* v_matcherName_926_; lean_object* v_matcherLevels_927_; lean_object* v_params_928_; lean_object* v_motive_929_; lean_object* v_discrs_930_; lean_object* v_alts_931_; lean_object* v___f_932_; lean_object* v___f_933_; lean_object* v___x_934_; lean_object* v___f_935_; lean_object* v___f_936_; lean_object* v___x_937_; size_t v_sz_938_; size_t v___x_939_; lean_object* v_discrDecls_940_; uint8_t v___x_941_; lean_object* v___x_942_; 
v_toApplicative_921_ = lean_ctor_get(v_inst_845_, 0);
v_matcherApp_922_ = lean_ctor_get(v_info_846_, 0);
lean_inc_ref(v_matcherApp_922_);
lean_dec_ref_known(v_info_846_, 1);
v_toBind_923_ = lean_ctor_get(v_inst_845_, 1);
v_toPure_924_ = lean_ctor_get(v_toApplicative_921_, 1);
v_toMatcherInfo_925_ = lean_ctor_get(v_matcherApp_922_, 0);
lean_inc_ref(v_toMatcherInfo_925_);
v_matcherName_926_ = lean_ctor_get(v_matcherApp_922_, 1);
lean_inc(v_matcherName_926_);
v_matcherLevels_927_ = lean_ctor_get(v_matcherApp_922_, 2);
lean_inc_ref(v_matcherLevels_927_);
v_params_928_ = lean_ctor_get(v_matcherApp_922_, 3);
lean_inc_ref(v_params_928_);
v_motive_929_ = lean_ctor_get(v_matcherApp_922_, 4);
lean_inc_ref(v_motive_929_);
v_discrs_930_ = lean_ctor_get(v_matcherApp_922_, 5);
lean_inc_ref_n(v_discrs_930_, 3);
v_alts_931_ = lean_ctor_get(v_matcherApp_922_, 6);
lean_inc_ref(v_alts_931_);
lean_dec_ref(v_matcherApp_922_);
lean_inc_ref(v_resTy_847_);
v___f_932_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed), 8, 1);
lean_closure_set(v___f_932_, 0, v_resTy_847_);
v___f_933_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__13));
v___x_934_ = l_Lean_instInhabitedExpr;
lean_inc(v_inst_843_);
v___f_935_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23), 6, 3);
lean_closure_set(v___f_935_, 0, v___x_934_);
lean_closure_set(v___f_935_, 1, v_discrs_930_);
lean_closure_set(v___f_935_, 2, v_inst_843_);
lean_inc(v_toPure_924_);
lean_inc_ref(v_inst_845_);
lean_inc_ref(v_inst_844_);
lean_inc(v_toBind_923_);
v___f_936_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_936_, 0, v_toMatcherInfo_925_);
lean_closure_set(v___f_936_, 1, v_matcherName_926_);
lean_closure_set(v___f_936_, 2, v_params_928_);
lean_closure_set(v___f_936_, 3, v_k_848_);
lean_closure_set(v___f_936_, 4, v___x_888_);
lean_closure_set(v___f_936_, 5, v_inst_843_);
lean_closure_set(v___f_936_, 6, v_toBind_923_);
lean_closure_set(v___f_936_, 7, v___f_933_);
lean_closure_set(v___f_936_, 8, v_inst_844_);
lean_closure_set(v___f_936_, 9, v_inst_845_);
lean_closure_set(v___f_936_, 10, v_alts_931_);
lean_closure_set(v___f_936_, 11, v_toPure_924_);
lean_closure_set(v___f_936_, 12, v_matcherLevels_927_);
lean_closure_set(v___f_936_, 13, v_resTy_847_);
lean_closure_set(v___f_936_, 14, v___x_904_);
lean_closure_set(v___f_936_, 15, v_motive_929_);
lean_closure_set(v___f_936_, 16, v___f_932_);
v___x_937_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_938_ = lean_array_size(v_discrs_930_);
v___x_939_ = ((size_t)0ULL);
v_discrDecls_940_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_937_, v_discrs_930_, v___f_935_, v_sz_938_, v___x_939_, v_discrs_930_);
lean_dec_ref(v_discrs_930_);
v___x_941_ = 0;
v___x_942_ = l_Lean_Meta_withLocalDeclsD___redArg(v_inst_844_, v_inst_845_, v_discrDecls_940_, v___f_936_, v___x_941_);
return v___x_942_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object* v_n_949_, lean_object* v_00_u03b1_950_, lean_object* v_inst_951_, lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_info_955_, lean_object* v_resTy_956_, lean_object* v_k_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(v_inst_951_, v_inst_952_, v_inst_953_, v_info_955_, v_resTy_956_, v_k_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object* v_n_959_, lean_object* v_00_u03b1_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_info_965_, lean_object* v_resTy_966_, lean_object* v_k_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(v_n_959_, v_00_u03b1_960_, v_inst_961_, v_inst_962_, v_inst_963_, v_inst_964_, v_info_965_, v_resTy_966_, v_k_967_);
lean_dec(v_inst_964_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object* v_u_969_, lean_object* v_resTy_970_, lean_object* v_c_971_, lean_object* v_h_972_, lean_object* v_t_973_, lean_object* v_toPure_974_, lean_object* v_e_975_){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_976_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_977_ = lean_box(0);
v___x_978_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_978_, 0, v_u_969_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = l_Lean_mkConst(v___x_976_, v___x_978_);
v___x_980_ = l_Lean_mkApp5(v___x_979_, v_resTy_970_, v_c_971_, v_h_972_, v_t_973_, v_e_975_);
v___x_981_ = lean_apply_2(v_toPure_974_, lean_box(0), v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object* v_u_985_, lean_object* v_resTy_986_, lean_object* v_c_987_, lean_object* v_h_988_, lean_object* v_toPure_989_, lean_object* v_onAlt_990_, lean_object* v___x_991_, lean_object* v___x_992_, lean_object* v_toBind_993_, lean_object* v_t_994_){
_start:
{
lean_object* v___f_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_inc_ref(v_resTy_986_);
v___f_995_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0), 7, 6);
lean_closure_set(v___f_995_, 0, v_u_985_);
lean_closure_set(v___f_995_, 1, v_resTy_986_);
lean_closure_set(v___f_995_, 2, v_c_987_);
lean_closure_set(v___f_995_, 3, v_h_988_);
lean_closure_set(v___f_995_, 4, v_t_994_);
lean_closure_set(v___f_995_, 5, v_toPure_989_);
v___x_996_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_997_ = lean_apply_4(v_onAlt_990_, v___x_996_, v_resTy_986_, v___x_991_, v___x_992_);
v___x_998_ = lean_apply_4(v_toBind_993_, lean_box(0), lean_box(0), v___x_997_, v___f_995_);
return v___x_998_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object* v___x_999_, uint8_t v_useSplitter_1000_, lean_object* v_inst_1001_, lean_object* v_____do__lift_1002_){
_start:
{
uint8_t v___x_1003_; uint8_t v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1003_ = 0;
v___x_1004_ = 1;
v___x_1005_ = lean_box(v___x_1003_);
v___x_1006_ = lean_box(v_useSplitter_1000_);
v___x_1007_ = lean_box(v___x_1003_);
v___x_1008_ = lean_box(v_useSplitter_1000_);
v___x_1009_ = lean_box(v___x_1004_);
v___x_1010_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1010_, 0, v___x_999_);
lean_closure_set(v___x_1010_, 1, v_____do__lift_1002_);
lean_closure_set(v___x_1010_, 2, v___x_1005_);
lean_closure_set(v___x_1010_, 3, v___x_1006_);
lean_closure_set(v___x_1010_, 4, v___x_1007_);
lean_closure_set(v___x_1010_, 5, v___x_1008_);
lean_closure_set(v___x_1010_, 6, v___x_1009_);
v___x_1011_ = lean_apply_2(v_inst_1001_, lean_box(0), v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_999_ = stack[0].m_obj;
uint8_t v_useSplitter_1000_ = stack[1].m_num;
lean_object* v_inst_1001_ = stack[2].m_obj;
lean_object* v_____do__lift_1002_ = stack[3].m_obj;
lean_object* v_res_1012_;
v_res_1012_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(v___x_999_, v_useSplitter_1000_, v_inst_1001_, v_____do__lift_1002_);
stack->m_obj
 = v_res_1012_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object* v___x_1013_, lean_object* v_useSplitter_1014_, lean_object* v_inst_1015_, lean_object* v_____do__lift_1016_){
_start:
{
uint8_t v_useSplitter_boxed_1017_; lean_object* v_res_1018_; 
v_useSplitter_boxed_1017_ = lean_unbox(v_useSplitter_1014_);
v_res_1018_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(v___x_1013_, v_useSplitter_boxed_1017_, v_inst_1015_, v_____do__lift_1016_);
return v_res_1018_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object* v___x_1022_, uint8_t v_useSplitter_1023_, lean_object* v_inst_1024_, lean_object* v_onAlt_1025_, lean_object* v_resTy_1026_, lean_object* v_toBind_1027_, lean_object* v_h_1028_){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1029_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1032_ = lean_mk_empty_array_with_capacity(v___x_1022_);
v___x_1033_ = lean_array_push(v___x_1032_, v_h_1028_);
v___x_1034_ = lean_box(v_useSplitter_1023_);
lean_inc_ref(v___x_1033_);
v___f_1035_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1035_, 0, v___x_1033_);
lean_closure_set(v___f_1035_, 1, v___x_1034_);
lean_closure_set(v___f_1035_, 2, v_inst_1024_);
v___x_1036_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1031_);
lean_ctor_set(v___x_1036_, 1, v___x_1033_);
lean_ctor_set(v___x_1036_, 2, v___x_1031_);
lean_ctor_set(v___x_1036_, 3, v___x_1031_);
lean_ctor_set(v___x_1036_, 4, v___x_1031_);
v___x_1037_ = lean_apply_4(v_onAlt_1025_, v___x_1029_, v_resTy_1026_, v___x_1030_, v___x_1036_);
v___x_1038_ = lean_apply_4(v_toBind_1027_, lean_box(0), lean_box(0), v___x_1037_, v___f_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1022_ = stack[0].m_obj;
uint8_t v_useSplitter_1023_ = stack[1].m_num;
lean_object* v_inst_1024_ = stack[2].m_obj;
lean_object* v_onAlt_1025_ = stack[3].m_obj;
lean_object* v_resTy_1026_ = stack[4].m_obj;
lean_object* v_toBind_1027_ = stack[5].m_obj;
lean_object* v_h_1028_ = stack[6].m_obj;
lean_object* v_res_1039_;
v_res_1039_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(v___x_1022_, v_useSplitter_1023_, v_inst_1024_, v_onAlt_1025_, v_resTy_1026_, v_toBind_1027_, v_h_1028_);
stack->m_obj
 = v_res_1039_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object* v___x_1040_, lean_object* v_useSplitter_1041_, lean_object* v_inst_1042_, lean_object* v_onAlt_1043_, lean_object* v_resTy_1044_, lean_object* v_toBind_1045_, lean_object* v_h_1046_){
_start:
{
uint8_t v_useSplitter_boxed_1047_; lean_object* v_res_1048_; 
v_useSplitter_boxed_1047_ = lean_unbox(v_useSplitter_1041_);
v_res_1048_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(v___x_1040_, v_useSplitter_boxed_1047_, v_inst_1042_, v_onAlt_1043_, v_resTy_1044_, v_toBind_1045_, v_h_1046_);
lean_dec(v___x_1040_);
return v_res_1048_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object* v___x_1049_, uint8_t v_useSplitter_1050_, lean_object* v_inst_1051_, lean_object* v_onAlt_1052_, lean_object* v_resTy_1053_, lean_object* v_toBind_1054_, lean_object* v_h_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1056_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1057_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1058_ = lean_mk_empty_array_with_capacity(v___x_1049_);
v___x_1059_ = lean_array_push(v___x_1058_, v_h_1055_);
v___x_1060_ = lean_box(v_useSplitter_1050_);
lean_inc_ref(v___x_1059_);
v___f_1061_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1061_, 0, v___x_1059_);
lean_closure_set(v___f_1061_, 1, v___x_1060_);
lean_closure_set(v___f_1061_, 2, v_inst_1051_);
v___x_1062_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1057_);
lean_ctor_set(v___x_1062_, 1, v___x_1059_);
lean_ctor_set(v___x_1062_, 2, v___x_1057_);
lean_ctor_set(v___x_1062_, 3, v___x_1057_);
lean_ctor_set(v___x_1062_, 4, v___x_1057_);
v___x_1063_ = lean_apply_4(v_onAlt_1052_, v___x_1056_, v_resTy_1053_, v___x_1049_, v___x_1062_);
v___x_1064_ = lean_apply_4(v_toBind_1054_, lean_box(0), lean_box(0), v___x_1063_, v___f_1061_);
return v___x_1064_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1049_ = stack[0].m_obj;
uint8_t v_useSplitter_1050_ = stack[1].m_num;
lean_object* v_inst_1051_ = stack[2].m_obj;
lean_object* v_onAlt_1052_ = stack[3].m_obj;
lean_object* v_resTy_1053_ = stack[4].m_obj;
lean_object* v_toBind_1054_ = stack[5].m_obj;
lean_object* v_h_1055_ = stack[6].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(v___x_1049_, v_useSplitter_1050_, v_inst_1051_, v_onAlt_1052_, v_resTy_1053_, v_toBind_1054_, v_h_1055_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object* v___x_1066_, lean_object* v_useSplitter_1067_, lean_object* v_inst_1068_, lean_object* v_onAlt_1069_, lean_object* v_resTy_1070_, lean_object* v_toBind_1071_, lean_object* v_h_1072_){
_start:
{
uint8_t v_useSplitter_boxed_1073_; lean_object* v_res_1074_; 
v_useSplitter_boxed_1073_ = lean_unbox(v_useSplitter_1067_);
v_res_1074_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(v___x_1066_, v_useSplitter_boxed_1073_, v_inst_1068_, v_onAlt_1069_, v_resTy_1070_, v_toBind_1071_, v_h_1072_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object* v_u_1075_, lean_object* v_resTy_1076_, lean_object* v_c_1077_, lean_object* v_h_1078_, lean_object* v_t_1079_, lean_object* v_toPure_1080_, lean_object* v_e_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1082_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_u_1075_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_mkConst(v___x_1082_, v___x_1084_);
v___x_1086_ = l_Lean_mkApp5(v___x_1085_, v_resTy_1076_, v_c_1077_, v_h_1078_, v_t_1079_, v_e_1081_);
v___x_1087_ = lean_apply_2(v_toPure_1080_, lean_box(0), v___x_1086_);
return v___x_1087_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object* v_u_1088_, lean_object* v_resTy_1089_, lean_object* v_c_1090_, lean_object* v_h_1091_, lean_object* v_toPure_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_n_1095_, uint8_t v___x_1096_, lean_object* v___f_1097_, uint8_t v___x_1098_, lean_object* v_toBind_1099_, lean_object* v_t_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
lean_inc_ref(v_c_1090_);
v___f_1101_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1101_, 0, v_u_1088_);
lean_closure_set(v___f_1101_, 1, v_resTy_1089_);
lean_closure_set(v___f_1101_, 2, v_c_1090_);
lean_closure_set(v___f_1101_, 3, v_h_1091_);
lean_closure_set(v___f_1101_, 4, v_t_1100_);
lean_closure_set(v___f_1101_, 5, v_toPure_1092_);
v___x_1102_ = l_Lean_mkNot(v_c_1090_);
v___x_1103_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1093_, v_inst_1094_, v_n_1095_, v___x_1096_, v___x_1102_, v___f_1097_, v___x_1098_);
v___x_1104_ = lean_apply_4(v_toBind_1099_, lean_box(0), lean_box(0), v___x_1103_, v___f_1101_);
return v___x_1104_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_u_1088_ = stack[0].m_obj;
lean_object* v_resTy_1089_ = stack[1].m_obj;
lean_object* v_c_1090_ = stack[2].m_obj;
lean_object* v_h_1091_ = stack[3].m_obj;
lean_object* v_toPure_1092_ = stack[4].m_obj;
lean_object* v_inst_1093_ = stack[5].m_obj;
lean_object* v_inst_1094_ = stack[6].m_obj;
lean_object* v_n_1095_ = stack[7].m_obj;
uint8_t v___x_1096_ = stack[8].m_num;
lean_object* v___f_1097_ = stack[9].m_obj;
uint8_t v___x_1098_ = stack[10].m_num;
lean_object* v_toBind_1099_ = stack[11].m_obj;
lean_object* v_t_1100_ = stack[12].m_obj;
lean_object* v_res_1105_;
v_res_1105_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(v_u_1088_, v_resTy_1089_, v_c_1090_, v_h_1091_, v_toPure_1092_, v_inst_1093_, v_inst_1094_, v_n_1095_, v___x_1096_, v___f_1097_, v___x_1098_, v_toBind_1099_, v_t_1100_);
stack->m_obj
 = v_res_1105_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object* v_u_1106_, lean_object* v_resTy_1107_, lean_object* v_c_1108_, lean_object* v_h_1109_, lean_object* v_toPure_1110_, lean_object* v_inst_1111_, lean_object* v_inst_1112_, lean_object* v_n_1113_, lean_object* v___x_1114_, lean_object* v___f_1115_, lean_object* v___x_1116_, lean_object* v_toBind_1117_, lean_object* v_t_1118_){
_start:
{
uint8_t v___x_1734__boxed_1119_; uint8_t v___x_1736__boxed_1120_; lean_object* v_res_1121_; 
v___x_1734__boxed_1119_ = lean_unbox(v___x_1114_);
v___x_1736__boxed_1120_ = lean_unbox(v___x_1116_);
v_res_1121_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(v_u_1106_, v_resTy_1107_, v_c_1108_, v_h_1109_, v_toPure_1110_, v_inst_1111_, v_inst_1112_, v_n_1113_, v___x_1734__boxed_1119_, v___f_1115_, v___x_1736__boxed_1120_, v_toBind_1117_, v_t_1118_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object* v_u_1122_, lean_object* v_resTy_1123_, lean_object* v_c_1124_, lean_object* v_h_1125_, lean_object* v_toPure_1126_, lean_object* v_inst_1127_, lean_object* v_inst_1128_, lean_object* v___f_1129_, lean_object* v_toBind_1130_, lean_object* v___f_1131_, lean_object* v_n_1132_){
_start:
{
uint8_t v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___f_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1133_ = 0;
v___x_1134_ = 0;
v___x_1135_ = lean_box(v___x_1133_);
v___x_1136_ = lean_box(v___x_1134_);
lean_inc(v_toBind_1130_);
lean_inc(v_n_1132_);
lean_inc_ref(v_inst_1128_);
lean_inc_ref(v_inst_1127_);
lean_inc_ref(v_c_1124_);
v___f_1137_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1137_, 0, v_u_1122_);
lean_closure_set(v___f_1137_, 1, v_resTy_1123_);
lean_closure_set(v___f_1137_, 2, v_c_1124_);
lean_closure_set(v___f_1137_, 3, v_h_1125_);
lean_closure_set(v___f_1137_, 4, v_toPure_1126_);
lean_closure_set(v___f_1137_, 5, v_inst_1127_);
lean_closure_set(v___f_1137_, 6, v_inst_1128_);
lean_closure_set(v___f_1137_, 7, v_n_1132_);
lean_closure_set(v___f_1137_, 8, v___x_1135_);
lean_closure_set(v___f_1137_, 9, v___f_1129_);
lean_closure_set(v___f_1137_, 10, v___x_1136_);
lean_closure_set(v___f_1137_, 11, v_toBind_1130_);
v___x_1138_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1127_, v_inst_1128_, v_n_1132_, v___x_1133_, v_c_1124_, v___f_1131_, v___x_1134_);
v___x_1139_ = lean_apply_4(v_toBind_1130_, lean_box(0), lean_box(0), v___x_1138_, v___f_1137_);
return v___x_1139_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object* v___x_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = l_Lean_Core_mkFreshUserName(v___x_1140_, v___y_1143_, v___y_1144_);
return v___x_1146_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1140_ = stack[0].m_obj;
lean_object* v___y_1141_ = stack[1].m_obj;
lean_object* v___y_1142_ = stack[2].m_obj;
lean_object* v___y_1143_ = stack[3].m_obj;
lean_object* v___y_1144_ = stack[4].m_obj;
lean_object* v_res_1147_;
v_res_1147_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(v___x_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_);
stack->m_obj
 = v_res_1147_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object* v___x_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
lean_object* v_res_1154_; 
v_res_1154_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(v___x_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v___y_1150_);
lean_dec_ref(v___y_1149_);
return v_res_1154_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object* v_e_1162_, uint8_t v_useSplitter_1163_, lean_object* v_resTy_1164_, lean_object* v_toPure_1165_, lean_object* v_onAlt_1166_, lean_object* v_toBind_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_u_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v_c_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_h_1180_; 
v___x_1172_ = lean_unsigned_to_nat(1u);
v___x_1173_ = l_Lean_Expr_getAppNumArgs(v_e_1162_);
v___x_1174_ = lean_nat_sub(v___x_1173_, v___x_1172_);
v___x_1175_ = lean_nat_sub(v___x_1174_, v___x_1172_);
lean_dec(v___x_1174_);
v_c_1176_ = l_Lean_Expr_getRevArg_x21(v_e_1162_, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(2u);
v___x_1178_ = lean_nat_sub(v___x_1173_, v___x_1177_);
lean_dec(v___x_1173_);
v___x_1179_ = lean_nat_sub(v___x_1178_, v___x_1172_);
lean_dec(v___x_1178_);
v_h_1180_ = l_Lean_Expr_getRevArg_x21(v_e_1162_, v___x_1179_);
if (v_useSplitter_1163_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___f_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
lean_dec_ref(v_inst_1170_);
lean_dec_ref(v_inst_1169_);
lean_dec(v_inst_1168_);
v___x_1181_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1167_);
lean_inc(v_onAlt_1166_);
lean_inc_ref(v_resTy_1164_);
v___f_1184_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1184_, 0, v_u_1171_);
lean_closure_set(v___f_1184_, 1, v_resTy_1164_);
lean_closure_set(v___f_1184_, 2, v_c_1176_);
lean_closure_set(v___f_1184_, 3, v_h_1180_);
lean_closure_set(v___f_1184_, 4, v_toPure_1165_);
lean_closure_set(v___f_1184_, 5, v_onAlt_1166_);
lean_closure_set(v___f_1184_, 6, v___x_1172_);
lean_closure_set(v___f_1184_, 7, v___x_1183_);
lean_closure_set(v___f_1184_, 8, v_toBind_1167_);
v___x_1185_ = lean_apply_4(v_onAlt_1166_, v___x_1181_, v_resTy_1164_, v___x_1182_, v___x_1183_);
v___x_1186_ = lean_apply_4(v_toBind_1167_, lean_box(0), lean_box(0), v___x_1185_, v___f_1184_);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; lean_object* v___f_1188_; lean_object* v___x_1189_; lean_object* v___f_1190_; lean_object* v___f_1191_; lean_object* v___f_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1187_ = lean_box(v_useSplitter_1163_);
lean_inc_n(v_toBind_1167_, 3);
lean_inc_ref_n(v_resTy_1164_, 2);
lean_inc(v_onAlt_1166_);
lean_inc_n(v_inst_1168_, 2);
v___f_1188_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1188_, 0, v___x_1172_);
lean_closure_set(v___f_1188_, 1, v___x_1187_);
lean_closure_set(v___f_1188_, 2, v_inst_1168_);
lean_closure_set(v___f_1188_, 3, v_onAlt_1166_);
lean_closure_set(v___f_1188_, 4, v_resTy_1164_);
lean_closure_set(v___f_1188_, 5, v_toBind_1167_);
v___x_1189_ = lean_box(v_useSplitter_1163_);
v___f_1190_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1190_, 0, v___x_1172_);
lean_closure_set(v___f_1190_, 1, v___x_1189_);
lean_closure_set(v___f_1190_, 2, v_inst_1168_);
lean_closure_set(v___f_1190_, 3, v_onAlt_1166_);
lean_closure_set(v___f_1190_, 4, v_resTy_1164_);
lean_closure_set(v___f_1190_, 5, v_toBind_1167_);
v___f_1191_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1191_, 0, v_u_1171_);
lean_closure_set(v___f_1191_, 1, v_resTy_1164_);
lean_closure_set(v___f_1191_, 2, v_c_1176_);
lean_closure_set(v___f_1191_, 3, v_h_1180_);
lean_closure_set(v___f_1191_, 4, v_toPure_1165_);
lean_closure_set(v___f_1191_, 5, v_inst_1169_);
lean_closure_set(v___f_1191_, 6, v_inst_1170_);
lean_closure_set(v___f_1191_, 7, v___f_1190_);
lean_closure_set(v___f_1191_, 8, v_toBind_1167_);
lean_closure_set(v___f_1191_, 9, v___f_1188_);
v___f_1192_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1193_ = lean_apply_2(v_inst_1168_, lean_box(0), v___f_1192_);
v___x_1194_ = lean_apply_4(v_toBind_1167_, lean_box(0), lean_box(0), v___x_1193_, v___f_1191_);
return v___x_1194_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1162_ = stack[0].m_obj;
uint8_t v_useSplitter_1163_ = stack[1].m_num;
lean_object* v_resTy_1164_ = stack[2].m_obj;
lean_object* v_toPure_1165_ = stack[3].m_obj;
lean_object* v_onAlt_1166_ = stack[4].m_obj;
lean_object* v_toBind_1167_ = stack[5].m_obj;
lean_object* v_inst_1168_ = stack[6].m_obj;
lean_object* v_inst_1169_ = stack[7].m_obj;
lean_object* v_inst_1170_ = stack[8].m_obj;
lean_object* v_u_1171_ = stack[9].m_obj;
lean_object* v_res_1195_;
v_res_1195_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(v_e_1162_, v_useSplitter_1163_, v_resTy_1164_, v_toPure_1165_, v_onAlt_1166_, v_toBind_1167_, v_inst_1168_, v_inst_1169_, v_inst_1170_, v_u_1171_);
stack->m_obj
 = v_res_1195_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object* v_e_1196_, lean_object* v_useSplitter_1197_, lean_object* v_resTy_1198_, lean_object* v_toPure_1199_, lean_object* v_onAlt_1200_, lean_object* v_toBind_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_u_1205_){
_start:
{
uint8_t v_useSplitter_boxed_1206_; lean_object* v_res_1207_; 
v_useSplitter_boxed_1206_ = lean_unbox(v_useSplitter_1197_);
v_res_1207_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(v_e_1196_, v_useSplitter_boxed_1206_, v_resTy_1198_, v_toPure_1199_, v_onAlt_1200_, v_toBind_1201_, v_inst_1202_, v_inst_1203_, v_inst_1204_, v_u_1205_);
lean_dec_ref(v_e_1196_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object* v___x_1208_, lean_object* v_inst_1209_, lean_object* v_____do__lift_1210_){
_start:
{
uint8_t v___x_1211_; uint8_t v___x_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1211_ = 0;
v___x_1212_ = 1;
v___x_1213_ = 1;
v___x_1214_ = lean_box(v___x_1211_);
v___x_1215_ = lean_box(v___x_1212_);
v___x_1216_ = lean_box(v___x_1211_);
v___x_1217_ = lean_box(v___x_1212_);
v___x_1218_ = lean_box(v___x_1213_);
v___x_1219_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1219_, 0, v___x_1208_);
lean_closure_set(v___x_1219_, 1, v_____do__lift_1210_);
lean_closure_set(v___x_1219_, 2, v___x_1214_);
lean_closure_set(v___x_1219_, 3, v___x_1215_);
lean_closure_set(v___x_1219_, 4, v___x_1216_);
lean_closure_set(v___x_1219_, 5, v___x_1217_);
lean_closure_set(v___x_1219_, 6, v___x_1218_);
v___x_1220_ = lean_apply_2(v_inst_1209_, lean_box(0), v___x_1219_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object* v_inst_1221_, lean_object* v_onAlt_1222_, lean_object* v_resTy_1223_, lean_object* v_toBind_1224_, lean_object* v_h_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1226_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1227_ = lean_unsigned_to_nat(0u);
v___x_1228_ = lean_unsigned_to_nat(1u);
v___x_1229_ = lean_mk_empty_array_with_capacity(v___x_1228_);
v___x_1230_ = lean_array_push(v___x_1229_, v_h_1225_);
lean_inc_ref_n(v___x_1230_, 2);
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1231_, 0, v___x_1230_);
lean_closure_set(v___f_1231_, 1, v_inst_1221_);
v___x_1232_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1230_);
lean_ctor_set(v___x_1233_, 1, v___x_1230_);
lean_ctor_set(v___x_1233_, 2, v___x_1232_);
lean_ctor_set(v___x_1233_, 3, v___x_1232_);
lean_ctor_set(v___x_1233_, 4, v___x_1232_);
v___x_1234_ = lean_apply_4(v_onAlt_1222_, v___x_1226_, v_resTy_1223_, v___x_1227_, v___x_1233_);
v___x_1235_ = lean_apply_4(v_toBind_1224_, lean_box(0), lean_box(0), v___x_1234_, v___f_1231_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object* v___x_1236_, lean_object* v_inst_1237_, lean_object* v_onAlt_1238_, lean_object* v_resTy_1239_, lean_object* v_toBind_1240_, lean_object* v_h_1241_){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___f_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1242_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1243_ = lean_mk_empty_array_with_capacity(v___x_1236_);
v___x_1244_ = lean_array_push(v___x_1243_, v_h_1241_);
lean_inc_ref_n(v___x_1244_, 2);
v___f_1245_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1245_, 0, v___x_1244_);
lean_closure_set(v___f_1245_, 1, v_inst_1237_);
v___x_1246_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1247_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1244_);
lean_ctor_set(v___x_1247_, 1, v___x_1244_);
lean_ctor_set(v___x_1247_, 2, v___x_1246_);
lean_ctor_set(v___x_1247_, 3, v___x_1246_);
lean_ctor_set(v___x_1247_, 4, v___x_1246_);
v___x_1248_ = lean_apply_4(v_onAlt_1238_, v___x_1242_, v_resTy_1239_, v___x_1236_, v___x_1247_);
v___x_1249_ = lean_apply_4(v_toBind_1240_, lean_box(0), lean_box(0), v___x_1248_, v___f_1245_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object* v_inst_1250_, lean_object* v_onAlt_1251_, lean_object* v_resTy_1252_, lean_object* v_toBind_1253_, lean_object* v_e_1254_, lean_object* v_toPure_1255_, lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v___f_1258_, lean_object* v_u_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v_c_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_h_1269_; lean_object* v___f_1270_; lean_object* v___f_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1260_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_toBind_1253_, 2);
lean_inc_ref(v_resTy_1252_);
lean_inc(v_inst_1250_);
v___f_1261_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13), 6, 5);
lean_closure_set(v___f_1261_, 0, v___x_1260_);
lean_closure_set(v___f_1261_, 1, v_inst_1250_);
lean_closure_set(v___f_1261_, 2, v_onAlt_1251_);
lean_closure_set(v___f_1261_, 3, v_resTy_1252_);
lean_closure_set(v___f_1261_, 4, v_toBind_1253_);
v___x_1262_ = l_Lean_Expr_getAppNumArgs(v_e_1254_);
v___x_1263_ = lean_nat_sub(v___x_1262_, v___x_1260_);
v___x_1264_ = lean_nat_sub(v___x_1263_, v___x_1260_);
lean_dec(v___x_1263_);
v_c_1265_ = l_Lean_Expr_getRevArg_x21(v_e_1254_, v___x_1264_);
v___x_1266_ = lean_unsigned_to_nat(2u);
v___x_1267_ = lean_nat_sub(v___x_1262_, v___x_1266_);
lean_dec(v___x_1262_);
v___x_1268_ = lean_nat_sub(v___x_1267_, v___x_1260_);
lean_dec(v___x_1267_);
v_h_1269_ = l_Lean_Expr_getRevArg_x21(v_e_1254_, v___x_1268_);
v___f_1270_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1270_, 0, v_u_1259_);
lean_closure_set(v___f_1270_, 1, v_resTy_1252_);
lean_closure_set(v___f_1270_, 2, v_c_1265_);
lean_closure_set(v___f_1270_, 3, v_h_1269_);
lean_closure_set(v___f_1270_, 4, v_toPure_1255_);
lean_closure_set(v___f_1270_, 5, v_inst_1256_);
lean_closure_set(v___f_1270_, 6, v_inst_1257_);
lean_closure_set(v___f_1270_, 7, v___f_1261_);
lean_closure_set(v___f_1270_, 8, v_toBind_1253_);
lean_closure_set(v___f_1270_, 9, v___f_1258_);
v___f_1271_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1272_ = lean_apply_2(v_inst_1250_, lean_box(0), v___f_1271_);
v___x_1273_ = lean_apply_4(v_toBind_1253_, lean_box(0), lean_box(0), v___x_1272_, v___f_1270_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object* v_inst_1274_, lean_object* v_onAlt_1275_, lean_object* v_resTy_1276_, lean_object* v_toBind_1277_, lean_object* v_e_1278_, lean_object* v_toPure_1279_, lean_object* v_inst_1280_, lean_object* v_inst_1281_, lean_object* v___f_1282_, lean_object* v_u_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(v_inst_1274_, v_onAlt_1275_, v_resTy_1276_, v_toBind_1277_, v_e_1278_, v_toPure_1279_, v_inst_1280_, v_inst_1281_, v___f_1282_, v_u_1283_);
lean_dec_ref(v_e_1278_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object* v_u_1285_, lean_object* v_resTy_1286_, lean_object* v_c_1287_, lean_object* v_t_1288_, lean_object* v_toPure_1289_, lean_object* v_e_1290_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1291_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_1292_ = lean_box(0);
v___x_1293_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1293_, 0, v_u_1285_);
lean_ctor_set(v___x_1293_, 1, v___x_1292_);
v___x_1294_ = l_Lean_mkConst(v___x_1291_, v___x_1293_);
v___x_1295_ = l_Lean_mkApp4(v___x_1294_, v_resTy_1286_, v_c_1287_, v_t_1288_, v_e_1290_);
v___x_1296_ = lean_apply_2(v_toPure_1289_, lean_box(0), v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object* v_u_1297_, lean_object* v_resTy_1298_, lean_object* v_c_1299_, lean_object* v_toPure_1300_, lean_object* v_onAlt_1301_, lean_object* v___x_1302_, lean_object* v___x_1303_, lean_object* v_toBind_1304_, lean_object* v_t_1305_){
_start:
{
lean_object* v___f_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
lean_inc_ref(v_resTy_1298_);
v___f_1306_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12), 6, 5);
lean_closure_set(v___f_1306_, 0, v_u_1297_);
lean_closure_set(v___f_1306_, 1, v_resTy_1298_);
lean_closure_set(v___f_1306_, 2, v_c_1299_);
lean_closure_set(v___f_1306_, 3, v_t_1305_);
lean_closure_set(v___f_1306_, 4, v_toPure_1300_);
v___x_1307_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1308_ = lean_apply_4(v_onAlt_1301_, v___x_1307_, v_resTy_1298_, v___x_1302_, v___x_1303_);
v___x_1309_ = lean_apply_4(v_toBind_1304_, lean_box(0), lean_box(0), v___x_1308_, v___f_1306_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20(lean_object* v___x_1311_, lean_object* v_u_1312_, lean_object* v___x_1313_, lean_object* v_resTy_1314_, lean_object* v_c_1315_, lean_object* v_t_1316_, lean_object* v_toPure_1317_, lean_object* v_e_1318_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1319_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20___closed__0));
v___x_1320_ = l_Lean_Name_mkStr2(v___x_1311_, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_u_1312_);
lean_ctor_set(v___x_1321_, 1, v___x_1313_);
v___x_1322_ = l_Lean_mkConst(v___x_1320_, v___x_1321_);
v___x_1323_ = l_Lean_mkApp4(v___x_1322_, v_resTy_1314_, v_c_1315_, v_t_1316_, v_e_1318_);
v___x_1324_ = lean_apply_2(v_toPure_1317_, lean_box(0), v___x_1323_);
return v___x_1324_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object* v___x_1325_, lean_object* v_u_1326_, lean_object* v___x_1327_, lean_object* v_resTy_1328_, lean_object* v_c_1329_, lean_object* v_toPure_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_n_1333_, uint8_t v___x_1334_, lean_object* v_hFalse_1335_, lean_object* v___f_1336_, uint8_t v___x_1337_, lean_object* v_toBind_1338_, lean_object* v_t_1339_){
_start:
{
lean_object* v___f_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___f_1340_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20), 8, 7);
lean_closure_set(v___f_1340_, 0, v___x_1325_);
lean_closure_set(v___f_1340_, 1, v_u_1326_);
lean_closure_set(v___f_1340_, 2, v___x_1327_);
lean_closure_set(v___f_1340_, 3, v_resTy_1328_);
lean_closure_set(v___f_1340_, 4, v_c_1329_);
lean_closure_set(v___f_1340_, 5, v_t_1339_);
lean_closure_set(v___f_1340_, 6, v_toPure_1330_);
v___x_1341_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1331_, v_inst_1332_, v_n_1333_, v___x_1334_, v_hFalse_1335_, v___f_1336_, v___x_1337_);
v___x_1342_ = lean_apply_4(v_toBind_1338_, lean_box(0), lean_box(0), v___x_1341_, v___f_1340_);
return v___x_1342_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1325_ = stack[0].m_obj;
lean_object* v_u_1326_ = stack[1].m_obj;
lean_object* v___x_1327_ = stack[2].m_obj;
lean_object* v_resTy_1328_ = stack[3].m_obj;
lean_object* v_c_1329_ = stack[4].m_obj;
lean_object* v_toPure_1330_ = stack[5].m_obj;
lean_object* v_inst_1331_ = stack[6].m_obj;
lean_object* v_inst_1332_ = stack[7].m_obj;
lean_object* v_n_1333_ = stack[8].m_obj;
uint8_t v___x_1334_ = stack[9].m_num;
lean_object* v_hFalse_1335_ = stack[10].m_obj;
lean_object* v___f_1336_ = stack[11].m_obj;
uint8_t v___x_1337_ = stack[12].m_num;
lean_object* v_toBind_1338_ = stack[13].m_obj;
lean_object* v_t_1339_ = stack[14].m_obj;
lean_object* v_res_1343_;
v_res_1343_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(v___x_1325_, v_u_1326_, v___x_1327_, v_resTy_1328_, v_c_1329_, v_toPure_1330_, v_inst_1331_, v_inst_1332_, v_n_1333_, v___x_1334_, v_hFalse_1335_, v___f_1336_, v___x_1337_, v_toBind_1338_, v_t_1339_);
stack->m_obj
 = v_res_1343_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object* v___x_1344_, lean_object* v_u_1345_, lean_object* v___x_1346_, lean_object* v_resTy_1347_, lean_object* v_c_1348_, lean_object* v_toPure_1349_, lean_object* v_inst_1350_, lean_object* v_inst_1351_, lean_object* v_n_1352_, lean_object* v___x_1353_, lean_object* v_hFalse_1354_, lean_object* v___f_1355_, lean_object* v___x_1356_, lean_object* v_toBind_1357_, lean_object* v_t_1358_){
_start:
{
uint8_t v___x_2218__boxed_1359_; uint8_t v___x_2220__boxed_1360_; lean_object* v_res_1361_; 
v___x_2218__boxed_1359_ = lean_unbox(v___x_1353_);
v___x_2220__boxed_1360_ = lean_unbox(v___x_1356_);
v_res_1361_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(v___x_1344_, v_u_1345_, v___x_1346_, v_resTy_1347_, v_c_1348_, v_toPure_1349_, v_inst_1350_, v_inst_1351_, v_n_1352_, v___x_2218__boxed_1359_, v_hFalse_1354_, v___f_1355_, v___x_2220__boxed_1360_, v_toBind_1357_, v_t_1358_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16(lean_object* v___x_1362_, lean_object* v_u_1363_, lean_object* v___x_1364_, lean_object* v_resTy_1365_, lean_object* v_c_1366_, lean_object* v_toPure_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_n_1370_, lean_object* v___f_1371_, lean_object* v_toBind_1372_, lean_object* v_hTrue_1373_, lean_object* v___f_1374_, lean_object* v_hFalse_1375_){
_start:
{
uint8_t v___x_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___f_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1376_ = 0;
v___x_1377_ = 0;
v___x_1378_ = lean_box(v___x_1376_);
v___x_1379_ = lean_box(v___x_1377_);
lean_inc(v_toBind_1372_);
lean_inc(v_n_1370_);
lean_inc_ref(v_inst_1369_);
lean_inc_ref(v_inst_1368_);
v___f_1380_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed), 15, 14);
lean_closure_set(v___f_1380_, 0, v___x_1362_);
lean_closure_set(v___f_1380_, 1, v_u_1363_);
lean_closure_set(v___f_1380_, 2, v___x_1364_);
lean_closure_set(v___f_1380_, 3, v_resTy_1365_);
lean_closure_set(v___f_1380_, 4, v_c_1366_);
lean_closure_set(v___f_1380_, 5, v_toPure_1367_);
lean_closure_set(v___f_1380_, 6, v_inst_1368_);
lean_closure_set(v___f_1380_, 7, v_inst_1369_);
lean_closure_set(v___f_1380_, 8, v_n_1370_);
lean_closure_set(v___f_1380_, 9, v___x_1378_);
lean_closure_set(v___f_1380_, 10, v_hFalse_1375_);
lean_closure_set(v___f_1380_, 11, v___f_1371_);
lean_closure_set(v___f_1380_, 12, v___x_1379_);
lean_closure_set(v___f_1380_, 13, v_toBind_1372_);
v___x_1381_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1368_, v_inst_1369_, v_n_1370_, v___x_1376_, v_hTrue_1373_, v___f_1374_, v___x_1377_);
v___x_1382_ = lean_apply_4(v_toBind_1372_, lean_box(0), lean_box(0), v___x_1381_, v___f_1380_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18(lean_object* v___x_1384_, lean_object* v_u_1385_, lean_object* v___x_1386_, lean_object* v_resTy_1387_, lean_object* v_c_1388_, lean_object* v_toPure_1389_, lean_object* v_inst_1390_, lean_object* v_inst_1391_, lean_object* v_n_1392_, lean_object* v___f_1393_, lean_object* v_toBind_1394_, lean_object* v___f_1395_, lean_object* v_inst_1396_, lean_object* v_hTrue_1397_){
_start:
{
lean_object* v___f_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_inc(v_toBind_1394_);
lean_inc_ref(v_c_1388_);
lean_inc(v___x_1386_);
lean_inc_ref(v___x_1384_);
v___f_1398_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16), 14, 13);
lean_closure_set(v___f_1398_, 0, v___x_1384_);
lean_closure_set(v___f_1398_, 1, v_u_1385_);
lean_closure_set(v___f_1398_, 2, v___x_1386_);
lean_closure_set(v___f_1398_, 3, v_resTy_1387_);
lean_closure_set(v___f_1398_, 4, v_c_1388_);
lean_closure_set(v___f_1398_, 5, v_toPure_1389_);
lean_closure_set(v___f_1398_, 6, v_inst_1390_);
lean_closure_set(v___f_1398_, 7, v_inst_1391_);
lean_closure_set(v___f_1398_, 8, v_n_1392_);
lean_closure_set(v___f_1398_, 9, v___f_1393_);
lean_closure_set(v___f_1398_, 10, v_toBind_1394_);
lean_closure_set(v___f_1398_, 11, v_hTrue_1397_);
lean_closure_set(v___f_1398_, 12, v___f_1395_);
v___x_1399_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0));
v___x_1400_ = l_Lean_Name_mkStr2(v___x_1384_, v___x_1399_);
v___x_1401_ = l_Lean_mkConst(v___x_1400_, v___x_1386_);
v___x_1402_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_1402_, 0, v_c_1388_);
lean_closure_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = lean_apply_2(v_inst_1396_, lean_box(0), v___x_1402_);
v___x_1404_ = lean_apply_4(v_toBind_1394_, lean_box(0), lean_box(0), v___x_1403_, v___f_1398_);
return v___x_1404_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2(void){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = lean_box(0);
v___x_1410_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1));
v___x_1411_ = l_Lean_mkConst(v___x_1410_, v___x_1409_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19(lean_object* v_u_1412_, lean_object* v_resTy_1413_, lean_object* v_c_1414_, lean_object* v_toPure_1415_, lean_object* v_inst_1416_, lean_object* v_inst_1417_, lean_object* v___f_1418_, lean_object* v_toBind_1419_, lean_object* v___f_1420_, lean_object* v_inst_1421_, lean_object* v_n_1422_){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1423_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10));
v___x_1424_ = lean_box(0);
lean_inc(v_inst_1421_);
lean_inc(v_toBind_1419_);
lean_inc_ref(v_c_1414_);
v___f_1425_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18), 14, 13);
lean_closure_set(v___f_1425_, 0, v___x_1423_);
lean_closure_set(v___f_1425_, 1, v_u_1412_);
lean_closure_set(v___f_1425_, 2, v___x_1424_);
lean_closure_set(v___f_1425_, 3, v_resTy_1413_);
lean_closure_set(v___f_1425_, 4, v_c_1414_);
lean_closure_set(v___f_1425_, 5, v_toPure_1415_);
lean_closure_set(v___f_1425_, 6, v_inst_1416_);
lean_closure_set(v___f_1425_, 7, v_inst_1417_);
lean_closure_set(v___f_1425_, 8, v_n_1422_);
lean_closure_set(v___f_1425_, 9, v___f_1418_);
lean_closure_set(v___f_1425_, 10, v_toBind_1419_);
lean_closure_set(v___f_1425_, 11, v___f_1420_);
lean_closure_set(v___f_1425_, 12, v_inst_1421_);
v___x_1426_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2, &l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2);
v___x_1427_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_1427_, 0, v_c_1414_);
lean_closure_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = lean_apply_2(v_inst_1421_, lean_box(0), v___x_1427_);
v___x_1429_ = lean_apply_4(v_toBind_1419_, lean_box(0), lean_box(0), v___x_1428_, v___f_1425_);
return v___x_1429_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(lean_object* v_e_1430_, uint8_t v_useSplitter_1431_, lean_object* v_resTy_1432_, lean_object* v_toPure_1433_, lean_object* v_onAlt_1434_, lean_object* v_toBind_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_u_1439_){
_start:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v_c_1444_; 
v___x_1440_ = lean_unsigned_to_nat(1u);
v___x_1441_ = l_Lean_Expr_getAppNumArgs(v_e_1430_);
v___x_1442_ = lean_nat_sub(v___x_1441_, v___x_1440_);
lean_dec(v___x_1441_);
v___x_1443_ = lean_nat_sub(v___x_1442_, v___x_1440_);
lean_dec(v___x_1442_);
v_c_1444_ = l_Lean_Expr_getRevArg_x21(v_e_1430_, v___x_1443_);
if (v_useSplitter_1431_ == 0)
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___f_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
lean_dec_ref(v_inst_1438_);
lean_dec_ref(v_inst_1437_);
lean_dec(v_inst_1436_);
v___x_1445_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1446_ = lean_unsigned_to_nat(0u);
v___x_1447_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1435_);
lean_inc(v_onAlt_1434_);
lean_inc_ref(v_resTy_1432_);
v___f_1448_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14), 9, 8);
lean_closure_set(v___f_1448_, 0, v_u_1439_);
lean_closure_set(v___f_1448_, 1, v_resTy_1432_);
lean_closure_set(v___f_1448_, 2, v_c_1444_);
lean_closure_set(v___f_1448_, 3, v_toPure_1433_);
lean_closure_set(v___f_1448_, 4, v_onAlt_1434_);
lean_closure_set(v___f_1448_, 5, v___x_1440_);
lean_closure_set(v___f_1448_, 6, v___x_1447_);
lean_closure_set(v___f_1448_, 7, v_toBind_1435_);
v___x_1449_ = lean_apply_4(v_onAlt_1434_, v___x_1445_, v_resTy_1432_, v___x_1446_, v___x_1447_);
v___x_1450_ = lean_apply_4(v_toBind_1435_, lean_box(0), lean_box(0), v___x_1449_, v___f_1448_);
return v___x_1450_;
}
else
{
lean_object* v___x_1451_; lean_object* v___f_1452_; lean_object* v___x_1453_; lean_object* v___f_1454_; lean_object* v___f_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1451_ = lean_box(v_useSplitter_1431_);
lean_inc_n(v_toBind_1435_, 3);
lean_inc_ref_n(v_resTy_1432_, 2);
lean_inc(v_onAlt_1434_);
lean_inc_n(v_inst_1436_, 3);
v___f_1452_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1452_, 0, v___x_1440_);
lean_closure_set(v___f_1452_, 1, v___x_1451_);
lean_closure_set(v___f_1452_, 2, v_inst_1436_);
lean_closure_set(v___f_1452_, 3, v_onAlt_1434_);
lean_closure_set(v___f_1452_, 4, v_resTy_1432_);
lean_closure_set(v___f_1452_, 5, v_toBind_1435_);
v___x_1453_ = lean_box(v_useSplitter_1431_);
v___f_1454_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1454_, 0, v___x_1440_);
lean_closure_set(v___f_1454_, 1, v___x_1453_);
lean_closure_set(v___f_1454_, 2, v_inst_1436_);
lean_closure_set(v___f_1454_, 3, v_onAlt_1434_);
lean_closure_set(v___f_1454_, 4, v_resTy_1432_);
lean_closure_set(v___f_1454_, 5, v_toBind_1435_);
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19), 11, 10);
lean_closure_set(v___f_1455_, 0, v_u_1439_);
lean_closure_set(v___f_1455_, 1, v_resTy_1432_);
lean_closure_set(v___f_1455_, 2, v_c_1444_);
lean_closure_set(v___f_1455_, 3, v_toPure_1433_);
lean_closure_set(v___f_1455_, 4, v_inst_1437_);
lean_closure_set(v___f_1455_, 5, v_inst_1438_);
lean_closure_set(v___f_1455_, 6, v___f_1454_);
lean_closure_set(v___f_1455_, 7, v_toBind_1435_);
lean_closure_set(v___f_1455_, 8, v___f_1452_);
lean_closure_set(v___f_1455_, 9, v_inst_1436_);
v___f_1456_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1457_ = lean_apply_2(v_inst_1436_, lean_box(0), v___f_1456_);
v___x_1458_ = lean_apply_4(v_toBind_1435_, lean_box(0), lean_box(0), v___x_1457_, v___f_1455_);
return v___x_1458_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1430_ = stack[0].m_obj;
uint8_t v_useSplitter_1431_ = stack[1].m_num;
lean_object* v_resTy_1432_ = stack[2].m_obj;
lean_object* v_toPure_1433_ = stack[3].m_obj;
lean_object* v_onAlt_1434_ = stack[4].m_obj;
lean_object* v_toBind_1435_ = stack[5].m_obj;
lean_object* v_inst_1436_ = stack[6].m_obj;
lean_object* v_inst_1437_ = stack[7].m_obj;
lean_object* v_inst_1438_ = stack[8].m_obj;
lean_object* v_u_1439_ = stack[9].m_obj;
lean_object* v_res_1459_;
v_res_1459_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(v_e_1430_, v_useSplitter_1431_, v_resTy_1432_, v_toPure_1433_, v_onAlt_1434_, v_toBind_1435_, v_inst_1436_, v_inst_1437_, v_inst_1438_, v_u_1439_);
stack->m_obj
 = v_res_1459_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22___boxed(lean_object* v_e_1460_, lean_object* v_useSplitter_1461_, lean_object* v_resTy_1462_, lean_object* v_toPure_1463_, lean_object* v_onAlt_1464_, lean_object* v_toBind_1465_, lean_object* v_inst_1466_, lean_object* v_inst_1467_, lean_object* v_inst_1468_, lean_object* v_u_1469_){
_start:
{
uint8_t v_useSplitter_boxed_1470_; lean_object* v_res_1471_; 
v_useSplitter_boxed_1470_ = lean_unbox(v_useSplitter_1461_);
v_res_1471_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(v_e_1460_, v_useSplitter_boxed_1470_, v_resTy_1462_, v_toPure_1463_, v_onAlt_1464_, v_toBind_1465_, v_inst_1466_, v_inst_1467_, v_inst_1468_, v_u_1469_);
lean_dec_ref(v_e_1460_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21(lean_object* v_onAlt_1472_, lean_object* v_idx_1473_, lean_object* v_expAltType_1474_, lean_object* v_altFVars_1475_, lean_object* v___alt_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1477_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2));
v___x_1478_ = lean_unsigned_to_nat(1u);
v___x_1479_ = lean_nat_add(v_idx_1473_, v___x_1478_);
v___x_1480_ = lean_name_append_index_after(v___x_1477_, v___x_1479_);
v___x_1481_ = lean_apply_4(v_onAlt_1472_, v___x_1480_, v_expAltType_1474_, v_idx_1473_, v_altFVars_1475_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21___boxed(lean_object* v_onAlt_1482_, lean_object* v_idx_1483_, lean_object* v_expAltType_1484_, lean_object* v_altFVars_1485_, lean_object* v___alt_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21(v_onAlt_1482_, v_idx_1483_, v_expAltType_1484_, v_altFVars_1485_, v___alt_1486_);
lean_dec_ref(v___alt_1486_);
return v_res_1487_;
}
}
uint8_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(lean_object* v_toMatcherInfo_1488_, lean_object* v_i_1489_, lean_object* v_a_1490_, lean_object* v_x_1491_){
_start:
{
uint8_t v___x_1492_; 
v___x_1492_ = l_Lean_Expr_isFVar(v_a_1490_);
if (v___x_1492_ == 0)
{
return v___x_1492_;
}
else
{
lean_object* v_discrInfos_1493_; lean_object* v___x_1494_; uint8_t v___x_1495_; 
v_discrInfos_1493_ = lean_ctor_get(v_toMatcherInfo_1488_, 4);
v___x_1494_ = lean_array_get_size(v_discrInfos_1493_);
v___x_1495_ = lean_nat_dec_lt(v_i_1489_, v___x_1494_);
if (v___x_1495_ == 0)
{
return v___x_1492_;
}
else
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_array_fget_borrowed(v_discrInfos_1493_, v_i_1489_);
if (lean_obj_tag(v___x_1496_) == 0)
{
return v___x_1492_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = 0;
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23_0interp(lean_interpreter_value* stack)
{
lean_object* v_toMatcherInfo_1488_ = stack[0].m_obj;
lean_object* v_i_1489_ = stack[1].m_obj;
lean_object* v_a_1490_ = stack[2].m_obj;
uint8_t v_res_1498_;
v_res_1498_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(v_toMatcherInfo_1488_, v_i_1489_, v_a_1490_, lean_box(0));
stack->m_num = v_res_1498_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23___boxed(lean_object* v_toMatcherInfo_1499_, lean_object* v_i_1500_, lean_object* v_a_1501_, lean_object* v_x_1502_){
_start:
{
uint8_t v_res_1503_; lean_object* v_r_1504_; 
v_res_1503_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(v_toMatcherInfo_1499_, v_i_1500_, v_a_1501_, v_x_1502_);
lean_dec_ref(v_a_1501_);
lean_dec(v_i_1500_);
lean_dec_ref(v_toMatcherInfo_1499_);
v_r_1504_ = lean_box(v_res_1503_);
return v_r_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24(lean_object* v_mask_1505_, lean_object* v_absMotiveBody_1506_, lean_object* v_toPure_1507_, lean_object* v_xs_1508_, lean_object* v___body_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1510_ = l_Lean_Array_mask___redArg(v_mask_1505_, v_xs_1508_);
v___x_1511_ = lean_expr_instantiate_rev(v_absMotiveBody_1506_, v___x_1510_);
lean_dec(v___x_1510_);
v___x_1512_ = lean_apply_2(v_toPure_1507_, lean_box(0), v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24___boxed(lean_object* v_mask_1513_, lean_object* v_absMotiveBody_1514_, lean_object* v_toPure_1515_, lean_object* v_xs_1516_, lean_object* v___body_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24(v_mask_1513_, v_absMotiveBody_1514_, v_toPure_1515_, v_xs_1516_, v___body_1517_);
lean_dec_ref(v___body_1517_);
lean_dec_ref(v_absMotiveBody_1514_);
lean_dec_ref(v_mask_1513_);
return v_res_1518_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(lean_object* v_toFunctor_1519_, lean_object* v_mask_1520_, lean_object* v_toPure_1521_, lean_object* v_inst_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_matcherApp_1527_, uint8_t v_useSplitter_1528_, lean_object* v___f_1529_, lean_object* v___f_1530_, lean_object* v_absMotiveBody_1531_){
_start:
{
lean_object* v_map_1532_; lean_object* v___f_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v_map_1532_ = lean_ctor_get(v_toFunctor_1519_, 0);
lean_inc(v_map_1532_);
lean_dec_ref(v_toFunctor_1519_);
lean_inc(v_toPure_1521_);
v___f_1533_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24___boxed), 5, 3);
lean_closure_set(v___f_1533_, 0, v_mask_1520_);
lean_closure_set(v___f_1533_, 1, v_absMotiveBody_1531_);
lean_closure_set(v___f_1533_, 2, v_toPure_1521_);
v___x_1534_ = lean_apply_1(v_toPure_1521_, lean_box(0));
lean_inc(v___x_1534_);
v___x_1535_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_1522_, v_inst_1523_, v_inst_1524_, v_inst_1525_, v_inst_1526_, v_matcherApp_1527_, v_useSplitter_1528_, v_useSplitter_1528_, v___x_1534_, v___f_1533_, v___f_1529_, v___x_1534_);
v___x_1536_ = lean_apply_4(v_map_1532_, lean_box(0), lean_box(0), v___f_1530_, v___x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25_0interp(lean_interpreter_value* stack)
{
lean_object* v_toFunctor_1519_ = stack[0].m_obj;
lean_object* v_mask_1520_ = stack[1].m_obj;
lean_object* v_toPure_1521_ = stack[2].m_obj;
lean_object* v_inst_1522_ = stack[3].m_obj;
lean_object* v_inst_1523_ = stack[4].m_obj;
lean_object* v_inst_1524_ = stack[5].m_obj;
lean_object* v_inst_1525_ = stack[6].m_obj;
lean_object* v_inst_1526_ = stack[7].m_obj;
lean_object* v_matcherApp_1527_ = stack[8].m_obj;
uint8_t v_useSplitter_1528_ = stack[9].m_num;
lean_object* v___f_1529_ = stack[10].m_obj;
lean_object* v___f_1530_ = stack[11].m_obj;
lean_object* v_absMotiveBody_1531_ = stack[12].m_obj;
lean_object* v_res_1537_;
v_res_1537_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(v_toFunctor_1519_, v_mask_1520_, v_toPure_1521_, v_inst_1522_, v_inst_1523_, v_inst_1524_, v_inst_1525_, v_inst_1526_, v_matcherApp_1527_, v_useSplitter_1528_, v___f_1529_, v___f_1530_, v_absMotiveBody_1531_);
stack->m_obj
 = v_res_1537_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25___boxed(lean_object* v_toFunctor_1538_, lean_object* v_mask_1539_, lean_object* v_toPure_1540_, lean_object* v_inst_1541_, lean_object* v_inst_1542_, lean_object* v_inst_1543_, lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_matcherApp_1546_, lean_object* v_useSplitter_1547_, lean_object* v___f_1548_, lean_object* v___f_1549_, lean_object* v_absMotiveBody_1550_){
_start:
{
uint8_t v_useSplitter_boxed_1551_; lean_object* v_res_1552_; 
v_useSplitter_boxed_1551_ = lean_unbox(v_useSplitter_1547_);
v_res_1552_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(v_toFunctor_1538_, v_mask_1539_, v_toPure_1540_, v_inst_1541_, v_inst_1542_, v_inst_1543_, v_inst_1544_, v_inst_1545_, v_matcherApp_1546_, v_useSplitter_boxed_1551_, v___f_1548_, v___f_1549_, v_absMotiveBody_1550_);
return v_res_1552_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object* v_inst_1554_, lean_object* v_inst_1555_, lean_object* v_inst_1556_, lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_info_1559_, lean_object* v_resTy_1560_, lean_object* v_onAlt_1561_, uint8_t v_useSplitter_1562_){
_start:
{
switch(lean_obj_tag(v_info_1559_))
{
case 0:
{
lean_object* v_toApplicative_1563_; lean_object* v_toBind_1564_; lean_object* v_toPure_1565_; lean_object* v_e_1566_; lean_object* v___x_1567_; lean_object* v___f_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_toApplicative_1563_ = lean_ctor_get(v_inst_1556_, 0);
lean_dec_ref(v_inst_1558_);
lean_dec_ref(v_inst_1557_);
v_toBind_1564_ = lean_ctor_get(v_inst_1556_, 1);
lean_inc_n(v_toBind_1564_, 2);
v_toPure_1565_ = lean_ctor_get(v_toApplicative_1563_, 1);
lean_inc(v_toPure_1565_);
v_e_1566_ = lean_ctor_get(v_info_1559_, 0);
lean_inc_ref(v_e_1566_);
lean_dec_ref_known(v_info_1559_, 1);
v___x_1567_ = lean_box(v_useSplitter_1562_);
lean_inc(v_inst_1554_);
lean_inc_ref(v_resTy_1560_);
v___f_1568_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1568_, 0, v_e_1566_);
lean_closure_set(v___f_1568_, 1, v___x_1567_);
lean_closure_set(v___f_1568_, 2, v_resTy_1560_);
lean_closure_set(v___f_1568_, 3, v_toPure_1565_);
lean_closure_set(v___f_1568_, 4, v_onAlt_1561_);
lean_closure_set(v___f_1568_, 5, v_toBind_1564_);
lean_closure_set(v___f_1568_, 6, v_inst_1554_);
lean_closure_set(v___f_1568_, 7, v_inst_1555_);
lean_closure_set(v___f_1568_, 8, v_inst_1556_);
v___x_1569_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1569_, 0, v_resTy_1560_);
v___x_1570_ = lean_apply_2(v_inst_1554_, lean_box(0), v___x_1569_);
v___x_1571_ = lean_apply_4(v_toBind_1564_, lean_box(0), lean_box(0), v___x_1570_, v___f_1568_);
return v___x_1571_;
}
case 1:
{
lean_object* v_toApplicative_1572_; lean_object* v_toBind_1573_; lean_object* v_toPure_1574_; lean_object* v_e_1575_; lean_object* v___f_1576_; lean_object* v___f_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v_toApplicative_1572_ = lean_ctor_get(v_inst_1556_, 0);
lean_dec_ref(v_inst_1558_);
lean_dec_ref(v_inst_1557_);
v_toBind_1573_ = lean_ctor_get(v_inst_1556_, 1);
lean_inc_n(v_toBind_1573_, 3);
v_toPure_1574_ = lean_ctor_get(v_toApplicative_1572_, 1);
lean_inc(v_toPure_1574_);
v_e_1575_ = lean_ctor_get(v_info_1559_, 0);
lean_inc_ref(v_e_1575_);
lean_dec_ref_known(v_info_1559_, 1);
lean_inc_ref_n(v_resTy_1560_, 2);
lean_inc(v_onAlt_1561_);
lean_inc_n(v_inst_1554_, 2);
v___f_1576_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11), 5, 4);
lean_closure_set(v___f_1576_, 0, v_inst_1554_);
lean_closure_set(v___f_1576_, 1, v_onAlt_1561_);
lean_closure_set(v___f_1576_, 2, v_resTy_1560_);
lean_closure_set(v___f_1576_, 3, v_toBind_1573_);
v___f_1577_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed), 10, 9);
lean_closure_set(v___f_1577_, 0, v_inst_1554_);
lean_closure_set(v___f_1577_, 1, v_onAlt_1561_);
lean_closure_set(v___f_1577_, 2, v_resTy_1560_);
lean_closure_set(v___f_1577_, 3, v_toBind_1573_);
lean_closure_set(v___f_1577_, 4, v_e_1575_);
lean_closure_set(v___f_1577_, 5, v_toPure_1574_);
lean_closure_set(v___f_1577_, 6, v_inst_1555_);
lean_closure_set(v___f_1577_, 7, v_inst_1556_);
lean_closure_set(v___f_1577_, 8, v___f_1576_);
v___x_1578_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1578_, 0, v_resTy_1560_);
v___x_1579_ = lean_apply_2(v_inst_1554_, lean_box(0), v___x_1578_);
v___x_1580_ = lean_apply_4(v_toBind_1573_, lean_box(0), lean_box(0), v___x_1579_, v___f_1577_);
return v___x_1580_;
}
case 2:
{
lean_object* v_toApplicative_1581_; lean_object* v_toBind_1582_; lean_object* v_toPure_1583_; lean_object* v_e_1584_; lean_object* v___x_1585_; lean_object* v___f_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v_toApplicative_1581_ = lean_ctor_get(v_inst_1556_, 0);
lean_dec_ref(v_inst_1558_);
lean_dec_ref(v_inst_1557_);
v_toBind_1582_ = lean_ctor_get(v_inst_1556_, 1);
lean_inc_n(v_toBind_1582_, 2);
v_toPure_1583_ = lean_ctor_get(v_toApplicative_1581_, 1);
lean_inc(v_toPure_1583_);
v_e_1584_ = lean_ctor_get(v_info_1559_, 0);
lean_inc_ref(v_e_1584_);
lean_dec_ref_known(v_info_1559_, 1);
v___x_1585_ = lean_box(v_useSplitter_1562_);
lean_inc(v_inst_1554_);
lean_inc_ref(v_resTy_1560_);
v___f_1586_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22___boxed), 10, 9);
lean_closure_set(v___f_1586_, 0, v_e_1584_);
lean_closure_set(v___f_1586_, 1, v___x_1585_);
lean_closure_set(v___f_1586_, 2, v_resTy_1560_);
lean_closure_set(v___f_1586_, 3, v_toPure_1583_);
lean_closure_set(v___f_1586_, 4, v_onAlt_1561_);
lean_closure_set(v___f_1586_, 5, v_toBind_1582_);
lean_closure_set(v___f_1586_, 6, v_inst_1554_);
lean_closure_set(v___f_1586_, 7, v_inst_1555_);
lean_closure_set(v___f_1586_, 8, v_inst_1556_);
v___x_1587_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1587_, 0, v_resTy_1560_);
v___x_1588_ = lean_apply_2(v_inst_1554_, lean_box(0), v___x_1587_);
v___x_1589_ = lean_apply_4(v_toBind_1582_, lean_box(0), lean_box(0), v___x_1588_, v___f_1586_);
return v___x_1589_;
}
default: 
{
lean_object* v_toApplicative_1590_; lean_object* v_matcherApp_1591_; lean_object* v_toBind_1592_; lean_object* v_toFunctor_1593_; lean_object* v_toPure_1594_; lean_object* v_toMatcherInfo_1595_; lean_object* v_discrs_1596_; lean_object* v___f_1597_; lean_object* v___f_1598_; lean_object* v___f_1599_; lean_object* v___x_1600_; size_t v_sz_1601_; size_t v___x_1602_; lean_object* v_mask_1603_; lean_object* v___x_1604_; lean_object* v___f_1605_; lean_object* v_maskedDiscrs_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v_toApplicative_1590_ = lean_ctor_get(v_inst_1556_, 0);
v_matcherApp_1591_ = lean_ctor_get(v_info_1559_, 0);
lean_inc_ref(v_matcherApp_1591_);
lean_dec_ref_known(v_info_1559_, 1);
v_toBind_1592_ = lean_ctor_get(v_inst_1556_, 1);
lean_inc(v_toBind_1592_);
v_toFunctor_1593_ = lean_ctor_get(v_toApplicative_1590_, 0);
lean_inc_ref(v_toFunctor_1593_);
v_toPure_1594_ = lean_ctor_get(v_toApplicative_1590_, 1);
lean_inc(v_toPure_1594_);
v_toMatcherInfo_1595_ = lean_ctor_get(v_matcherApp_1591_, 0);
v_discrs_1596_ = lean_ctor_get(v_matcherApp_1591_, 5);
lean_inc_ref_n(v_discrs_1596_, 2);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21___boxed), 5, 1);
lean_closure_set(v___f_1597_, 0, v_onAlt_1561_);
v___f_1598_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0));
lean_inc_ref(v_toMatcherInfo_1595_);
v___f_1599_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23___boxed), 4, 1);
lean_closure_set(v___f_1599_, 0, v_toMatcherInfo_1595_);
v___x_1600_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_1601_ = lean_array_size(v_discrs_1596_);
v___x_1602_ = ((size_t)0ULL);
v_mask_1603_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1600_, v_discrs_1596_, v___f_1599_, v_sz_1601_, v___x_1602_, v_discrs_1596_);
v___x_1604_ = lean_box(v_useSplitter_1562_);
lean_inc(v_inst_1554_);
lean_inc(v_mask_1603_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25___boxed), 13, 12);
lean_closure_set(v___f_1605_, 0, v_toFunctor_1593_);
lean_closure_set(v___f_1605_, 1, v_mask_1603_);
lean_closure_set(v___f_1605_, 2, v_toPure_1594_);
lean_closure_set(v___f_1605_, 3, v_inst_1554_);
lean_closure_set(v___f_1605_, 4, v_inst_1555_);
lean_closure_set(v___f_1605_, 5, v_inst_1556_);
lean_closure_set(v___f_1605_, 6, v_inst_1557_);
lean_closure_set(v___f_1605_, 7, v_inst_1558_);
lean_closure_set(v___f_1605_, 8, v_matcherApp_1591_);
lean_closure_set(v___f_1605_, 9, v___x_1604_);
lean_closure_set(v___f_1605_, 10, v___f_1597_);
lean_closure_set(v___f_1605_, 11, v___f_1598_);
v_maskedDiscrs_1606_ = l_Lean_Array_mask___redArg(v_mask_1603_, v_discrs_1596_);
lean_dec(v_mask_1603_);
v___x_1607_ = lean_alloc_closure((void*)(l_Lean_Expr_abstractM___boxed), 7, 2);
lean_closure_set(v___x_1607_, 0, v_resTy_1560_);
lean_closure_set(v___x_1607_, 1, v_maskedDiscrs_1606_);
v___x_1608_ = lean_apply_2(v_inst_1554_, lean_box(0), v___x_1607_);
v___x_1609_ = lean_apply_4(v_toBind_1592_, lean_box(0), lean_box(0), v___x_1608_, v___f_1605_);
return v___x_1609_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1554_ = stack[0].m_obj;
lean_object* v_inst_1555_ = stack[1].m_obj;
lean_object* v_inst_1556_ = stack[2].m_obj;
lean_object* v_inst_1557_ = stack[3].m_obj;
lean_object* v_inst_1558_ = stack[4].m_obj;
lean_object* v_info_1559_ = stack[5].m_obj;
lean_object* v_resTy_1560_ = stack[6].m_obj;
lean_object* v_onAlt_1561_ = stack[7].m_obj;
uint8_t v_useSplitter_1562_ = stack[8].m_num;
lean_object* v_res_1610_;
v_res_1610_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1554_, v_inst_1555_, v_inst_1556_, v_inst_1557_, v_inst_1558_, v_info_1559_, v_resTy_1560_, v_onAlt_1561_, v_useSplitter_1562_);
stack->m_obj
 = v_res_1610_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_inst_1615_, lean_object* v_info_1616_, lean_object* v_resTy_1617_, lean_object* v_onAlt_1618_, lean_object* v_useSplitter_1619_){
_start:
{
uint8_t v_useSplitter_boxed_1620_; lean_object* v_res_1621_; 
v_useSplitter_boxed_1620_ = lean_unbox(v_useSplitter_1619_);
v_res_1621_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1611_, v_inst_1612_, v_inst_1613_, v_inst_1614_, v_inst_1615_, v_info_1616_, v_resTy_1617_, v_onAlt_1618_, v_useSplitter_boxed_1620_);
return v_res_1621_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object* v_n_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v_info_1631_, lean_object* v_resTy_1632_, lean_object* v_onAlt_1633_, uint8_t v_useSplitter_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1623_, v_inst_1624_, v_inst_1625_, v_inst_1626_, v_inst_1627_, v_info_1631_, v_resTy_1632_, v_onAlt_1633_, v_useSplitter_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_splitWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1623_ = stack[1].m_obj;
lean_object* v_inst_1624_ = stack[2].m_obj;
lean_object* v_inst_1625_ = stack[3].m_obj;
lean_object* v_inst_1626_ = stack[4].m_obj;
lean_object* v_inst_1627_ = stack[5].m_obj;
lean_object* v_inst_1628_ = stack[6].m_obj;
lean_object* v_inst_1629_ = stack[7].m_obj;
lean_object* v_inst_1630_ = stack[8].m_obj;
lean_object* v_info_1631_ = stack[9].m_obj;
lean_object* v_resTy_1632_ = stack[10].m_obj;
lean_object* v_onAlt_1633_ = stack[11].m_obj;
uint8_t v_useSplitter_1634_ = stack[12].m_num;
lean_object* v_res_1636_;
v_res_1636_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_box(0), v_inst_1623_, v_inst_1624_, v_inst_1625_, v_inst_1626_, v_inst_1627_, v_inst_1628_, v_inst_1629_, v_inst_1630_, v_info_1631_, v_resTy_1632_, v_onAlt_1633_, v_useSplitter_1634_);
stack->m_obj
 = v_res_1636_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object* v_n_1637_, lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_info_1646_, lean_object* v_resTy_1647_, lean_object* v_onAlt_1648_, lean_object* v_useSplitter_1649_){
_start:
{
uint8_t v_useSplitter_boxed_1650_; lean_object* v_res_1651_; 
v_useSplitter_boxed_1650_ = lean_unbox(v_useSplitter_1649_);
v_res_1651_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(v_n_1637_, v_inst_1638_, v_inst_1639_, v_inst_1640_, v_inst_1641_, v_inst_1642_, v_inst_1643_, v_inst_1644_, v_inst_1645_, v_info_1646_, v_resTy_1647_, v_onAlt_1648_, v_useSplitter_boxed_1650_);
lean_dec_ref(v_inst_1645_);
lean_dec(v_inst_1644_);
lean_dec_ref(v_inst_1643_);
return v_res_1651_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object* v_info_1652_, lean_object* v_e_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_){
_start:
{
if (lean_obj_tag(v_info_1652_) == 3)
{
lean_object* v_matcherApp_1662_; lean_object* v_toMatcherInfo_1663_; lean_object* v___x_1664_; 
v_matcherApp_1662_ = lean_ctor_get(v_info_1652_, 0);
lean_inc_ref(v_matcherApp_1662_);
lean_dec_ref_known(v_info_1652_, 1);
v_toMatcherInfo_1663_ = lean_ctor_get(v_matcherApp_1662_, 0);
lean_inc_ref(v_toMatcherInfo_1663_);
lean_dec_ref(v_matcherApp_1662_);
v___x_1664_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_toMatcherInfo_1663_, v_e_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
return v___x_1664_;
}
else
{
lean_object* v___x_1665_; lean_object* v___x_1666_; 
lean_dec_ref(v_e_1653_);
lean_dec_ref(v_info_1652_);
v___x_1665_ = lean_box(0);
v___x_1666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
return v___x_1666_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1652_ = stack[0].m_obj;
lean_object* v_e_1653_ = stack[1].m_obj;
lean_object* v_a_1654_ = stack[2].m_obj;
lean_object* v_a_1655_ = stack[3].m_obj;
lean_object* v_a_1656_ = stack[4].m_obj;
lean_object* v_a_1657_ = stack[5].m_obj;
lean_object* v_a_1658_ = stack[6].m_obj;
lean_object* v_a_1659_ = stack[7].m_obj;
lean_object* v_a_1660_ = stack[8].m_obj;
lean_object* v_res_1667_;
v_res_1667_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(v_info_1652_, v_e_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
stack->m_obj
 = v_res_1667_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object* v_info_1668_, lean_object* v_e_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(v_info_1668_, v_e_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
return v_res_1678_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object* v_declName_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; lean_object* v_env_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1682_ = lean_st_ref_get(v___y_1680_);
v_env_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc_ref(v_env_1683_);
lean_dec(v___x_1682_);
v___x_1684_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1683_, v_declName_1679_);
v___x_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
return v___x_1685_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1679_ = stack[0].m_obj;
lean_object* v___y_1680_ = stack[1].m_obj;
lean_object* v_res_1686_;
v_res_1686_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1679_, v___y_1680_);
stack->m_obj
 = v_res_1686_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object* v_declName_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1687_, v___y_1688_);
lean_dec(v___y_1688_);
return v_res_1690_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v___x_1697_; lean_object* v_env_1698_; uint8_t v___x_1699_; lean_object* v_env_1700_; lean_object* v___x_1701_; lean_object* v_toCold_1702_; lean_object* v_mctx_1703_; lean_object* v_lctx_1704_; lean_object* v_options_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1697_ = lean_st_ref_get(v___y_1695_);
v_env_1698_ = lean_ctor_get(v___x_1697_, 0);
lean_inc_ref(v_env_1698_);
lean_dec(v___x_1697_);
v___x_1699_ = 0;
v_env_1700_ = l_Lean_Environment_setRecordingDeps(v_env_1698_, v___x_1699_);
v___x_1701_ = lean_st_ref_get(v___y_1693_);
v_toCold_1702_ = lean_ctor_get(v___y_1694_, 0);
v_mctx_1703_ = lean_ctor_get(v___x_1701_, 0);
lean_inc_ref(v_mctx_1703_);
lean_dec(v___x_1701_);
v_lctx_1704_ = lean_ctor_get(v___y_1692_, 2);
v_options_1705_ = lean_ctor_get(v_toCold_1702_, 2);
lean_inc_ref(v_options_1705_);
lean_inc_ref(v_lctx_1704_);
v___x_1706_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1706_, 0, v_env_1700_);
lean_ctor_set(v___x_1706_, 1, v_mctx_1703_);
lean_ctor_set(v___x_1706_, 2, v_lctx_1704_);
lean_ctor_set(v___x_1706_, 3, v_options_1705_);
v___x_1707_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set(v___x_1707_, 1, v_msgData_1691_);
v___x_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_1691_ = stack[0].m_obj;
lean_object* v___y_1692_ = stack[1].m_obj;
lean_object* v___y_1693_ = stack[2].m_obj;
lean_object* v___y_1694_ = stack[3].m_obj;
lean_object* v___y_1695_ = stack[4].m_obj;
lean_object* v_res_1709_;
v_res_1709_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
stack->m_obj
 = v_res_1709_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1716_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_){
_start:
{
lean_object* v_ref_1723_; lean_object* v___x_1724_; lean_object* v_a_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1733_; 
v_ref_1723_ = lean_ctor_get(v___y_1720_, 2);
v___x_1724_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1727_ = v___x_1724_;
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_a_1725_);
lean_dec(v___x_1724_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1733_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1729_; lean_object* v___x_1731_; 
lean_inc(v_ref_1723_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v_ref_1723_);
lean_ctor_set(v___x_1729_, 1, v_a_1725_);
if (v_isShared_1728_ == 0)
{
lean_ctor_set_tag(v___x_1727_, 1);
lean_ctor_set(v___x_1727_, 0, v___x_1729_);
v___x_1731_ = v___x_1727_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1717_ = stack[0].m_obj;
lean_object* v___y_1718_ = stack[1].m_obj;
lean_object* v___y_1719_ = stack[2].m_obj;
lean_object* v___y_1720_ = stack[3].m_obj;
lean_object* v___y_1721_ = stack[4].m_obj;
lean_object* v_res_1734_;
v_res_1734_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_);
stack->m_obj
 = v_res_1734_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
return v_res_1741_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_1742_, lean_object* v_msg_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_toCold_1749_; lean_object* v_currRecDepth_1750_; lean_object* v_ref_1751_; uint16_t v_optionFlags_1752_; uint8_t v_suppressElabErrors_1753_; uint8_t v_isRecordingDeps_1754_; lean_object* v_ref_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v_toCold_1749_ = lean_ctor_get(v___y_1746_, 0);
v_currRecDepth_1750_ = lean_ctor_get(v___y_1746_, 1);
v_ref_1751_ = lean_ctor_get(v___y_1746_, 2);
v_optionFlags_1752_ = lean_ctor_get_uint16(v___y_1746_, sizeof(void*)*3);
v_suppressElabErrors_1753_ = lean_ctor_get_uint8(v___y_1746_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1754_ = lean_ctor_get_uint8(v___y_1746_, sizeof(void*)*3 + 3);
v_ref_1755_ = l_Lean_replaceRef(v_ref_1742_, v_ref_1751_);
lean_inc(v_currRecDepth_1750_);
lean_inc_ref(v_toCold_1749_);
v___x_1756_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1756_, 0, v_toCold_1749_);
lean_ctor_set(v___x_1756_, 1, v_currRecDepth_1750_);
lean_ctor_set(v___x_1756_, 2, v_ref_1755_);
lean_ctor_set_uint16(v___x_1756_, sizeof(void*)*3, v_optionFlags_1752_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*3 + 2, v_suppressElabErrors_1753_);
lean_ctor_set_uint8(v___x_1756_, sizeof(void*)*3 + 3, v_isRecordingDeps_1754_);
v___x_1757_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1743_, v___y_1744_, v___y_1745_, v___x_1756_, v___y_1747_);
lean_dec_ref_known(v___x_1756_, 3);
return v___x_1757_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1742_ = stack[0].m_obj;
lean_object* v_msg_1743_ = stack[1].m_obj;
lean_object* v___y_1744_ = stack[2].m_obj;
lean_object* v___y_1745_ = stack[3].m_obj;
lean_object* v___y_1746_ = stack[4].m_obj;
lean_object* v___y_1747_ = stack[5].m_obj;
lean_object* v_res_1758_;
v_res_1758_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1742_, v_msg_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
stack->m_obj
 = v_res_1758_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1759_, lean_object* v_msg_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1759_, v_msg_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v_ref_1759_);
return v_res_1766_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1767_; 
v___x_1767_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
return v___x_1769_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1770_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1771_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1772_ = lean_unsigned_to_nat(0u);
v___x_1773_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1772_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
lean_ctor_set(v___x_1773_, 2, v___x_1772_);
lean_ctor_set(v___x_1773_, 3, v___x_1772_);
lean_ctor_set(v___x_1773_, 4, v___x_1771_);
lean_ctor_set(v___x_1773_, 5, v___x_1771_);
lean_ctor_set(v___x_1773_, 6, v___x_1771_);
lean_ctor_set(v___x_1773_, 7, v___x_1771_);
lean_ctor_set(v___x_1773_, 8, v___x_1771_);
lean_ctor_set(v___x_1773_, 9, v___x_1771_);
lean_ctor_set(v___x_1773_, 10, v___x_1771_);
lean_ctor_set(v___x_1773_, 11, v___x_1770_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_unsigned_to_nat(32u);
v___x_1775_ = lean_mk_empty_array_with_capacity(v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1777_ = ((size_t)5ULL);
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_unsigned_to_nat(32u);
v___x_1780_ = lean_mk_empty_array_with_capacity(v___x_1779_);
v___x_1781_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_1782_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v___x_1780_);
lean_ctor_set(v___x_1782_, 2, v___x_1778_);
lean_ctor_set(v___x_1782_, 3, v___x_1778_);
lean_ctor_set_usize(v___x_1782_, 4, v___x_1777_);
return v___x_1782_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1783_ = lean_box(1);
v___x_1784_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_1785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1785_);
lean_ctor_set(v___x_1786_, 1, v___x_1784_);
lean_ctor_set(v___x_1786_, 2, v___x_1783_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_1789_ = l_Lean_stringToMessageData(v___x_1788_);
return v___x_1789_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_1792_ = l_Lean_stringToMessageData(v___x_1791_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_1795_ = l_Lean_stringToMessageData(v___x_1794_);
return v___x_1795_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_1798_ = l_Lean_stringToMessageData(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_1801_ = l_Lean_stringToMessageData(v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__20));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__22));
v___x_1813_ = l_Lean_stringToMessageData(v___x_1812_);
return v___x_1813_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__24));
v___x_1816_ = l_Lean_stringToMessageData(v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__26));
v___x_1819_ = l_Lean_stringToMessageData(v___x_1818_);
return v___x_1819_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_1820_, lean_object* v_declHint_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v_env_1826_; uint8_t v___x_1827_; 
v___x_1824_ = lean_box(0);
v___x_1825_ = lean_st_ref_get(v___y_1822_);
v_env_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc_ref(v_env_1826_);
lean_dec(v___x_1825_);
v___x_1827_ = l_Lean_Name_isAnonymous(v_declHint_1821_);
if (v___x_1827_ == 0)
{
uint8_t v_isExporting_1828_; 
v_isExporting_1828_ = lean_ctor_get_uint8(v_env_1826_, sizeof(void*)*13);
if (v_isExporting_1828_ == 0)
{
lean_object* v___x_1829_; 
lean_dec_ref(v_env_1826_);
lean_dec(v_declHint_1821_);
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v_msg_1820_);
return v___x_1829_;
}
else
{
lean_object* v___x_1830_; uint8_t v___x_1831_; 
lean_inc_ref(v_env_1826_);
v___x_1830_ = l_Lean_Environment_setExporting(v_env_1826_, v___x_1827_);
lean_inc(v_declHint_1821_);
lean_inc_ref(v___x_1830_);
v___x_1831_ = l_Lean_Environment_contains(v___x_1830_, v_declHint_1821_, v_isExporting_1828_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; 
lean_dec_ref(v___x_1830_);
lean_dec_ref(v_env_1826_);
lean_dec(v_declHint_1821_);
v___x_1832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1832_, 0, v_msg_1820_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v_c_1838_; lean_object* v___x_1839_; 
v___x_1833_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_1834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_1835_ = l_Lean_Options_empty;
v___x_1836_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1830_);
lean_ctor_set(v___x_1836_, 1, v___x_1833_);
lean_ctor_set(v___x_1836_, 2, v___x_1834_);
lean_ctor_set(v___x_1836_, 3, v___x_1835_);
lean_inc(v_declHint_1821_);
v___x_1837_ = l_Lean_MessageData_ofConstName(v_declHint_1821_, v___x_1827_);
v_c_1838_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1838_, 0, v___x_1836_);
lean_ctor_set(v_c_1838_, 1, v___x_1837_);
v___x_1839_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1826_, v_declHint_1821_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
lean_dec_ref(v_env_1826_);
lean_dec(v_declHint_1821_);
v___x_1840_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1840_);
lean_ctor_set(v___x_1841_, 1, v_c_1838_);
v___x_1842_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_1843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1841_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
v___x_1844_ = l_Lean_MessageData_note(v___x_1843_);
v___x_1845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1845_, 0, v_msg_1820_);
lean_ctor_set(v___x_1845_, 1, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
else
{
lean_object* v_val_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1903_; 
v_val_1847_ = lean_ctor_get(v___x_1839_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1839_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1849_ = v___x_1839_;
v_isShared_1850_ = v_isSharedCheck_1903_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_val_1847_);
lean_dec(v___x_1839_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1903_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v_modules_1852_; lean_object* v_moduleNames_1853_; lean_object* v_mod_1854_; uint8_t v___y_1856_; uint8_t v___x_1886_; 
v___x_1851_ = l_Lean_Environment_header(v_env_1826_);
lean_dec_ref(v_env_1826_);
v_modules_1852_ = lean_ctor_get(v___x_1851_, 3);
lean_inc_ref(v_modules_1852_);
v_moduleNames_1853_ = lean_ctor_get(v___x_1851_, 4);
lean_inc_ref(v_moduleNames_1853_);
lean_dec_ref(v___x_1851_);
v_mod_1854_ = lean_array_get(v___x_1824_, v_moduleNames_1853_, v_val_1847_);
lean_dec_ref(v_moduleNames_1853_);
v___x_1886_ = l_Lean_isPrivateName(v_declHint_1821_);
lean_dec(v_declHint_1821_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = lean_array_get_size(v_modules_1852_);
v___x_1888_ = lean_nat_dec_lt(v_val_1847_, v___x_1887_);
if (v___x_1888_ == 0)
{
lean_dec_ref(v_modules_1852_);
lean_dec(v_val_1847_);
v___y_1856_ = v___x_1886_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1889_; lean_object* v_toImport_1890_; uint8_t v_isExported_1891_; 
v___x_1889_ = lean_array_fget(v_modules_1852_, v_val_1847_);
lean_dec(v_val_1847_);
lean_dec_ref(v_modules_1852_);
v_toImport_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc_ref(v_toImport_1890_);
lean_dec(v___x_1889_);
v_isExported_1891_ = lean_ctor_get_uint8(v_toImport_1890_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1890_);
v___y_1856_ = v_isExported_1891_;
goto v___jp_1855_;
}
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec_ref(v_modules_1852_);
lean_del_object(v___x_1849_);
lean_dec(v_val_1847_);
v___x_1892_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v_c_1838_);
v___x_1894_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25);
v___x_1895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = l_Lean_MessageData_ofName(v_mod_1854_);
v___x_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1895_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = l_Lean_MessageData_note(v___x_1899_);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v_msg_1820_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
return v___x_1902_;
}
v___jp_1855_:
{
if (v___y_1856_ == 0)
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_1858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v_c_1838_);
v___x_1859_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = l_Lean_MessageData_ofName(v_mod_1854_);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = l_Lean_MessageData_note(v___x_1864_);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v_msg_1820_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set_tag(v___x_1849_, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1866_);
v___x_1868_ = v___x_1849_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
else
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1870_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1870_);
lean_ctor_set(v___x_1871_, 1, v_c_1838_);
v___x_1872_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = l_Lean_MessageData_ofName(v_mod_1854_);
lean_inc_ref(v___x_1874_);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1873_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v___x_1874_);
v___x_1879_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23);
v___x_1880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1880_, 0, v___x_1878_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
v___x_1881_ = l_Lean_MessageData_note(v___x_1880_);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v_msg_1820_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set_tag(v___x_1849_, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1882_);
v___x_1884_ = v___x_1849_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
return v___x_1884_;
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
lean_object* v___x_1904_; 
lean_dec_ref(v_env_1826_);
lean_dec(v_declHint_1821_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_msg_1820_);
return v___x_1904_;
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1820_ = stack[0].m_obj;
lean_object* v_declHint_1821_ = stack[1].m_obj;
lean_object* v___y_1822_ = stack[2].m_obj;
lean_object* v_res_1905_;
v_res_1905_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1820_, v_declHint_1821_, v___y_1822_);
stack->m_obj
 = v_res_1905_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1906_, lean_object* v_declHint_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1906_, v_declHint_1907_, v___y_1908_);
lean_dec(v___y_1908_);
return v_res_1910_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object* v_msg_1911_, lean_object* v_declHint_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v___x_1918_; lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1928_; 
v___x_1918_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1911_, v_declHint_1912_, v___y_1916_);
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1921_ = v___x_1918_;
v_isShared_1922_ = v_isSharedCheck_1928_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1918_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1928_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1923_ = l_Lean_unknownIdentifierMessageTag;
v___x_1924_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v_a_1919_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 0, v___x_1924_);
v___x_1926_ = v___x_1921_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1911_ = stack[0].m_obj;
lean_object* v_declHint_1912_ = stack[1].m_obj;
lean_object* v___y_1913_ = stack[2].m_obj;
lean_object* v___y_1914_ = stack[3].m_obj;
lean_object* v___y_1915_ = stack[4].m_obj;
lean_object* v___y_1916_ = stack[5].m_obj;
lean_object* v_res_1929_;
v_res_1929_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1911_, v_declHint_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
stack->m_obj
 = v_res_1929_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1930_, lean_object* v_declHint_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1930_, v_declHint_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_);
lean_dec(v___y_1935_);
lean_dec_ref(v___y_1934_);
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
return v_res_1937_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1938_, lean_object* v_msg_1939_, lean_object* v_declHint_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v_a_1947_; lean_object* v___x_1948_; 
v___x_1946_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1939_, v_declHint_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref(v___x_1946_);
v___x_1948_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1938_, v_a_1947_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
return v___x_1948_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1938_ = stack[0].m_obj;
lean_object* v_msg_1939_ = stack[1].m_obj;
lean_object* v_declHint_1940_ = stack[2].m_obj;
lean_object* v___y_1941_ = stack[3].m_obj;
lean_object* v___y_1942_ = stack[4].m_obj;
lean_object* v___y_1943_ = stack[5].m_obj;
lean_object* v___y_1944_ = stack[6].m_obj;
lean_object* v_res_1949_;
v_res_1949_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1938_, v_msg_1939_, v_declHint_1940_, v___y_1941_, v___y_1942_, v___y_1943_, v___y_1944_);
stack->m_obj
 = v_res_1949_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1950_, lean_object* v_msg_1951_, lean_object* v_declHint_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1950_, v_msg_1951_, v_declHint_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v_ref_1950_);
return v_res_1958_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_1961_ = l_Lean_stringToMessageData(v___x_1960_);
return v___x_1961_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1963_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2));
v___x_1964_ = l_Lean_stringToMessageData(v___x_1963_);
return v___x_1964_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1965_, lean_object* v_constName_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; uint8_t v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1972_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1973_ = 0;
lean_inc(v_constName_1966_);
v___x_1974_ = l_Lean_MessageData_ofConstName(v_constName_1966_, v___x_1973_);
v___x_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1972_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1965_, v___x_1977_, v_constName_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_1978_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_1965_ = stack[0].m_obj;
lean_object* v_constName_1966_ = stack[1].m_obj;
lean_object* v___y_1967_ = stack[2].m_obj;
lean_object* v___y_1968_ = stack[3].m_obj;
lean_object* v___y_1969_ = stack[4].m_obj;
lean_object* v___y_1970_ = stack[5].m_obj;
lean_object* v_res_1979_;
v_res_1979_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1965_, v_constName_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
stack->m_obj
 = v_res_1979_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1980_, lean_object* v_constName_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1980_, v_constName_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v_ref_1980_);
return v_res_1987_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v_ref_1994_; lean_object* v___x_1995_; 
v_ref_1994_ = lean_ctor_get(v___y_1991_, 2);
v___x_1995_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1994_, v_constName_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
return v___x_1995_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_1988_ = stack[0].m_obj;
lean_object* v___y_1989_ = stack[1].m_obj;
lean_object* v___y_1990_ = stack[2].m_obj;
lean_object* v___y_1991_ = stack[3].m_obj;
lean_object* v___y_1992_ = stack[4].m_obj;
lean_object* v_res_1996_;
v_res_1996_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_);
stack->m_obj
 = v_res_1996_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1997_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2003_;
}
}
lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object* v_constName_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
lean_object* v___x_2010_; lean_object* v_env_2011_; uint8_t v___x_2012_; lean_object* v___x_2013_; 
v___x_2010_ = lean_st_ref_get(v___y_2008_);
v_env_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc_ref(v_env_2011_);
lean_dec(v___x_2010_);
v___x_2012_ = 0;
lean_inc(v_constName_2004_);
v___x_2013_ = l_Lean_Environment_find_x3f(v_env_2011_, v_constName_2004_, v___x_2012_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
return v___x_2014_;
}
else
{
lean_object* v_val_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2022_; 
lean_dec(v_constName_2004_);
v_val_2015_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2017_ = v___x_2013_;
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_val_2015_);
lean_dec(v___x_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2022_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2020_; 
if (v_isShared_2018_ == 0)
{
lean_ctor_set_tag(v___x_2017_, 0);
v___x_2020_ = v___x_2017_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_val_2015_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2004_ = stack[0].m_obj;
lean_object* v___y_2005_ = stack[1].m_obj;
lean_object* v___y_2006_ = stack[2].m_obj;
lean_object* v___y_2007_ = stack[3].m_obj;
lean_object* v___y_2008_ = stack[4].m_obj;
lean_object* v_res_2023_;
v_res_2023_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
stack->m_obj
 = v_res_2023_;
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object* v_constName_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
lean_dec(v___y_2028_);
lean_dec_ref(v___y_2027_);
lean_dec(v___y_2026_);
lean_dec_ref(v___y_2025_);
return v_res_2030_;
}
}
lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object* v_msg_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
lean_object* v___x_2037_; lean_object* v_toApplicative_2038_; lean_object* v_toFunctor_2039_; lean_object* v_toSeq_2040_; lean_object* v_toSeqLeft_2041_; lean_object* v_toSeqRight_2042_; lean_object* v___f_2043_; lean_object* v___f_2044_; lean_object* v___f_2045_; lean_object* v___f_2046_; lean_object* v___x_2047_; lean_object* v___f_2048_; lean_object* v___f_2049_; lean_object* v___f_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v_toApplicative_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2085_; 
v___x_2037_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_2038_ = lean_ctor_get(v___x_2037_, 0);
v_toFunctor_2039_ = lean_ctor_get(v_toApplicative_2038_, 0);
v_toSeq_2040_ = lean_ctor_get(v_toApplicative_2038_, 2);
v_toSeqLeft_2041_ = lean_ctor_get(v_toApplicative_2038_, 3);
v_toSeqRight_2042_ = lean_ctor_get(v_toApplicative_2038_, 4);
v___f_2043_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_2044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2039_, 2);
v___f_2045_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2045_, 0, v_toFunctor_2039_);
v___f_2046_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2046_, 0, v_toFunctor_2039_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___f_2045_);
lean_ctor_set(v___x_2047_, 1, v___f_2046_);
lean_inc(v_toSeqRight_2042_);
v___f_2048_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2048_, 0, v_toSeqRight_2042_);
lean_inc(v_toSeqLeft_2041_);
v___f_2049_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2049_, 0, v_toSeqLeft_2041_);
lean_inc(v_toSeq_2040_);
v___f_2050_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2050_, 0, v_toSeq_2040_);
v___x_2051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2047_);
lean_ctor_set(v___x_2051_, 1, v___f_2043_);
lean_ctor_set(v___x_2051_, 2, v___f_2050_);
lean_ctor_set(v___x_2051_, 3, v___f_2049_);
lean_ctor_set(v___x_2051_, 4, v___f_2048_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v___x_2051_);
lean_ctor_set(v___x_2052_, 1, v___f_2044_);
v___x_2053_ = l_StateRefT_x27_instMonad___redArg(v___x_2052_);
v_toApplicative_2054_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2085_ == 0)
{
lean_object* v_unused_2086_; 
v_unused_2086_ = lean_ctor_get(v___x_2053_, 1);
lean_dec(v_unused_2086_);
v___x_2056_ = v___x_2053_;
v_isShared_2057_ = v_isSharedCheck_2085_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_toApplicative_2054_);
lean_dec(v___x_2053_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2085_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v_toFunctor_2058_; lean_object* v_toSeq_2059_; lean_object* v_toSeqLeft_2060_; lean_object* v_toSeqRight_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2083_; 
v_toFunctor_2058_ = lean_ctor_get(v_toApplicative_2054_, 0);
v_toSeq_2059_ = lean_ctor_get(v_toApplicative_2054_, 2);
v_toSeqLeft_2060_ = lean_ctor_get(v_toApplicative_2054_, 3);
v_toSeqRight_2061_ = lean_ctor_get(v_toApplicative_2054_, 4);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_toApplicative_2054_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v_toApplicative_2054_, 1);
lean_dec(v_unused_2084_);
v___x_2063_ = v_toApplicative_2054_;
v_isShared_2064_ = v_isSharedCheck_2083_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_toSeqRight_2061_);
lean_inc(v_toSeqLeft_2060_);
lean_inc(v_toSeq_2059_);
lean_inc(v_toFunctor_2058_);
lean_dec(v_toApplicative_2054_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2083_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___f_2065_; lean_object* v___f_2066_; lean_object* v___f_2067_; lean_object* v___f_2068_; lean_object* v___x_2069_; lean_object* v___f_2070_; lean_object* v___f_2071_; lean_object* v___f_2072_; lean_object* v___x_2074_; 
v___f_2065_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_2066_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_2058_);
v___f_2067_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2067_, 0, v_toFunctor_2058_);
v___f_2068_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2068_, 0, v_toFunctor_2058_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___f_2067_);
lean_ctor_set(v___x_2069_, 1, v___f_2068_);
v___f_2070_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2070_, 0, v_toSeqRight_2061_);
v___f_2071_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2071_, 0, v_toSeqLeft_2060_);
v___f_2072_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2072_, 0, v_toSeq_2059_);
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 4, v___f_2070_);
lean_ctor_set(v___x_2063_, 3, v___f_2071_);
lean_ctor_set(v___x_2063_, 2, v___f_2072_);
lean_ctor_set(v___x_2063_, 1, v___f_2065_);
lean_ctor_set(v___x_2063_, 0, v___x_2069_);
v___x_2074_ = v___x_2063_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___f_2065_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v___f_2072_);
lean_ctor_set(v_reuseFailAlloc_2082_, 3, v___f_2071_);
lean_ctor_set(v_reuseFailAlloc_2082_, 4, v___f_2070_);
v___x_2074_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v___x_2076_; 
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 1, v___f_2066_);
lean_ctor_set(v___x_2056_, 0, v___x_2074_);
v___x_2076_ = v___x_2056_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2081_, 1, v___f_2066_);
v___x_2076_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2732__overap_2079_; lean_object* v___x_2080_; 
v___x_2077_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2078_ = l_instInhabitedOfMonad___redArg(v___x_2076_, v___x_2077_);
v___x_2732__overap_2079_ = lean_panic_fn_borrowed(v___x_2078_, v_msg_2031_);
lean_dec(v___x_2078_);
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2034_);
lean_inc(v___y_2033_);
lean_inc_ref(v___y_2032_);
v___x_2080_ = lean_apply_5(v___x_2732__overap_2079_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, lean_box(0));
return v___x_2080_;
}
}
}
}
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2031_ = stack[0].m_obj;
lean_object* v___y_2032_ = stack[1].m_obj;
lean_object* v___y_2033_ = stack[2].m_obj;
lean_object* v___y_2034_ = stack[3].m_obj;
lean_object* v___y_2035_ = stack[4].m_obj;
lean_object* v_res_2087_;
v_res_2087_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
stack->m_obj
 = v_res_2087_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object* v_msg_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2094_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2098_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2));
v___x_2099_ = lean_unsigned_to_nat(53u);
v___x_2100_ = lean_unsigned_to_nat(62u);
v___x_2101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1));
v___x_2102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0));
v___x_2103_ = l_mkPanicMessageWithDecl(v___x_2102_, v___x_2101_, v___x_2100_, v___x_2099_, v___x_2098_);
return v___x_2103_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t v_sz_2104_, size_t v_i_2105_, lean_object* v_bs_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
uint8_t v___x_2112_; 
v___x_2112_ = lean_usize_dec_lt(v_i_2105_, v_sz_2104_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v_bs_2106_);
return v___x_2113_;
}
else
{
lean_object* v_v_2114_; lean_object* v___x_2115_; lean_object* v_bs_x27_2116_; lean_object* v_a_2118_; lean_object* v___x_2123_; 
v_v_2114_ = lean_array_uget(v_bs_2106_, v_i_2105_);
v___x_2115_ = lean_unsigned_to_nat(0u);
v_bs_x27_2116_ = lean_array_uset(v_bs_2106_, v_i_2105_, v___x_2115_);
v___x_2123_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_2114_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
if (lean_obj_tag(v_a_2124_) == 6)
{
lean_object* v_val_2125_; lean_object* v_numFields_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; 
v_val_2125_ = lean_ctor_get(v_a_2124_, 0);
lean_inc_ref(v_val_2125_);
lean_dec_ref_known(v_a_2124_, 1);
v_numFields_2126_ = lean_ctor_get(v_val_2125_, 4);
lean_inc(v_numFields_2126_);
lean_dec_ref(v_val_2125_);
v___x_2127_ = 0;
v___x_2128_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2128_, 0, v_numFields_2126_);
lean_ctor_set(v___x_2128_, 1, v___x_2115_);
lean_ctor_set_uint8(v___x_2128_, sizeof(void*)*2, v___x_2127_);
v_a_2118_ = v___x_2128_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
lean_dec(v_a_2124_);
v___x_2129_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
v___x_2130_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_2129_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref_known(v___x_2130_, 1);
v_a_2118_ = v_a_2131_;
goto v___jp_2117_;
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v_bs_x27_2116_);
v_a_2132_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2130_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2130_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec_ref(v_bs_x27_2116_);
v_a_2140_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2123_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2123_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
v___jp_2117_:
{
size_t v___x_2119_; size_t v___x_2120_; lean_object* v___x_2121_; 
v___x_2119_ = ((size_t)1ULL);
v___x_2120_ = lean_usize_add(v_i_2105_, v___x_2119_);
v___x_2121_ = lean_array_uset(v_bs_x27_2116_, v_i_2105_, v_a_2118_);
v_i_2105_ = v___x_2120_;
v_bs_2106_ = v___x_2121_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2104_ = stack[0].m_num;
size_t v_i_2105_ = stack[1].m_num;
lean_object* v_bs_2106_ = stack[2].m_obj;
lean_object* v___y_2107_ = stack[3].m_obj;
lean_object* v___y_2108_ = stack[4].m_obj;
lean_object* v___y_2109_ = stack[5].m_obj;
lean_object* v___y_2110_ = stack[6].m_obj;
lean_object* v_res_2148_;
v_res_2148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_2104_, v_i_2105_, v_bs_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
stack->m_obj
 = v_res_2148_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object* v_sz_2149_, lean_object* v_i_2150_, lean_object* v_bs_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
size_t v_sz_boxed_2157_; size_t v_i_boxed_2158_; lean_object* v_res_2159_; 
v_sz_boxed_2157_ = lean_unbox_usize(v_sz_2149_);
lean_dec(v_sz_2149_);
v_i_boxed_2158_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_res_2159_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_2157_, v_i_boxed_2158_, v_bs_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
return v_res_2159_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2160_; lean_object* v_dummy_2161_; 
v___x_2160_ = lean_box(0);
v_dummy_2161_ = l_Lean_Expr_sort___override(v___x_2160_);
return v_dummy_2161_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2162_ = lean_box(0);
v___x_2163_ = lean_unsigned_to_nat(16u);
v___x_2164_ = lean_mk_array(v___x_2163_, v___x_2162_);
return v___x_2164_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v___x_2165_);
return v___x_2167_;
}
}
lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object* v_e_2170_, uint8_t v_alsoCasesOn_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
uint8_t v___x_2180_; 
v___x_2180_ = l_Lean_Expr_isApp(v_e_2170_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec_ref(v_e_2170_);
v___x_2181_ = lean_box(0);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
else
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lean_Expr_getAppFn(v_e_2170_);
if (lean_obj_tag(v___x_2183_) == 4)
{
lean_object* v_declName_2184_; lean_object* v_us_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2340_; 
v_declName_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc_n(v_declName_2184_, 2);
v_us_2185_ = lean_ctor_get(v___x_2183_, 1);
lean_inc(v_us_2185_);
lean_dec_ref_known(v___x_2183_, 2);
v___x_2186_ = l_Lean_instInhabitedExpr;
v___x_2187_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2184_, v___y_2175_);
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2340_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2340_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
if (lean_obj_tag(v_a_2188_) == 1)
{
lean_object* v_val_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2233_; 
v_val_2192_ = lean_ctor_get(v_a_2188_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_a_2188_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2194_ = v_a_2188_;
v_isShared_2195_ = v_isSharedCheck_2233_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_val_2192_);
lean_dec(v_a_2188_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2233_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v_dummy_2196_; lean_object* v_nargs_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v_args_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; 
v_dummy_2196_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
v_nargs_2197_ = l_Lean_Expr_getAppNumArgs(v_e_2170_);
lean_inc(v_nargs_2197_);
v___x_2198_ = lean_mk_array(v_nargs_2197_, v_dummy_2196_);
v___x_2199_ = lean_unsigned_to_nat(1u);
v___x_2200_ = lean_nat_sub(v_nargs_2197_, v___x_2199_);
lean_dec(v_nargs_2197_);
v_args_2201_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2170_, v___x_2198_, v___x_2200_);
v___x_2202_ = lean_array_get_size(v_args_2201_);
v___x_2203_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2192_);
v___x_2204_ = lean_nat_dec_lt(v___x_2202_, v___x_2203_);
lean_dec(v___x_2203_);
if (v___x_2204_ == 0)
{
lean_object* v_numParams_2205_; lean_object* v_numDiscrs_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v_numParams_2205_ = lean_ctor_get(v_val_2192_, 0);
v_numDiscrs_2206_ = lean_ctor_get(v_val_2192_, 1);
v___x_2207_ = lean_array_mk(v_us_2185_);
v___x_2208_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2205_);
v___x_2209_ = l_Array_extract___redArg(v_args_2201_, v___x_2208_, v_numParams_2205_);
v___x_2210_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2192_);
v___x_2211_ = lean_array_get(v___x_2186_, v_args_2201_, v___x_2210_);
lean_dec(v___x_2210_);
v___x_2212_ = lean_nat_add(v_numParams_2205_, v___x_2199_);
v___x_2213_ = lean_nat_add(v___x_2212_, v_numDiscrs_2206_);
lean_inc(v___x_2213_);
lean_inc_ref_n(v_args_2201_, 2);
v___x_2214_ = l_Array_toSubarray___redArg(v_args_2201_, v___x_2212_, v___x_2213_);
v___x_2215_ = l_Subarray_copy___redArg(v___x_2214_);
v___x_2216_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2192_);
v___x_2217_ = lean_nat_add(v___x_2213_, v___x_2216_);
lean_dec(v___x_2216_);
lean_inc(v___x_2217_);
v___x_2218_ = l_Array_toSubarray___redArg(v_args_2201_, v___x_2213_, v___x_2217_);
v___x_2219_ = l_Subarray_copy___redArg(v___x_2218_);
v___x_2220_ = l_Array_toSubarray___redArg(v_args_2201_, v___x_2217_, v___x_2202_);
v___x_2221_ = l_Subarray_copy___redArg(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2222_, 0, v_val_2192_);
lean_ctor_set(v___x_2222_, 1, v_declName_2184_);
lean_ctor_set(v___x_2222_, 2, v___x_2207_);
lean_ctor_set(v___x_2222_, 3, v___x_2209_);
lean_ctor_set(v___x_2222_, 4, v___x_2211_);
lean_ctor_set(v___x_2222_, 5, v___x_2215_);
lean_ctor_set(v___x_2222_, 6, v___x_2219_);
lean_ctor_set(v___x_2222_, 7, v___x_2221_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2222_);
v___x_2224_ = v___x_2194_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2226_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2224_);
v___x_2226_ = v___x_2190_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
else
{
lean_object* v___x_2229_; lean_object* v___x_2231_; 
lean_dec_ref(v_args_2201_);
lean_del_object(v___x_2194_);
lean_dec(v_val_2192_);
lean_dec(v_us_2185_);
lean_dec(v_declName_2184_);
v___x_2229_ = lean_box(0);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2229_);
v___x_2231_ = v___x_2190_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_object* v___x_2234_; 
lean_del_object(v___x_2190_);
lean_dec(v_a_2188_);
v___x_2234_ = lean_st_ref_get(v___y_2175_);
if (v_alsoCasesOn_2171_ == 0)
{
lean_dec(v___x_2234_);
lean_dec(v_us_2185_);
lean_dec(v_declName_2184_);
lean_dec_ref(v_e_2170_);
goto v___jp_2177_;
}
else
{
lean_object* v_env_2235_; uint8_t v___x_2236_; 
v_env_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_ref(v_env_2235_);
lean_dec(v___x_2234_);
lean_inc(v_declName_2184_);
v___x_2236_ = l_Lean_isCasesOnRecursor(v_env_2235_, v_declName_2184_);
if (v___x_2236_ == 0)
{
lean_dec(v_us_2185_);
lean_dec(v_declName_2184_);
lean_dec_ref(v_e_2170_);
goto v___jp_2177_;
}
else
{
lean_object* v_indName_2237_; lean_object* v___x_2238_; 
v_indName_2237_ = l_Lean_Name_getPrefix(v_declName_2184_);
v___x_2238_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_2237_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2331_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2241_ = v___x_2238_;
v_isShared_2242_ = v_isSharedCheck_2331_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2238_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2331_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
if (lean_obj_tag(v_a_2239_) == 5)
{
lean_object* v_val_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2326_; 
v_val_2243_ = lean_ctor_get(v_a_2239_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_a_2239_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2245_ = v_a_2239_;
v_isShared_2246_ = v_isSharedCheck_2326_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_val_2243_);
lean_dec(v_a_2239_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2326_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v_toConstantVal_2247_; lean_object* v_numParams_2248_; lean_object* v_numIndices_2249_; lean_object* v_ctors_2250_; lean_object* v_nargs_2251_; lean_object* v_dummy_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v_args_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; uint8_t v___x_2263_; 
v_toConstantVal_2247_ = lean_ctor_get(v_val_2243_, 0);
lean_inc_ref(v_toConstantVal_2247_);
v_numParams_2248_ = lean_ctor_get(v_val_2243_, 1);
lean_inc(v_numParams_2248_);
v_numIndices_2249_ = lean_ctor_get(v_val_2243_, 2);
lean_inc(v_numIndices_2249_);
v_ctors_2250_ = lean_ctor_get(v_val_2243_, 4);
lean_inc(v_ctors_2250_);
v_nargs_2251_ = l_Lean_Expr_getAppNumArgs(v_e_2170_);
v_dummy_2252_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
lean_inc(v_nargs_2251_);
v___x_2253_ = lean_mk_array(v_nargs_2251_, v_dummy_2252_);
v___x_2254_ = lean_unsigned_to_nat(1u);
v___x_2255_ = lean_nat_sub(v_nargs_2251_, v___x_2254_);
lean_dec(v_nargs_2251_);
v_args_2256_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2170_, v___x_2253_, v___x_2255_);
v___x_2257_ = lean_nat_add(v_numParams_2248_, v___x_2254_);
v___x_2258_ = lean_nat_add(v___x_2257_, v_numIndices_2249_);
v___x_2259_ = lean_nat_add(v___x_2258_, v___x_2254_);
lean_dec(v___x_2258_);
v___x_2260_ = l_Lean_InductiveVal_numCtors(v_val_2243_);
lean_dec_ref(v_val_2243_);
v___x_2261_ = lean_nat_add(v___x_2259_, v___x_2260_);
lean_dec(v___x_2260_);
v___x_2262_ = lean_array_get_size(v_args_2256_);
v___x_2263_ = lean_nat_dec_le(v___x_2261_, v___x_2262_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
lean_dec(v___x_2261_);
lean_dec(v___x_2259_);
lean_dec(v___x_2257_);
lean_dec_ref(v_args_2256_);
lean_dec(v_ctors_2250_);
lean_dec(v_numIndices_2249_);
lean_dec(v_numParams_2248_);
lean_dec_ref(v_toConstantVal_2247_);
lean_del_object(v___x_2245_);
lean_dec(v_us_2185_);
lean_dec(v_declName_2184_);
v___x_2264_ = lean_box(0);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2264_);
v___x_2266_ = v___x_2241_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
else
{
lean_object* v___x_2268_; lean_object* v_params_2269_; lean_object* v_motive_2270_; lean_object* v_discrs_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v_discrInfos_2274_; lean_object* v_alts_2275_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v_lower_2317_; lean_object* v_upper_2318_; uint8_t v___x_2325_; 
lean_del_object(v___x_2241_);
v___x_2268_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2248_);
lean_inc_ref_n(v_args_2256_, 3);
v_params_2269_ = l_Array_toSubarray___redArg(v_args_2256_, v___x_2268_, v_numParams_2248_);
v_motive_2270_ = lean_array_get(v___x_2186_, v_args_2256_, v_numParams_2248_);
lean_dec(v_numParams_2248_);
lean_inc(v___x_2259_);
v_discrs_2271_ = l_Array_toSubarray___redArg(v_args_2256_, v___x_2257_, v___x_2259_);
v___x_2272_ = lean_nat_add(v_numIndices_2249_, v___x_2254_);
lean_dec(v_numIndices_2249_);
v___x_2273_ = lean_box(0);
v_discrInfos_2274_ = lean_mk_array(v___x_2272_, v___x_2273_);
lean_inc(v___x_2261_);
v_alts_2275_ = l_Array_toSubarray___redArg(v_args_2256_, v___x_2259_, v___x_2261_);
v___x_2325_ = lean_nat_dec_le(v___x_2261_, v___x_2268_);
if (v___x_2325_ == 0)
{
v_lower_2317_ = v___x_2261_;
v_upper_2318_ = v___x_2262_;
goto v___jp_2316_;
}
else
{
lean_dec(v___x_2261_);
v_lower_2317_ = v___x_2268_;
v_upper_2318_ = v___x_2262_;
goto v___jp_2316_;
}
v___jp_2276_:
{
lean_object* v___x_2279_; size_t v_sz_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
v___x_2279_ = lean_array_mk(v_ctors_2250_);
v_sz_2280_ = lean_array_size(v___x_2279_);
v___x_2281_ = ((size_t)0ULL);
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_2280_, v___x_2281_, v___x_2279_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2307_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2285_ = v___x_2282_;
v_isShared_2286_ = v_isSharedCheck_2307_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2307_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v_start_2287_; lean_object* v_stop_2288_; lean_object* v_start_2289_; lean_object* v_stop_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
v_start_2287_ = lean_ctor_get(v_params_2269_, 1);
v_stop_2288_ = lean_ctor_get(v_params_2269_, 2);
v_start_2289_ = lean_ctor_get(v_discrs_2271_, 1);
v_stop_2290_ = lean_ctor_get(v_discrs_2271_, 2);
v___x_2291_ = lean_nat_sub(v_stop_2288_, v_start_2287_);
v___x_2292_ = lean_nat_sub(v_stop_2290_, v_start_2289_);
v___x_2293_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2);
v___x_2294_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2291_);
lean_ctor_set(v___x_2294_, 1, v___x_2292_);
lean_ctor_set(v___x_2294_, 2, v_a_2283_);
lean_ctor_set(v___x_2294_, 3, v___y_2278_);
lean_ctor_set(v___x_2294_, 4, v_discrInfos_2274_);
lean_ctor_set(v___x_2294_, 5, v___x_2293_);
v___x_2295_ = lean_array_mk(v_us_2185_);
v___x_2296_ = l_Subarray_copy___redArg(v_params_2269_);
v___x_2297_ = l_Subarray_copy___redArg(v_discrs_2271_);
v___x_2298_ = l_Subarray_copy___redArg(v_alts_2275_);
v___x_2299_ = l_Subarray_copy___redArg(v___y_2277_);
v___x_2300_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2294_);
lean_ctor_set(v___x_2300_, 1, v_declName_2184_);
lean_ctor_set(v___x_2300_, 2, v___x_2295_);
lean_ctor_set(v___x_2300_, 3, v___x_2296_);
lean_ctor_set(v___x_2300_, 4, v_motive_2270_);
lean_ctor_set(v___x_2300_, 5, v___x_2297_);
lean_ctor_set(v___x_2300_, 6, v___x_2298_);
lean_ctor_set(v___x_2300_, 7, v___x_2299_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set_tag(v___x_2245_, 1);
lean_ctor_set(v___x_2245_, 0, v___x_2300_);
v___x_2302_ = v___x_2245_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2304_; 
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2302_);
v___x_2304_ = v___x_2285_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v_alts_2275_);
lean_dec_ref(v_discrInfos_2274_);
lean_dec_ref(v_discrs_2271_);
lean_dec(v_motive_2270_);
lean_dec_ref(v_params_2269_);
lean_del_object(v___x_2245_);
lean_dec(v_us_2185_);
lean_dec(v_declName_2184_);
v_a_2308_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2282_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2282_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
v___jp_2316_:
{
lean_object* v_levelParams_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; uint8_t v___x_2323_; 
v_levelParams_2319_ = lean_ctor_get(v_toConstantVal_2247_, 1);
lean_inc(v_levelParams_2319_);
lean_dec_ref(v_toConstantVal_2247_);
v___x_2320_ = l_Array_toSubarray___redArg(v_args_2256_, v_lower_2317_, v_upper_2318_);
v___x_2321_ = l_List_lengthTR___redArg(v_levelParams_2319_);
lean_dec(v_levelParams_2319_);
v___x_2322_ = l_List_lengthTR___redArg(v_us_2185_);
v___x_2323_ = lean_nat_dec_eq(v___x_2321_, v___x_2322_);
lean_dec(v___x_2322_);
lean_dec(v___x_2321_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; 
v___x_2324_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3));
v___y_2277_ = v___x_2320_;
v___y_2278_ = v___x_2324_;
goto v___jp_2276_;
}
else
{
v___y_2277_ = v___x_2320_;
v___y_2278_ = v___x_2273_;
goto v___jp_2276_;
}
}
}
}
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2329_; 
lean_dec(v_a_2239_);
lean_dec(v_us_2185_);
lean_dec(v_declName_2184_);
lean_dec_ref(v_e_2170_);
v___x_2327_ = lean_box(0);
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 0, v___x_2327_);
v___x_2329_ = v___x_2241_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_us_2185_);
lean_dec(v_declName_2184_);
lean_dec_ref(v_e_2170_);
v_a_2332_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2238_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2238_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
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
lean_dec_ref(v___x_2183_);
lean_dec_ref(v_e_2170_);
goto v___jp_2177_;
}
}
v___jp_2177_:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
return v___x_2179_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2170_ = stack[0].m_obj;
uint8_t v_alsoCasesOn_2171_ = stack[1].m_num;
lean_object* v___y_2172_ = stack[2].m_obj;
lean_object* v___y_2173_ = stack[3].m_obj;
lean_object* v___y_2174_ = stack[4].m_obj;
lean_object* v___y_2175_ = stack[5].m_obj;
lean_object* v_res_2341_;
v_res_2341_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_2170_, v_alsoCasesOn_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
stack->m_obj
 = v_res_2341_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object* v_e_2342_, lean_object* v_alsoCasesOn_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2349_; lean_object* v_res_2350_; 
v_alsoCasesOn_boxed_2349_ = lean_unbox(v_alsoCasesOn_2343_);
v_res_2350_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_2342_, v_alsoCasesOn_boxed_2349_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
return v_res_2350_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object* v_e_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_){
_start:
{
lean_object* v___x_2357_; uint8_t v___x_2358_; 
v___x_2357_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2358_ = l_Lean_Expr_isAppOf(v_e_2351_, v___x_2357_);
if (v___x_2358_ == 0)
{
lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2359_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2360_ = l_Lean_Expr_isAppOf(v_e_2351_, v___x_2359_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; uint8_t v___x_2362_; 
v___x_2361_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_2362_ = l_Lean_Expr_isAppOf(v_e_2351_, v___x_2361_);
if (v___x_2362_ == 0)
{
uint8_t v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = 1;
v___x_2364_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_2351_, v___x_2363_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2385_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2367_ = v___x_2364_;
v_isShared_2368_ = v_isSharedCheck_2385_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2385_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
if (lean_obj_tag(v_a_2365_) == 1)
{
lean_object* v_val_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2380_; 
v_val_2369_ = lean_ctor_get(v_a_2365_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_a_2365_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2371_ = v_a_2365_;
v_isShared_2372_ = v_isSharedCheck_2380_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_val_2369_);
lean_dec(v_a_2365_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2380_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v___x_2375_; 
v___x_2373_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2373_, 0, v_val_2369_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 0, v___x_2373_);
v___x_2375_ = v___x_2371_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2377_; 
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2375_);
v___x_2377_ = v___x_2367_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v___x_2375_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_dec(v_a_2365_);
v___x_2381_ = lean_box(0);
if (v_isShared_2368_ == 0)
{
lean_ctor_set(v___x_2367_, 0, v___x_2381_);
v___x_2383_ = v___x_2367_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
return v___x_2383_;
}
}
}
}
else
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2393_; 
v_a_2386_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2388_ = v___x_2364_;
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2364_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2393_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2391_; 
if (v_isShared_2389_ == 0)
{
v___x_2391_ = v___x_2388_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2386_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
else
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2394_, 0, v_e_2351_);
v___x_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
return v___x_2396_;
}
}
else
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2397_, 0, v_e_2351_);
v___x_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2398_, 0, v___x_2397_);
v___x_2399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
return v___x_2399_;
}
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v_e_2351_);
v___x_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
return v___x_2402_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_getSplitInfo_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2351_ = stack[0].m_obj;
lean_object* v_a_2352_ = stack[1].m_obj;
lean_object* v_a_2353_ = stack[2].m_obj;
lean_object* v_a_2354_ = stack[3].m_obj;
lean_object* v_a_2355_ = stack[4].m_obj;
lean_object* v_res_2403_;
v_res_2403_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_2351_, v_a_2352_, v_a_2353_, v_a_2354_, v_a_2355_);
stack->m_obj
 = v_res_2403_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object* v_e_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2410_;
}
}
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object* v_declName_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2411_, v___y_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT void l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_2411_ = stack[0].m_obj;
lean_object* v___y_2412_ = stack[1].m_obj;
lean_object* v___y_2413_ = stack[2].m_obj;
lean_object* v___y_2414_ = stack[3].m_obj;
lean_object* v___y_2415_ = stack[4].m_obj;
lean_object* v_res_2418_;
v_res_2418_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
stack->m_obj
 = v_res_2418_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object* v_declName_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2425_;
}
}
lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2426_, lean_object* v_constName_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_constName_2427_ = stack[1].m_obj;
lean_object* v___y_2428_ = stack[2].m_obj;
lean_object* v___y_2429_ = stack[3].m_obj;
lean_object* v___y_2430_ = stack[4].m_obj;
lean_object* v___y_2431_ = stack[5].m_obj;
lean_object* v_res_2434_;
v_res_2434_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_box(0), v_constName_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
stack->m_obj
 = v_res_2434_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2435_, lean_object* v_constName_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2435_, v_constName_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v_res_2442_;
}
}
lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2443_, lean_object* v_ref_2444_, lean_object* v_constName_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2444_, v_constName_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2444_ = stack[1].m_obj;
lean_object* v_constName_2445_ = stack[2].m_obj;
lean_object* v___y_2446_ = stack[3].m_obj;
lean_object* v___y_2447_ = stack[4].m_obj;
lean_object* v___y_2448_ = stack[5].m_obj;
lean_object* v___y_2449_ = stack[6].m_obj;
lean_object* v_res_2452_;
v_res_2452_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_box(0), v_ref_2444_, v_constName_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
stack->m_obj
 = v_res_2452_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2453_, lean_object* v_ref_2454_, lean_object* v_constName_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2453_, v_ref_2454_, v_constName_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v_ref_2454_);
return v_res_2461_;
}
}
lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2462_, lean_object* v_ref_2463_, lean_object* v_msg_2464_, lean_object* v_declHint_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2463_, v_msg_2464_, v_declHint_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT void l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2463_ = stack[1].m_obj;
lean_object* v_msg_2464_ = stack[2].m_obj;
lean_object* v_declHint_2465_ = stack[3].m_obj;
lean_object* v___y_2466_ = stack[4].m_obj;
lean_object* v___y_2467_ = stack[5].m_obj;
lean_object* v___y_2468_ = stack[6].m_obj;
lean_object* v___y_2469_ = stack[7].m_obj;
lean_object* v_res_2472_;
v_res_2472_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_box(0), v_ref_2463_, v_msg_2464_, v_declHint_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
stack->m_obj
 = v_res_2472_;
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2473_, lean_object* v_ref_2474_, lean_object* v_msg_2475_, lean_object* v_declHint_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2473_, v_ref_2474_, v_msg_2475_, v_declHint_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v_ref_2474_);
return v_res_2482_;
}
}
lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_2483_, lean_object* v_declHint_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2483_, v_declHint_2484_, v___y_2488_);
return v___x_2490_;
}
}
LEAN_EXPORT void l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2483_ = stack[0].m_obj;
lean_object* v_declHint_2484_ = stack[1].m_obj;
lean_object* v___y_2485_ = stack[2].m_obj;
lean_object* v___y_2486_ = stack[3].m_obj;
lean_object* v___y_2487_ = stack[4].m_obj;
lean_object* v___y_2488_ = stack[5].m_obj;
lean_object* v_res_2491_;
v_res_2491_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_2483_, v_declHint_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_);
stack->m_obj
 = v_res_2491_;
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_2492_, lean_object* v_declHint_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_2492_, v_declHint_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2499_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2500_, lean_object* v_ref_2501_, lean_object* v_msg_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_2501_, v_msg_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
return v___x_2508_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_2501_ = stack[1].m_obj;
lean_object* v_msg_2502_ = stack[2].m_obj;
lean_object* v___y_2503_ = stack[3].m_obj;
lean_object* v___y_2504_ = stack[4].m_obj;
lean_object* v___y_2505_ = stack[5].m_obj;
lean_object* v___y_2506_ = stack[6].m_obj;
lean_object* v_res_2509_;
v_res_2509_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_box(0), v_ref_2501_, v_msg_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
stack->m_obj
 = v_res_2509_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2510_, lean_object* v_ref_2511_, lean_object* v_msg_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2510_, v_ref_2511_, v_msg_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v_ref_2511_);
return v_res_2518_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_2519_, lean_object* v_msg_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v___x_2526_; 
v___x_2526_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
return v___x_2526_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2520_ = stack[1].m_obj;
lean_object* v___y_2521_ = stack[2].m_obj;
lean_object* v___y_2522_ = stack[3].m_obj;
lean_object* v___y_2523_ = stack[4].m_obj;
lean_object* v___y_2524_ = stack[5].m_obj;
lean_object* v_res_2527_;
v_res_2527_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_box(0), v_msg_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
stack->m_obj
 = v_res_2527_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2528_, lean_object* v_msg_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_2528_, v_msg_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_);
lean_dec(v___y_2533_);
lean_dec_ref(v___y_2532_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
return v_res_2535_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0));
v___x_2538_ = l_Lean_stringToMessageData(v___x_2537_);
return v___x_2538_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__2));
v___x_2541_ = l_Lean_stringToMessageData(v___x_2540_);
return v___x_2541_;
}
}
lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object* v_idx_2545_, lean_object* v_e_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v___y_2553_; lean_object* v___y_2572_; lean_object* v___y_2573_; uint8_t v___y_2604_; lean_object* v___x_2625_; uint8_t v___x_2626_; 
v___x_2625_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2626_ = l_Lean_Expr_isAppOf(v_e_2546_, v___x_2625_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2628_ = l_Lean_Expr_isAppOf(v_e_2546_, v___x_2627_);
v___y_2604_ = v___x_2628_;
goto v___jp_2603_;
}
else
{
v___y_2604_ = v___x_2626_;
goto v___jp_2603_;
}
v___jp_2552_:
{
lean_object* v___x_2554_; 
lean_inc_ref(v___y_2553_);
v___x_2554_ = l_Lean_Meta_findLocalDeclWithType_x3f(v___y_2553_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2554_, 1);
if (lean_obj_tag(v_a_2555_) == 1)
{
lean_object* v_val_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; 
lean_dec_ref(v___y_2553_);
v_val_2556_ = lean_ctor_get(v_a_2555_, 0);
lean_inc(v_val_2556_);
lean_dec_ref_known(v_a_2555_, 1);
v___x_2557_ = l_Lean_mkFVar(v_val_2556_);
v___x_2558_ = l_Lean_Meta_rwIfWith(v___x_2557_, v_e_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2558_;
}
else
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
lean_dec(v_a_2555_);
lean_dec_ref(v_e_2546_);
v___x_2559_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1);
v___x_2560_ = l_Lean_MessageData_ofExpr(v___y_2553_);
v___x_2561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2559_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2561_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2562_;
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v___y_2553_);
lean_dec_ref(v_e_2546_);
v_a_2563_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2554_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2554_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
v___jp_2571_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = lean_box(0);
lean_inc(v___y_2573_);
v___x_2575_ = l_Lean_mkConst(v___y_2573_, v___x_2574_);
v___x_2576_ = l_Lean_Meta_mkEq(v___y_2572_, v___x_2575_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2578_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc_n(v_a_2577_, 2);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_a_2577_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
if (lean_obj_tag(v___x_2578_) == 0)
{
lean_object* v_a_2579_; 
v_a_2579_ = lean_ctor_get(v___x_2578_, 0);
lean_inc(v_a_2579_);
lean_dec_ref_known(v___x_2578_, 1);
if (lean_obj_tag(v_a_2579_) == 1)
{
lean_object* v_val_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
lean_dec(v_a_2577_);
v_val_2580_ = lean_ctor_get(v_a_2579_, 0);
lean_inc(v_val_2580_);
lean_dec_ref_known(v_a_2579_, 1);
v___x_2581_ = l_Lean_mkFVar(v_val_2580_);
v___x_2582_ = l_Lean_Meta_rwIfWith(v___x_2581_, v_e_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2582_;
}
else
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec(v_a_2579_);
lean_dec_ref(v_e_2546_);
v___x_2583_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3);
v___x_2584_ = l_Lean_MessageData_ofExpr(v_a_2577_);
v___x_2585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2583_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___x_2586_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2585_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2586_;
}
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec(v_a_2577_);
lean_dec_ref(v_e_2546_);
v_a_2587_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2578_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2578_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v_e_2546_);
v_a_2595_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2576_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2576_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
v___jp_2603_:
{
if (v___y_2604_ == 0)
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_2606_ = l_Lean_Expr_isAppOf(v_e_2546_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Lean_Meta_rwMatcher(v_idx_2545_, v_e_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
return v___x_2607_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v_c_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
v___x_2608_ = lean_unsigned_to_nat(1u);
v___x_2609_ = l_Lean_Expr_getAppNumArgs(v_e_2546_);
v___x_2610_ = lean_nat_sub(v___x_2609_, v___x_2608_);
lean_dec(v___x_2609_);
v___x_2611_ = lean_nat_sub(v___x_2610_, v___x_2608_);
lean_dec(v___x_2610_);
v_c_2612_ = l_Lean_Expr_getRevArg_x21(v_e_2546_, v___x_2611_);
v___x_2613_ = lean_unsigned_to_nat(0u);
v___x_2614_ = lean_nat_dec_eq(v_idx_2545_, v___x_2613_);
lean_dec(v_idx_2545_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; 
v___x_2615_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4));
v___y_2572_ = v_c_2612_;
v___y_2573_ = v___x_2615_;
goto v___jp_2571_;
}
else
{
lean_object* v___x_2616_; 
v___x_2616_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1));
v___y_2572_ = v_c_2612_;
v___y_2573_ = v___x_2616_;
goto v___jp_2571_;
}
}
}
else
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v_c_2621_; lean_object* v___x_2622_; uint8_t v___x_2623_; 
v___x_2617_ = lean_unsigned_to_nat(1u);
v___x_2618_ = l_Lean_Expr_getAppNumArgs(v_e_2546_);
v___x_2619_ = lean_nat_sub(v___x_2618_, v___x_2617_);
lean_dec(v___x_2618_);
v___x_2620_ = lean_nat_sub(v___x_2619_, v___x_2617_);
lean_dec(v___x_2619_);
v_c_2621_ = l_Lean_Expr_getRevArg_x21(v_e_2546_, v___x_2620_);
v___x_2622_ = lean_unsigned_to_nat(0u);
v___x_2623_ = lean_nat_dec_eq(v_idx_2545_, v___x_2622_);
lean_dec(v_idx_2545_);
if (v___x_2623_ == 0)
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Lean_mkNot(v_c_2621_);
v___y_2553_ = v___x_2624_;
goto v___jp_2552_;
}
else
{
v___y_2553_ = v_c_2621_;
goto v___jp_2552_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_Do_rwIfOrMatcher_0interp(lean_interpreter_value* stack)
{
lean_object* v_idx_2545_ = stack[0].m_obj;
lean_object* v_e_2546_ = stack[1].m_obj;
lean_object* v_a_2547_ = stack[2].m_obj;
lean_object* v_a_2548_ = stack[3].m_obj;
lean_object* v_a_2549_ = stack[4].m_obj;
lean_object* v_a_2550_ = stack[5].m_obj;
lean_object* v_res_2629_;
v_res_2629_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(v_idx_2545_, v_e_2546_, v_a_2547_, v_a_2548_, v_a_2549_, v_a_2550_);
stack->m_obj
 = v_res_2629_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object* v_idx_2630_, lean_object* v_e_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_){
_start:
{
lean_object* v_res_2637_; 
v_res_2637_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(v_idx_2630_, v_e_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
return v_res_2637_;
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
