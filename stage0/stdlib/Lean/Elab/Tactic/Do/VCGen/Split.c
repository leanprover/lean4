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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object* v_matcherApp_110_, size_t v_sz_111_, size_t v_i_112_, lean_object* v_bs_113_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object* v_matcherApp_127_, lean_object* v_sz_128_, lean_object* v_i_129_, lean_object* v_bs_130_){
_start:
{
size_t v_sz_boxed_131_; size_t v_i_boxed_132_; lean_object* v_res_133_; 
v_sz_boxed_131_ = lean_unbox_usize(v_sz_128_);
lean_dec(v_sz_128_);
v_i_boxed_132_ = lean_unbox_usize(v_i_129_);
lean_dec(v_i_129_);
v_res_133_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_127_, v_sz_boxed_131_, v_i_boxed_132_, v_bs_130_);
lean_dec_ref(v_matcherApp_127_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object* v_info_134_){
_start:
{
switch(lean_obj_tag(v_info_134_))
{
case 0:
{
lean_object* v_e_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v_e_135_ = lean_ctor_get(v_info_134_, 0);
lean_inc_ref(v_e_135_);
lean_dec_ref_known(v_info_134_, 1);
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = lean_unsigned_to_nat(3u);
v___x_138_ = l_Lean_Expr_getAppNumArgs(v_e_135_);
v___x_139_ = lean_nat_sub(v___x_138_, v___x_137_);
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_sub(v___x_139_, v___x_140_);
lean_dec(v___x_139_);
v___x_142_ = l_Lean_Expr_getRevArg_x21(v_e_135_, v___x_141_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_136_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = lean_unsigned_to_nat(4u);
v___x_145_ = lean_nat_sub(v___x_138_, v___x_144_);
lean_dec(v___x_138_);
v___x_146_ = lean_nat_sub(v___x_145_, v___x_140_);
lean_dec(v___x_145_);
v___x_147_ = l_Lean_Expr_getRevArg_x21(v_e_135_, v___x_146_);
lean_dec_ref(v_e_135_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_136_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = lean_unsigned_to_nat(2u);
v___x_150_ = lean_mk_empty_array_with_capacity(v___x_149_);
v___x_151_ = lean_array_push(v___x_150_, v___x_143_);
v___x_152_ = lean_array_push(v___x_151_, v___x_148_);
return v___x_152_;
}
case 1:
{
lean_object* v_e_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v_e_153_ = lean_ctor_get(v_info_134_, 0);
lean_inc_ref(v_e_153_);
lean_dec_ref_known(v_info_134_, 1);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_unsigned_to_nat(3u);
v___x_156_ = l_Lean_Expr_getAppNumArgs(v_e_153_);
v___x_157_ = lean_nat_sub(v___x_156_, v___x_155_);
v___x_158_ = lean_nat_sub(v___x_157_, v___x_154_);
lean_dec(v___x_157_);
v___x_159_ = l_Lean_Expr_getRevArg_x21(v_e_153_, v___x_158_);
v___x_160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_154_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_unsigned_to_nat(4u);
v___x_162_ = lean_nat_sub(v___x_156_, v___x_161_);
lean_dec(v___x_156_);
v___x_163_ = lean_nat_sub(v___x_162_, v___x_154_);
lean_dec(v___x_162_);
v___x_164_ = l_Lean_Expr_getRevArg_x21(v_e_153_, v___x_163_);
lean_dec_ref(v_e_153_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_154_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_unsigned_to_nat(2u);
v___x_167_ = lean_mk_empty_array_with_capacity(v___x_166_);
v___x_168_ = lean_array_push(v___x_167_, v___x_160_);
v___x_169_ = lean_array_push(v___x_168_, v___x_165_);
return v___x_169_;
}
case 2:
{
lean_object* v_e_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_e_170_ = lean_ctor_get(v_info_134_, 0);
lean_inc_ref(v_e_170_);
lean_dec_ref_known(v_info_134_, 1);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_unsigned_to_nat(2u);
v___x_173_ = l_Lean_Expr_getAppNumArgs(v_e_170_);
v___x_174_ = lean_nat_sub(v___x_173_, v___x_172_);
v___x_175_ = lean_unsigned_to_nat(1u);
v___x_176_ = lean_nat_sub(v___x_174_, v___x_175_);
lean_dec(v___x_174_);
v___x_177_ = l_Lean_Expr_getRevArg_x21(v_e_170_, v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_171_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = lean_unsigned_to_nat(3u);
v___x_180_ = lean_nat_sub(v___x_173_, v___x_179_);
lean_dec(v___x_173_);
v___x_181_ = lean_nat_sub(v___x_180_, v___x_175_);
lean_dec(v___x_180_);
v___x_182_ = l_Lean_Expr_getRevArg_x21(v_e_170_, v___x_181_);
lean_dec_ref(v_e_170_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_171_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_mk_empty_array_with_capacity(v___x_172_);
v___x_185_ = lean_array_push(v___x_184_, v___x_178_);
v___x_186_ = lean_array_push(v___x_185_, v___x_183_);
return v___x_186_;
}
default: 
{
lean_object* v_matcherApp_187_; lean_object* v___x_188_; size_t v_sz_189_; size_t v___x_190_; lean_object* v___x_191_; 
v_matcherApp_187_ = lean_ctor_get(v_info_134_, 0);
lean_inc_ref_n(v_matcherApp_187_, 2);
lean_dec_ref_known(v_info_134_, 1);
v___x_188_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_187_);
v_sz_189_ = lean_array_size(v___x_188_);
v___x_190_ = ((size_t)0ULL);
v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_187_, v_sz_189_, v___x_190_, v___x_188_);
lean_dec_ref(v_matcherApp_187_);
return v___x_191_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object* v_matcherApp_192_, lean_object* v_as_193_, size_t v_sz_194_, size_t v_i_195_, lean_object* v_bs_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_192_, v_sz_194_, v_i_195_, v_bs_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object* v_matcherApp_198_, lean_object* v_as_199_, lean_object* v_sz_200_, lean_object* v_i_201_, lean_object* v_bs_202_){
_start:
{
size_t v_sz_boxed_203_; size_t v_i_boxed_204_; lean_object* v_res_205_; 
v_sz_boxed_203_ = lean_unbox_usize(v_sz_200_);
lean_dec(v_sz_200_);
v_i_boxed_204_ = lean_unbox_usize(v_i_201_);
lean_dec(v_i_201_);
v_res_205_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(v_matcherApp_198_, v_as_199_, v_sz_boxed_203_, v_i_boxed_204_, v_bs_202_);
lean_dec_ref(v_as_199_);
lean_dec_ref(v_matcherApp_198_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_expr(lean_object* v_x_206_){
_start:
{
if (lean_obj_tag(v_x_206_) == 3)
{
lean_object* v_matcherApp_207_; lean_object* v___x_208_; 
v_matcherApp_207_ = lean_ctor_get(v_x_206_, 0);
lean_inc_ref(v_matcherApp_207_);
lean_dec_ref_known(v_x_206_, 1);
v___x_208_ = l_Lean_Meta_MatcherApp_toExpr(v_matcherApp_207_);
return v___x_208_;
}
else
{
lean_object* v_e_209_; 
v_e_209_ = lean_ctor_get(v_x_206_, 0);
lean_inc_ref(v_e_209_);
lean_dec_ref(v_x_206_);
return v_e_209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0(lean_object* v___x_213_, lean_object* v_resTy_214_, lean_object* v_c_215_, lean_object* v_dec_216_, lean_object* v_t_217_, lean_object* v_e_218_, lean_object* v_k_219_, lean_object* v_u_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_221_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_222_, 0, v_u_220_);
lean_ctor_set(v___x_222_, 1, v___x_213_);
v___x_223_ = l_Lean_mkConst(v___x_221_, v___x_222_);
lean_inc_ref(v_e_218_);
lean_inc_ref(v_t_217_);
lean_inc_ref(v_dec_216_);
lean_inc_ref(v_c_215_);
v___x_224_ = l_Lean_mkApp5(v___x_223_, v_resTy_214_, v_c_215_, v_dec_216_, v_t_217_, v_e_218_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
v___x_226_ = lean_unsigned_to_nat(4u);
v___x_227_ = lean_mk_empty_array_with_capacity(v___x_226_);
v___x_228_ = lean_array_push(v___x_227_, v_c_215_);
v___x_229_ = lean_array_push(v___x_228_, v_dec_216_);
v___x_230_ = lean_array_push(v___x_229_, v_t_217_);
v___x_231_ = lean_array_push(v___x_230_, v_e_218_);
v___x_232_ = lean_apply_2(v_k_219_, v___x_225_, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1(lean_object* v___x_233_, lean_object* v_resTy_234_, lean_object* v_c_235_, lean_object* v_dec_236_, lean_object* v_t_237_, lean_object* v_k_238_, lean_object* v_inst_239_, lean_object* v_toBind_240_, lean_object* v_e_241_){
_start:
{
lean_object* v___f_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_inc_ref(v_resTy_234_);
v___f_242_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0), 8, 7);
lean_closure_set(v___f_242_, 0, v___x_233_);
lean_closure_set(v___f_242_, 1, v_resTy_234_);
lean_closure_set(v___f_242_, 2, v_c_235_);
lean_closure_set(v___f_242_, 3, v_dec_236_);
lean_closure_set(v___f_242_, 4, v_t_237_);
lean_closure_set(v___f_242_, 5, v_e_241_);
lean_closure_set(v___f_242_, 6, v_k_238_);
v___x_243_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_243_, 0, v_resTy_234_);
v___x_244_ = lean_apply_2(v_inst_239_, lean_box(0), v___x_243_);
v___x_245_ = lean_apply_4(v_toBind_240_, lean_box(0), lean_box(0), v___x_244_, v___f_242_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2(lean_object* v___x_249_, lean_object* v_resTy_250_, lean_object* v_c_251_, lean_object* v_dec_252_, lean_object* v_k_253_, lean_object* v_inst_254_, lean_object* v_toBind_255_, lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_t_258_){
_start:
{
lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_inc_ref(v_resTy_250_);
v___f_259_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1), 9, 8);
lean_closure_set(v___f_259_, 0, v___x_249_);
lean_closure_set(v___f_259_, 1, v_resTy_250_);
lean_closure_set(v___f_259_, 2, v_c_251_);
lean_closure_set(v___f_259_, 3, v_dec_252_);
lean_closure_set(v___f_259_, 4, v_t_258_);
lean_closure_set(v___f_259_, 5, v_k_253_);
lean_closure_set(v___f_259_, 6, v_inst_254_);
lean_closure_set(v___f_259_, 7, v_toBind_255_);
v___x_260_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_261_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_256_, v_inst_257_, v___x_260_, v_resTy_250_, v___f_259_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3(lean_object* v___x_265_, lean_object* v_resTy_266_, lean_object* v_c_267_, lean_object* v_k_268_, lean_object* v_inst_269_, lean_object* v_toBind_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_dec_273_){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
lean_inc_ref(v_inst_272_);
lean_inc_ref(v_inst_271_);
lean_inc_ref(v_resTy_266_);
v___f_274_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2), 10, 9);
lean_closure_set(v___f_274_, 0, v___x_265_);
lean_closure_set(v___f_274_, 1, v_resTy_266_);
lean_closure_set(v___f_274_, 2, v_c_267_);
lean_closure_set(v___f_274_, 3, v_dec_273_);
lean_closure_set(v___f_274_, 4, v_k_268_);
lean_closure_set(v___f_274_, 5, v_inst_269_);
lean_closure_set(v___f_274_, 6, v_toBind_270_);
lean_closure_set(v___f_274_, 7, v_inst_271_);
lean_closure_set(v___f_274_, 8, v_inst_272_);
v___x_275_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_276_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_271_, v_inst_272_, v___x_275_, v_resTy_266_, v___f_274_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_box(0);
v___x_284_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3));
v___x_285_ = l_Lean_mkConst(v___x_284_, v___x_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4(lean_object* v_resTy_286_, lean_object* v_k_287_, lean_object* v_inst_288_, lean_object* v_toBind_289_, lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_c_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___f_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_293_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_294_ = lean_box(0);
lean_inc_ref(v_inst_291_);
lean_inc_ref(v_inst_290_);
lean_inc_ref(v_c_292_);
v___f_295_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3), 9, 8);
lean_closure_set(v___f_295_, 0, v___x_294_);
lean_closure_set(v___f_295_, 1, v_resTy_286_);
lean_closure_set(v___f_295_, 2, v_c_292_);
lean_closure_set(v___f_295_, 3, v_k_287_);
lean_closure_set(v___f_295_, 4, v_inst_288_);
lean_closure_set(v___f_295_, 5, v_toBind_289_);
lean_closure_set(v___f_295_, 6, v_inst_290_);
lean_closure_set(v___f_295_, 7, v_inst_291_);
v___x_296_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_297_ = l_Lean_Expr_app___override(v___x_296_, v_c_292_);
v___x_298_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_290_, v_inst_291_, v___x_293_, v___x_297_, v___f_295_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(lean_object* v_c_299_, lean_object* v_resTy_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_mkArrow(v_c_299_, v_resTy_300_, v___y_303_, v___y_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed(lean_object* v_c_307_, lean_object* v_resTy_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(v_c_307_, v_resTy_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6(lean_object* v___x_318_, lean_object* v_resTy_319_, lean_object* v_c_320_, lean_object* v_dec_321_, lean_object* v_t_322_, lean_object* v_e_323_, lean_object* v_k_324_, lean_object* v_u_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_326_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_327_, 0, v_u_325_);
lean_ctor_set(v___x_327_, 1, v___x_318_);
v___x_328_ = l_Lean_mkConst(v___x_326_, v___x_327_);
lean_inc_ref(v_e_323_);
lean_inc_ref(v_t_322_);
lean_inc_ref(v_dec_321_);
lean_inc_ref(v_c_320_);
v___x_329_ = l_Lean_mkApp5(v___x_328_, v_resTy_319_, v_c_320_, v_dec_321_, v_t_322_, v_e_323_);
v___x_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
v___x_331_ = lean_unsigned_to_nat(4u);
v___x_332_ = lean_mk_empty_array_with_capacity(v___x_331_);
v___x_333_ = lean_array_push(v___x_332_, v_c_320_);
v___x_334_ = lean_array_push(v___x_333_, v_dec_321_);
v___x_335_ = lean_array_push(v___x_334_, v_t_322_);
v___x_336_ = lean_array_push(v___x_335_, v_e_323_);
v___x_337_ = lean_apply_2(v_k_324_, v___x_330_, v___x_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7(lean_object* v___x_338_, lean_object* v_resTy_339_, lean_object* v_c_340_, lean_object* v_dec_341_, lean_object* v_t_342_, lean_object* v_k_343_, lean_object* v_inst_344_, lean_object* v_toBind_345_, lean_object* v_e_346_){
_start:
{
lean_object* v___f_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_inc_ref(v_resTy_339_);
v___f_347_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6), 8, 7);
lean_closure_set(v___f_347_, 0, v___x_338_);
lean_closure_set(v___f_347_, 1, v_resTy_339_);
lean_closure_set(v___f_347_, 2, v_c_340_);
lean_closure_set(v___f_347_, 3, v_dec_341_);
lean_closure_set(v___f_347_, 4, v_t_342_);
lean_closure_set(v___f_347_, 5, v_e_346_);
lean_closure_set(v___f_347_, 6, v_k_343_);
v___x_348_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_348_, 0, v_resTy_339_);
v___x_349_ = lean_apply_2(v_inst_344_, lean_box(0), v___x_348_);
v___x_350_ = lean_apply_4(v_toBind_345_, lean_box(0), lean_box(0), v___x_349_, v___f_347_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8(lean_object* v___x_351_, lean_object* v_resTy_352_, lean_object* v_c_353_, lean_object* v_dec_354_, lean_object* v_k_355_, lean_object* v_inst_356_, lean_object* v_toBind_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_eTy_360_, lean_object* v_t_361_){
_start:
{
lean_object* v___f_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___f_362_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7), 9, 8);
lean_closure_set(v___f_362_, 0, v___x_351_);
lean_closure_set(v___f_362_, 1, v_resTy_352_);
lean_closure_set(v___f_362_, 2, v_c_353_);
lean_closure_set(v___f_362_, 3, v_dec_354_);
lean_closure_set(v___f_362_, 4, v_t_361_);
lean_closure_set(v___f_362_, 5, v_k_355_);
lean_closure_set(v___f_362_, 6, v_inst_356_);
lean_closure_set(v___f_362_, 7, v_toBind_357_);
v___x_363_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_364_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_358_, v_inst_359_, v___x_363_, v_eTy_360_, v___f_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9(lean_object* v___x_365_, lean_object* v_resTy_366_, lean_object* v_c_367_, lean_object* v_dec_368_, lean_object* v_k_369_, lean_object* v_inst_370_, lean_object* v_toBind_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_tTy_374_, lean_object* v_eTy_375_){
_start:
{
lean_object* v___f_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
lean_inc_ref(v_inst_373_);
lean_inc_ref(v_inst_372_);
v___f_376_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8), 11, 10);
lean_closure_set(v___f_376_, 0, v___x_365_);
lean_closure_set(v___f_376_, 1, v_resTy_366_);
lean_closure_set(v___f_376_, 2, v_c_367_);
lean_closure_set(v___f_376_, 3, v_dec_368_);
lean_closure_set(v___f_376_, 4, v_k_369_);
lean_closure_set(v___f_376_, 5, v_inst_370_);
lean_closure_set(v___f_376_, 6, v_toBind_371_);
lean_closure_set(v___f_376_, 7, v_inst_372_);
lean_closure_set(v___f_376_, 8, v_inst_373_);
lean_closure_set(v___f_376_, 9, v_eTy_375_);
v___x_377_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_378_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_372_, v_inst_373_, v___x_377_, v_tTy_374_, v___f_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(lean_object* v___x_379_, lean_object* v_resTy_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_mkArrow(v___x_379_, v_resTy_380_, v___y_383_, v___y_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(lean_object* v___x_387_, lean_object* v_resTy_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(v___x_387_, v_resTy_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(lean_object* v___x_395_, lean_object* v_resTy_396_, lean_object* v_c_397_, lean_object* v_dec_398_, lean_object* v_k_399_, lean_object* v_inst_400_, lean_object* v_toBind_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_tTy_404_){
_start:
{
lean_object* v___f_405_; lean_object* v___x_406_; lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
lean_inc(v_toBind_401_);
lean_inc(v_inst_400_);
lean_inc_ref(v_c_397_);
lean_inc_ref(v_resTy_396_);
v___f_405_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9), 11, 10);
lean_closure_set(v___f_405_, 0, v___x_395_);
lean_closure_set(v___f_405_, 1, v_resTy_396_);
lean_closure_set(v___f_405_, 2, v_c_397_);
lean_closure_set(v___f_405_, 3, v_dec_398_);
lean_closure_set(v___f_405_, 4, v_k_399_);
lean_closure_set(v___f_405_, 5, v_inst_400_);
lean_closure_set(v___f_405_, 6, v_toBind_401_);
lean_closure_set(v___f_405_, 7, v_inst_402_);
lean_closure_set(v___f_405_, 8, v_inst_403_);
lean_closure_set(v___f_405_, 9, v_tTy_404_);
v___x_406_ = l_Lean_mkNot(v_c_397_);
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed), 7, 2);
lean_closure_set(v___f_407_, 0, v___x_406_);
lean_closure_set(v___f_407_, 1, v_resTy_396_);
v___x_408_ = lean_apply_2(v_inst_400_, lean_box(0), v___f_407_);
v___x_409_ = lean_apply_4(v_toBind_401_, lean_box(0), lean_box(0), v___x_408_, v___f_405_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(lean_object* v___x_410_, lean_object* v_resTy_411_, lean_object* v_c_412_, lean_object* v_k_413_, lean_object* v_inst_414_, lean_object* v_toBind_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v___f_418_, lean_object* v_dec_419_){
_start:
{
lean_object* v___f_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_inc(v_toBind_415_);
lean_inc(v_inst_414_);
v___f_420_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11), 10, 9);
lean_closure_set(v___f_420_, 0, v___x_410_);
lean_closure_set(v___f_420_, 1, v_resTy_411_);
lean_closure_set(v___f_420_, 2, v_c_412_);
lean_closure_set(v___f_420_, 3, v_dec_419_);
lean_closure_set(v___f_420_, 4, v_k_413_);
lean_closure_set(v___f_420_, 5, v_inst_414_);
lean_closure_set(v___f_420_, 6, v_toBind_415_);
lean_closure_set(v___f_420_, 7, v_inst_416_);
lean_closure_set(v___f_420_, 8, v_inst_417_);
v___x_421_ = lean_apply_2(v_inst_414_, lean_box(0), v___f_418_);
v___x_422_ = lean_apply_4(v_toBind_415_, lean_box(0), lean_box(0), v___x_421_, v___f_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(lean_object* v_resTy_423_, lean_object* v_k_424_, lean_object* v_inst_425_, lean_object* v_toBind_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_c_429_){
_start:
{
lean_object* v___f_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___f_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
lean_inc_ref(v_resTy_423_);
lean_inc_ref_n(v_c_429_, 2);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed), 7, 2);
lean_closure_set(v___f_430_, 0, v_c_429_);
lean_closure_set(v___f_430_, 1, v_resTy_423_);
v___x_431_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_432_ = lean_box(0);
lean_inc_ref(v_inst_428_);
lean_inc_ref(v_inst_427_);
v___f_433_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12), 10, 9);
lean_closure_set(v___f_433_, 0, v___x_432_);
lean_closure_set(v___f_433_, 1, v_resTy_423_);
lean_closure_set(v___f_433_, 2, v_c_429_);
lean_closure_set(v___f_433_, 3, v_k_424_);
lean_closure_set(v___f_433_, 4, v_inst_425_);
lean_closure_set(v___f_433_, 5, v_toBind_426_);
lean_closure_set(v___f_433_, 6, v_inst_427_);
lean_closure_set(v___f_433_, 7, v_inst_428_);
lean_closure_set(v___f_433_, 8, v___f_430_);
v___x_434_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_435_ = l_Lean_Expr_app___override(v___x_434_, v_c_429_);
v___x_436_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_427_, v_inst_428_, v___x_431_, v___x_435_, v___f_433_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object* v___x_440_, lean_object* v_resTy_441_, lean_object* v_c_442_, lean_object* v_t_443_, lean_object* v_e_444_, lean_object* v_k_445_, lean_object* v_u_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_447_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v_u_446_);
lean_ctor_set(v___x_448_, 1, v___x_440_);
v___x_449_ = l_Lean_mkConst(v___x_447_, v___x_448_);
lean_inc_ref(v_e_444_);
lean_inc_ref(v_t_443_);
lean_inc_ref(v_c_442_);
v___x_450_ = l_Lean_mkApp4(v___x_449_, v_resTy_441_, v_c_442_, v_t_443_, v_e_444_);
v___x_451_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
v___x_452_ = lean_unsigned_to_nat(3u);
v___x_453_ = lean_mk_empty_array_with_capacity(v___x_452_);
v___x_454_ = lean_array_push(v___x_453_, v_c_442_);
v___x_455_ = lean_array_push(v___x_454_, v_t_443_);
v___x_456_ = lean_array_push(v___x_455_, v_e_444_);
v___x_457_ = lean_apply_2(v_k_445_, v___x_451_, v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object* v___x_458_, lean_object* v_resTy_459_, lean_object* v_c_460_, lean_object* v_t_461_, lean_object* v_k_462_, lean_object* v_inst_463_, lean_object* v_toBind_464_, lean_object* v_e_465_){
_start:
{
lean_object* v___f_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_inc_ref(v_resTy_459_);
v___f_466_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14), 7, 6);
lean_closure_set(v___f_466_, 0, v___x_458_);
lean_closure_set(v___f_466_, 1, v_resTy_459_);
lean_closure_set(v___f_466_, 2, v_c_460_);
lean_closure_set(v___f_466_, 3, v_t_461_);
lean_closure_set(v___f_466_, 4, v_e_465_);
lean_closure_set(v___f_466_, 5, v_k_462_);
v___x_467_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_467_, 0, v_resTy_459_);
v___x_468_ = lean_apply_2(v_inst_463_, lean_box(0), v___x_467_);
v___x_469_ = lean_apply_4(v_toBind_464_, lean_box(0), lean_box(0), v___x_468_, v___f_466_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object* v___x_470_, lean_object* v_resTy_471_, lean_object* v_c_472_, lean_object* v_k_473_, lean_object* v_inst_474_, lean_object* v_toBind_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_t_478_){
_start:
{
lean_object* v___f_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
lean_inc_ref(v_resTy_471_);
v___f_479_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15), 8, 7);
lean_closure_set(v___f_479_, 0, v___x_470_);
lean_closure_set(v___f_479_, 1, v_resTy_471_);
lean_closure_set(v___f_479_, 2, v_c_472_);
lean_closure_set(v___f_479_, 3, v_t_478_);
lean_closure_set(v___f_479_, 4, v_k_473_);
lean_closure_set(v___f_479_, 5, v_inst_474_);
lean_closure_set(v___f_479_, 6, v_toBind_475_);
v___x_480_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_481_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_476_, v_inst_477_, v___x_480_, v_resTy_471_, v___f_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object* v___x_482_, lean_object* v_resTy_483_, lean_object* v_k_484_, lean_object* v_inst_485_, lean_object* v_toBind_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_c_489_){
_start:
{
lean_object* v___f_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
lean_inc_ref(v_inst_488_);
lean_inc_ref(v_inst_487_);
lean_inc_ref(v_resTy_483_);
v___f_490_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16), 9, 8);
lean_closure_set(v___f_490_, 0, v___x_482_);
lean_closure_set(v___f_490_, 1, v_resTy_483_);
lean_closure_set(v___f_490_, 2, v_c_489_);
lean_closure_set(v___f_490_, 3, v_k_484_);
lean_closure_set(v___f_490_, 4, v_inst_485_);
lean_closure_set(v___f_490_, 5, v_toBind_486_);
lean_closure_set(v___f_490_, 6, v_inst_487_);
lean_closure_set(v___f_490_, 7, v_inst_488_);
v___x_491_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_492_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_487_, v_inst_488_, v___x_491_, v_resTy_483_, v___f_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object* v_resTy_493_, lean_object* v_motiveArgs_494_, lean_object* v_x_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
uint8_t v___x_501_; uint8_t v___x_502_; uint8_t v___x_503_; lean_object* v___x_504_; 
v___x_501_ = 0;
v___x_502_ = 1;
v___x_503_ = 1;
v___x_504_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_494_, v_resTy_493_, v___x_501_, v___x_502_, v___x_501_, v___x_502_, v___x_503_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed(lean_object* v_resTy_505_, lean_object* v_motiveArgs_506_, lean_object* v_x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(v_resTy_505_, v_motiveArgs_506_, v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_x_507_);
lean_dec_ref(v_motiveArgs_506_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object* v_i_517_, lean_object* v_a_518_, lean_object* v_x_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_520_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1));
v___x_521_ = lean_unsigned_to_nat(1u);
v___x_522_ = lean_nat_add(v_i_517_, v___x_521_);
v___x_523_ = lean_name_append_index_after(v___x_520_, v___x_522_);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v_a_518_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___boxed(lean_object* v_i_525_, lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(v_i_525_, v_a_526_, v_x_527_);
lean_dec(v_i_525_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object* v_i_529_, lean_object* v___x_530_, lean_object* v_discrs_531_, lean_object* v_prior_532_, lean_object* v_next_533_, lean_object* v_acc_534_, lean_object* v_h_535_, lean_object* v_G_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_a_543_; uint8_t v___x_547_; 
v___x_547_ = lean_nat_dec_lt(v_next_533_, v_i_529_);
if (v___x_547_ == 0)
{
lean_object* v___x_548_; 
lean_dec_ref(v_G_536_);
v___x_548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_548_, 0, v_acc_534_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_array_get_borrowed(v___x_530_, v_discrs_531_, v_next_533_);
v___x_550_ = l_Lean_Expr_isFVar(v___x_549_);
if (v___x_550_ == 0)
{
v_a_543_ = v_acc_534_;
goto v___jp_542_;
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_array_get_borrowed(v___x_530_, v_prior_532_, v_next_533_);
lean_inc(v___x_549_);
v___x_552_ = l_Lean_Expr_replaceFVar(v_acc_534_, v___x_549_, v___x_551_);
lean_dec_ref(v_acc_534_);
v_a_543_ = v___x_552_;
goto v___jp_542_;
}
}
v___jp_542_:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_add(v_next_533_, v___x_544_);
lean_inc(v___y_540_);
lean_inc_ref(v___y_539_);
lean_inc(v___y_538_);
lean_inc_ref(v___y_537_);
v___x_546_ = lean_apply_9(v_G_536_, v___x_545_, v_a_543_, lean_box(0), lean_box(0), v___y_537_, v___y_538_, v___y_539_, v___y_540_, lean_box(0));
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed(lean_object* v_i_553_, lean_object* v___x_554_, lean_object* v_discrs_555_, lean_object* v_prior_556_, lean_object* v_next_557_, lean_object* v_acc_558_, lean_object* v_h_559_, lean_object* v_G_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(v_i_553_, v___x_554_, v_discrs_555_, v_prior_556_, v_next_557_, v_acc_558_, v_h_559_, v_G_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v_next_557_);
lean_dec_ref(v_prior_556_);
lean_dec_ref(v_discrs_555_);
lean_dec_ref(v___x_554_);
lean_dec(v_i_553_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object* v_a_567_, lean_object* v___f_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; 
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
v___x_574_ = lean_infer_type(v_a_567_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v_a_575_; lean_object* v___x_576_; lean_object* v___x_2423__overap_577_; lean_object* v___x_578_; 
v_a_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc(v_a_575_);
lean_dec_ref_known(v___x_574_, 1);
v___x_576_ = lean_unsigned_to_nat(0u);
v___x_2423__overap_577_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_568_, v___x_576_, v_a_575_, lean_box(0));
v___x_578_ = lean_apply_5(v___x_2423__overap_577_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, lean_box(0));
return v___x_578_;
}
else
{
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec_ref(v___f_568_);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed(lean_object* v_a_579_, lean_object* v___f_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(v_a_579_, v___f_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object* v_i_587_, lean_object* v___x_588_, lean_object* v_discrs_589_, lean_object* v_a_590_, lean_object* v_inst_591_, lean_object* v_prior_592_){
_start:
{
lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___x_595_; 
v___f_593_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed), 13, 4);
lean_closure_set(v___f_593_, 0, v_i_587_);
lean_closure_set(v___f_593_, 1, v___x_588_);
lean_closure_set(v___f_593_, 2, v_discrs_589_);
lean_closure_set(v___f_593_, 3, v_prior_592_);
v___f_594_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___boxed), 7, 2);
lean_closure_set(v___f_594_, 0, v_a_590_);
lean_closure_set(v___f_594_, 1, v___f_593_);
v___x_595_ = lean_apply_2(v_inst_591_, lean_box(0), v___f_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object* v___x_599_, lean_object* v_discrs_600_, lean_object* v_inst_601_, lean_object* v_i_602_, lean_object* v_a_603_, lean_object* v_x_604_){
_start:
{
lean_object* v___f_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_inc(v_i_602_);
v___f_605_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22), 6, 5);
lean_closure_set(v___f_605_, 0, v_i_602_);
lean_closure_set(v___f_605_, 1, v___x_599_);
lean_closure_set(v___f_605_, 2, v_discrs_600_);
lean_closure_set(v___f_605_, 3, v_a_603_);
lean_closure_set(v___f_605_, 4, v_inst_601_);
v___x_606_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___closed__1));
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_add(v_i_602_, v___x_607_);
lean_dec(v_i_602_);
v___x_609_ = lean_name_append_index_after(v___x_606_, v___x_608_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___f_605_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object* v_toMatcherInfo_613_, lean_object* v_matcherName_614_, lean_object* v_matcherLevels_615_, lean_object* v_params_616_, lean_object* v_motive_617_, lean_object* v_discrs_618_, lean_object* v_alts_619_, lean_object* v_k_620_, lean_object* v_____do__lift_621_){
_start:
{
lean_object* v___x_622_; lean_object* v_abstractMatcherApp_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_622_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
lean_inc_ref(v_discrs_618_);
v_abstractMatcherApp_623_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_abstractMatcherApp_623_, 0, v_toMatcherInfo_613_);
lean_ctor_set(v_abstractMatcherApp_623_, 1, v_matcherName_614_);
lean_ctor_set(v_abstractMatcherApp_623_, 2, v_matcherLevels_615_);
lean_ctor_set(v_abstractMatcherApp_623_, 3, v_params_616_);
lean_ctor_set(v_abstractMatcherApp_623_, 4, v_motive_617_);
lean_ctor_set(v_abstractMatcherApp_623_, 5, v_discrs_618_);
lean_ctor_set(v_abstractMatcherApp_623_, 6, v_____do__lift_621_);
lean_ctor_set(v_abstractMatcherApp_623_, 7, v___x_622_);
v___x_624_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_624_, 0, v_abstractMatcherApp_623_);
v___x_625_ = l_Array_append___redArg(v_discrs_618_, v_alts_619_);
v___x_626_ = lean_apply_2(v_k_620_, v___x_624_, v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed(lean_object* v_toMatcherInfo_627_, lean_object* v_matcherName_628_, lean_object* v_matcherLevels_629_, lean_object* v_params_630_, lean_object* v_motive_631_, lean_object* v_discrs_632_, lean_object* v_alts_633_, lean_object* v_k_634_, lean_object* v_____do__lift_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(v_toMatcherInfo_627_, v_matcherName_628_, v_matcherLevels_629_, v_params_630_, v_motive_631_, v_discrs_632_, v_alts_633_, v_k_634_, v_____do__lift_635_);
lean_dec_ref(v_alts_633_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object* v_toMatcherInfo_638_, lean_object* v_matcherName_639_, lean_object* v_matcherLevels_640_, lean_object* v_params_641_, lean_object* v_motive_642_, lean_object* v_discrs_643_, lean_object* v_k_644_, lean_object* v___x_645_, lean_object* v_inst_646_, lean_object* v_toBind_647_, lean_object* v_alts_648_){
_start:
{
lean_object* v___f_649_; lean_object* v___x_650_; size_t v_sz_651_; size_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_inc_ref(v_alts_648_);
v___f_649_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___boxed), 9, 8);
lean_closure_set(v___f_649_, 0, v_toMatcherInfo_638_);
lean_closure_set(v___f_649_, 1, v_matcherName_639_);
lean_closure_set(v___f_649_, 2, v_matcherLevels_640_);
lean_closure_set(v___f_649_, 3, v_params_641_);
lean_closure_set(v___f_649_, 4, v_motive_642_);
lean_closure_set(v___f_649_, 5, v_discrs_643_);
lean_closure_set(v___f_649_, 6, v_alts_648_);
lean_closure_set(v___f_649_, 7, v_k_644_);
v___x_650_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25___closed__0));
v_sz_651_ = lean_array_size(v_alts_648_);
v___x_652_ = ((size_t)0ULL);
v___x_653_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_645_, v___x_650_, v_sz_651_, v___x_652_, v_alts_648_);
v___x_654_ = lean_apply_2(v_inst_646_, lean_box(0), v___x_653_);
v___x_655_ = lean_apply_4(v_toBind_647_, lean_box(0), lean_box(0), v___x_654_, v___f_649_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object* v___f_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v___f_678_, lean_object* v_origAltTypes_679_){
_start:
{
lean_object* v___x_680_; size_t v_sz_681_; size_t v___x_682_; lean_object* v_altNamesTypes_683_; uint8_t v___x_684_; lean_object* v___x_685_; 
v___x_680_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_681_ = lean_array_size(v_origAltTypes_679_);
v___x_682_ = ((size_t)0ULL);
lean_inc_ref(v_origAltTypes_679_);
v_altNamesTypes_683_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_680_, v_origAltTypes_679_, v___f_675_, v_sz_681_, v___x_682_, v_origAltTypes_679_);
lean_dec_ref(v_origAltTypes_679_);
v___x_684_ = 0;
v___x_685_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_676_, v_inst_677_, v_altNamesTypes_683_, v___f_678_, v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object* v_toMatcherInfo_686_, lean_object* v_matcherName_687_, lean_object* v_params_688_, lean_object* v_motive_689_, lean_object* v_discrs_690_, lean_object* v_k_691_, lean_object* v___x_692_, lean_object* v_inst_693_, lean_object* v_toBind_694_, lean_object* v___f_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_alts_698_, lean_object* v_matcherLevels_699_){
_start:
{
lean_object* v___f_700_; lean_object* v___f_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v_matcherPartial_704_; lean_object* v_matcherPartial_705_; lean_object* v_matcherPartial_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
lean_inc(v_toBind_694_);
lean_inc(v_inst_693_);
lean_inc_ref(v_discrs_690_);
lean_inc_ref(v_motive_689_);
lean_inc_ref(v_params_688_);
lean_inc_ref(v_matcherLevels_699_);
lean_inc(v_matcherName_687_);
v___f_700_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25), 11, 10);
lean_closure_set(v___f_700_, 0, v_toMatcherInfo_686_);
lean_closure_set(v___f_700_, 1, v_matcherName_687_);
lean_closure_set(v___f_700_, 2, v_matcherLevels_699_);
lean_closure_set(v___f_700_, 3, v_params_688_);
lean_closure_set(v___f_700_, 4, v_motive_689_);
lean_closure_set(v___f_700_, 5, v_discrs_690_);
lean_closure_set(v___f_700_, 6, v_k_691_);
lean_closure_set(v___f_700_, 7, v___x_692_);
lean_closure_set(v___f_700_, 8, v_inst_693_);
lean_closure_set(v___f_700_, 9, v_toBind_694_);
v___f_701_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26), 5, 4);
lean_closure_set(v___f_701_, 0, v___f_695_);
lean_closure_set(v___f_701_, 1, v_inst_696_);
lean_closure_set(v___f_701_, 2, v_inst_697_);
lean_closure_set(v___f_701_, 3, v___f_700_);
v___x_702_ = lean_array_to_list(v_matcherLevels_699_);
v___x_703_ = l_Lean_mkConst(v_matcherName_687_, v___x_702_);
v_matcherPartial_704_ = l_Lean_mkAppN(v___x_703_, v_params_688_);
lean_dec_ref(v_params_688_);
v_matcherPartial_705_ = l_Lean_Expr_app___override(v_matcherPartial_704_, v_motive_689_);
v_matcherPartial_706_ = l_Lean_mkAppN(v_matcherPartial_705_, v_discrs_690_);
lean_dec_ref(v_discrs_690_);
v___x_707_ = lean_array_get_size(v_alts_698_);
v___x_708_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_708_, 0, v___x_707_);
lean_closure_set(v___x_708_, 1, v_matcherPartial_706_);
v___x_709_ = lean_apply_2(v_inst_693_, lean_box(0), v___x_708_);
v___x_710_ = lean_apply_4(v_toBind_694_, lean_box(0), lean_box(0), v___x_709_, v___f_701_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object* v_toMatcherInfo_711_, lean_object* v_matcherName_712_, lean_object* v_params_713_, lean_object* v_motive_714_, lean_object* v_discrs_715_, lean_object* v_k_716_, lean_object* v___x_717_, lean_object* v_inst_718_, lean_object* v_toBind_719_, lean_object* v___f_720_, lean_object* v_inst_721_, lean_object* v_inst_722_, lean_object* v_alts_723_, lean_object* v_matcherLevels_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(v_toMatcherInfo_711_, v_matcherName_712_, v_params_713_, v_motive_714_, v_discrs_715_, v_k_716_, v___x_717_, v_inst_718_, v_toBind_719_, v___f_720_, v_inst_721_, v_inst_722_, v_alts_723_, v_matcherLevels_724_);
lean_dec_ref(v_alts_723_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28(lean_object* v___f_726_, lean_object* v_matcherLevels_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_apply_1(v___f_726_, v_matcherLevels_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30(lean_object* v_matcherLevels_729_, lean_object* v_val_730_, lean_object* v_toPure_731_, lean_object* v_toBind_732_, lean_object* v___f_733_, lean_object* v_uElim_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_array_set(v_matcherLevels_729_, v_val_730_, v_uElim_734_);
v___x_736_ = lean_apply_2(v_toPure_731_, lean_box(0), v___x_735_);
v___x_737_ = lean_apply_4(v_toBind_732_, lean_box(0), lean_box(0), v___x_736_, v___f_733_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30___boxed(lean_object* v_matcherLevels_738_, lean_object* v_val_739_, lean_object* v_toPure_740_, lean_object* v_toBind_741_, lean_object* v___f_742_, lean_object* v_uElim_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30(v_matcherLevels_738_, v_val_739_, v_toPure_740_, v_toBind_741_, v___f_742_, v_uElim_743_);
lean_dec(v_val_739_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__29(lean_object* v_toMatcherInfo_745_, lean_object* v_matcherName_746_, lean_object* v_params_747_, lean_object* v_discrs_748_, lean_object* v_k_749_, lean_object* v___x_750_, lean_object* v_inst_751_, lean_object* v_toBind_752_, lean_object* v___f_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_alts_756_, lean_object* v_toPure_757_, lean_object* v_matcherLevels_758_, lean_object* v_resTy_759_, lean_object* v_motive_760_){
_start:
{
lean_object* v_uElimPos_x3f_761_; lean_object* v___f_762_; 
v_uElimPos_x3f_761_ = lean_ctor_get(v_toMatcherInfo_745_, 3);
lean_inc(v_uElimPos_x3f_761_);
lean_inc(v_toBind_752_);
lean_inc(v_inst_751_);
v___f_762_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed), 14, 13);
lean_closure_set(v___f_762_, 0, v_toMatcherInfo_745_);
lean_closure_set(v___f_762_, 1, v_matcherName_746_);
lean_closure_set(v___f_762_, 2, v_params_747_);
lean_closure_set(v___f_762_, 3, v_motive_760_);
lean_closure_set(v___f_762_, 4, v_discrs_748_);
lean_closure_set(v___f_762_, 5, v_k_749_);
lean_closure_set(v___f_762_, 6, v___x_750_);
lean_closure_set(v___f_762_, 7, v_inst_751_);
lean_closure_set(v___f_762_, 8, v_toBind_752_);
lean_closure_set(v___f_762_, 9, v___f_753_);
lean_closure_set(v___f_762_, 10, v_inst_754_);
lean_closure_set(v___f_762_, 11, v_inst_755_);
lean_closure_set(v___f_762_, 12, v_alts_756_);
if (lean_obj_tag(v_uElimPos_x3f_761_) == 0)
{
lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
lean_dec_ref(v_resTy_759_);
lean_dec(v_inst_751_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28), 2, 1);
lean_closure_set(v___f_763_, 0, v___f_762_);
v___x_764_ = lean_apply_2(v_toPure_757_, lean_box(0), v_matcherLevels_758_);
v___x_765_ = lean_apply_4(v_toBind_752_, lean_box(0), lean_box(0), v___x_764_, v___f_763_);
return v___x_765_;
}
else
{
lean_object* v_val_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_val_766_ = lean_ctor_get(v_uElimPos_x3f_761_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v_uElimPos_x3f_761_, 1);
v___f_767_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__28), 2, 1);
lean_closure_set(v___f_767_, 0, v___f_762_);
lean_inc(v_toBind_752_);
v___f_768_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__30___boxed), 6, 5);
lean_closure_set(v___f_768_, 0, v_matcherLevels_758_);
lean_closure_set(v___f_768_, 1, v_val_766_);
lean_closure_set(v___f_768_, 2, v_toPure_757_);
lean_closure_set(v___f_768_, 3, v_toBind_752_);
lean_closure_set(v___f_768_, 4, v___f_767_);
v___x_769_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_769_, 0, v_resTy_759_);
v___x_770_ = lean_apply_2(v_inst_751_, lean_box(0), v___x_769_);
v___x_771_ = lean_apply_4(v_toBind_752_, lean_box(0), lean_box(0), v___x_770_, v___f_768_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(lean_object* v_toMatcherInfo_772_, lean_object* v_matcherName_773_, lean_object* v_params_774_, lean_object* v_k_775_, lean_object* v___x_776_, lean_object* v_inst_777_, lean_object* v_toBind_778_, lean_object* v___f_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_alts_782_, lean_object* v_toPure_783_, lean_object* v_matcherLevels_784_, lean_object* v_resTy_785_, lean_object* v___x_786_, lean_object* v_motive_787_, lean_object* v___f_788_, lean_object* v_discrs_789_){
_start:
{
lean_object* v___f_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_inc(v_toBind_778_);
lean_inc(v_inst_777_);
lean_inc_ref(v___x_776_);
v___f_790_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__29), 16, 15);
lean_closure_set(v___f_790_, 0, v_toMatcherInfo_772_);
lean_closure_set(v___f_790_, 1, v_matcherName_773_);
lean_closure_set(v___f_790_, 2, v_params_774_);
lean_closure_set(v___f_790_, 3, v_discrs_789_);
lean_closure_set(v___f_790_, 4, v_k_775_);
lean_closure_set(v___f_790_, 5, v___x_776_);
lean_closure_set(v___f_790_, 6, v_inst_777_);
lean_closure_set(v___f_790_, 7, v_toBind_778_);
lean_closure_set(v___f_790_, 8, v___f_779_);
lean_closure_set(v___f_790_, 9, v_inst_780_);
lean_closure_set(v___f_790_, 10, v_inst_781_);
lean_closure_set(v___f_790_, 11, v_alts_782_);
lean_closure_set(v___f_790_, 12, v_toPure_783_);
lean_closure_set(v___f_790_, 13, v_matcherLevels_784_);
lean_closure_set(v___f_790_, 14, v_resTy_785_);
v___x_791_ = 0;
v___x_792_ = l_Lean_Meta_lambdaTelescope___redArg(v___x_786_, v___x_776_, v_motive_787_, v___f_788_, v___x_791_);
v___x_793_ = lean_apply_2(v_inst_777_, lean_box(0), v___x_792_);
v___x_794_ = lean_apply_4(v_toBind_778_, lean_box(0), lean_box(0), v___x_793_, v___f_790_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_795_ = _args[0];
lean_object* v_matcherName_796_ = _args[1];
lean_object* v_params_797_ = _args[2];
lean_object* v_k_798_ = _args[3];
lean_object* v___x_799_ = _args[4];
lean_object* v_inst_800_ = _args[5];
lean_object* v_toBind_801_ = _args[6];
lean_object* v___f_802_ = _args[7];
lean_object* v_inst_803_ = _args[8];
lean_object* v_inst_804_ = _args[9];
lean_object* v_alts_805_ = _args[10];
lean_object* v_toPure_806_ = _args[11];
lean_object* v_matcherLevels_807_ = _args[12];
lean_object* v_resTy_808_ = _args[13];
lean_object* v___x_809_ = _args[14];
lean_object* v_motive_810_ = _args[15];
lean_object* v___f_811_ = _args[16];
lean_object* v_discrs_812_ = _args[17];
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31(v_toMatcherInfo_795_, v_matcherName_796_, v_params_797_, v_k_798_, v___x_799_, v_inst_800_, v_toBind_801_, v___f_802_, v_inst_803_, v_inst_804_, v_alts_805_, v_toPure_806_, v_matcherLevels_807_, v_resTy_808_, v___x_809_, v_motive_810_, v___f_811_, v_discrs_812_);
return v_res_813_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0(void){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_instMonadEIO___redArg();
return v___x_814_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0);
v___x_816_ = l_StateRefT_x27_instMonad___redArg(v___x_815_);
return v___x_816_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = l_Lean_Level_ofNat(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8);
v___x_827_ = l_Lean_mkSort(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_box(0);
v___x_832_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__11));
v___x_833_ = l_Lean_mkConst(v___x_832_, v___x_831_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_info_838_, lean_object* v_resTy_839_, lean_object* v_k_840_){
_start:
{
lean_object* v___x_841_; lean_object* v_toApplicative_842_; lean_object* v_toFunctor_843_; lean_object* v_toSeq_844_; lean_object* v_toSeqLeft_845_; lean_object* v_toSeqRight_846_; lean_object* v___f_847_; lean_object* v___f_848_; lean_object* v___f_849_; lean_object* v___f_850_; lean_object* v___x_851_; lean_object* v___f_852_; lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_toApplicative_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_939_; 
v___x_841_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_842_ = lean_ctor_get(v___x_841_, 0);
v_toFunctor_843_ = lean_ctor_get(v_toApplicative_842_, 0);
v_toSeq_844_ = lean_ctor_get(v_toApplicative_842_, 2);
v_toSeqLeft_845_ = lean_ctor_get(v_toApplicative_842_, 3);
v_toSeqRight_846_ = lean_ctor_get(v_toApplicative_842_, 4);
v___f_847_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_848_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_843_, 2);
v___f_849_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_849_, 0, v_toFunctor_843_);
v___f_850_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_850_, 0, v_toFunctor_843_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___f_849_);
lean_ctor_set(v___x_851_, 1, v___f_850_);
lean_inc(v_toSeqRight_846_);
v___f_852_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_852_, 0, v_toSeqRight_846_);
lean_inc(v_toSeqLeft_845_);
v___f_853_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_853_, 0, v_toSeqLeft_845_);
lean_inc(v_toSeq_844_);
v___f_854_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_854_, 0, v_toSeq_844_);
v___x_855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_855_, 0, v___x_851_);
lean_ctor_set(v___x_855_, 1, v___f_847_);
lean_ctor_set(v___x_855_, 2, v___f_854_);
lean_ctor_set(v___x_855_, 3, v___f_853_);
lean_ctor_set(v___x_855_, 4, v___f_852_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v___f_848_);
v___x_857_ = l_StateRefT_x27_instMonad___redArg(v___x_856_);
v_toApplicative_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_939_ == 0)
{
lean_object* v_unused_940_; 
v_unused_940_ = lean_ctor_get(v___x_857_, 1);
lean_dec(v_unused_940_);
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_939_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_toApplicative_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_939_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_toFunctor_862_; lean_object* v_toSeq_863_; lean_object* v_toSeqLeft_864_; lean_object* v_toSeqRight_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_937_; 
v_toFunctor_862_ = lean_ctor_get(v_toApplicative_858_, 0);
v_toSeq_863_ = lean_ctor_get(v_toApplicative_858_, 2);
v_toSeqLeft_864_ = lean_ctor_get(v_toApplicative_858_, 3);
v_toSeqRight_865_ = lean_ctor_get(v_toApplicative_858_, 4);
v_isSharedCheck_937_ = !lean_is_exclusive(v_toApplicative_858_);
if (v_isSharedCheck_937_ == 0)
{
lean_object* v_unused_938_; 
v_unused_938_ = lean_ctor_get(v_toApplicative_858_, 1);
lean_dec(v_unused_938_);
v___x_867_ = v_toApplicative_858_;
v_isShared_868_ = v_isSharedCheck_937_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_toSeqRight_865_);
lean_inc(v_toSeqLeft_864_);
lean_inc(v_toSeq_863_);
lean_inc(v_toFunctor_862_);
lean_dec(v_toApplicative_858_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_937_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___f_872_; lean_object* v___x_873_; lean_object* v___f_874_; lean_object* v___f_875_; lean_object* v___f_876_; lean_object* v___x_878_; 
v___f_869_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_870_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_862_);
v___f_871_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_871_, 0, v_toFunctor_862_);
v___f_872_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_872_, 0, v_toFunctor_862_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___f_871_);
lean_ctor_set(v___x_873_, 1, v___f_872_);
v___f_874_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_874_, 0, v_toSeqRight_865_);
v___f_875_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_875_, 0, v_toSeqLeft_864_);
v___f_876_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_876_, 0, v_toSeq_863_);
if (v_isShared_868_ == 0)
{
lean_ctor_set(v___x_867_, 4, v___f_874_);
lean_ctor_set(v___x_867_, 3, v___f_875_);
lean_ctor_set(v___x_867_, 2, v___f_876_);
lean_ctor_set(v___x_867_, 1, v___f_869_);
lean_ctor_set(v___x_867_, 0, v___x_873_);
v___x_878_ = v___x_867_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_873_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v___f_869_);
lean_ctor_set(v_reuseFailAlloc_936_, 2, v___f_876_);
lean_ctor_set(v_reuseFailAlloc_936_, 3, v___f_875_);
lean_ctor_set(v_reuseFailAlloc_936_, 4, v___f_874_);
v___x_878_ = v_reuseFailAlloc_936_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v___f_870_);
lean_ctor_set(v___x_860_, 0, v___x_878_);
v___x_880_ = v___x_860_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v___f_870_);
v___x_880_ = v_reuseFailAlloc_935_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v_toApplicative_881_; lean_object* v_toFunctor_882_; lean_object* v_toSeq_883_; lean_object* v_toSeqLeft_884_; lean_object* v_toSeqRight_885_; lean_object* v___f_886_; lean_object* v___f_887_; lean_object* v___x_888_; lean_object* v___f_889_; lean_object* v___f_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_toApplicative_881_ = lean_ctor_get(v___x_841_, 0);
v_toFunctor_882_ = lean_ctor_get(v_toApplicative_881_, 0);
v_toSeq_883_ = lean_ctor_get(v_toApplicative_881_, 2);
v_toSeqLeft_884_ = lean_ctor_get(v_toApplicative_881_, 3);
v_toSeqRight_885_ = lean_ctor_get(v_toApplicative_881_, 4);
lean_inc_ref_n(v_toFunctor_882_, 2);
v___f_886_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_886_, 0, v_toFunctor_882_);
v___f_887_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_887_, 0, v_toFunctor_882_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___f_886_);
lean_ctor_set(v___x_888_, 1, v___f_887_);
lean_inc(v_toSeqRight_885_);
v___f_889_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_889_, 0, v_toSeqRight_885_);
lean_inc(v_toSeqLeft_884_);
v___f_890_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_890_, 0, v_toSeqLeft_884_);
lean_inc(v_toSeq_883_);
v___f_891_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_891_, 0, v_toSeq_883_);
v___x_892_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_892_, 0, v___x_888_);
lean_ctor_set(v___x_892_, 1, v___f_847_);
lean_ctor_set(v___x_892_, 2, v___f_891_);
lean_ctor_set(v___x_892_, 3, v___f_890_);
lean_ctor_set(v___x_892_, 4, v___f_889_);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
lean_ctor_set(v___x_893_, 1, v___f_848_);
v___x_894_ = l_StateRefT_x27_instMonad___redArg(v___x_893_);
v___x_895_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_895_, 0, lean_box(0));
lean_closure_set(v___x_895_, 1, lean_box(0));
lean_closure_set(v___x_895_, 2, v___x_894_);
v___x_896_ = l_instMonadControlTOfPure___redArg(v___x_895_);
switch(lean_obj_tag(v_info_838_))
{
case 0:
{
lean_object* v_toBind_897_; lean_object* v___f_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref_known(v_info_838_, 1);
lean_dec_ref(v___x_896_);
lean_dec_ref(v___x_880_);
v_toBind_897_ = lean_ctor_get(v_inst_837_, 1);
lean_inc_ref(v_inst_837_);
lean_inc_ref(v_inst_836_);
lean_inc(v_toBind_897_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4), 7, 6);
lean_closure_set(v___f_898_, 0, v_resTy_839_);
lean_closure_set(v___f_898_, 1, v_k_840_);
lean_closure_set(v___f_898_, 2, v_inst_835_);
lean_closure_set(v___f_898_, 3, v_toBind_897_);
lean_closure_set(v___f_898_, 4, v_inst_836_);
lean_closure_set(v___f_898_, 5, v_inst_837_);
v___x_899_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_900_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_901_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_836_, v_inst_837_, v___x_899_, v___x_900_, v___f_898_);
return v___x_901_;
}
case 1:
{
lean_object* v_toBind_902_; lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_dec_ref_known(v_info_838_, 1);
lean_dec_ref(v___x_896_);
lean_dec_ref(v___x_880_);
v_toBind_902_ = lean_ctor_get(v_inst_837_, 1);
lean_inc_ref(v_inst_837_);
lean_inc_ref(v_inst_836_);
lean_inc(v_toBind_902_);
v___f_903_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13), 7, 6);
lean_closure_set(v___f_903_, 0, v_resTy_839_);
lean_closure_set(v___f_903_, 1, v_k_840_);
lean_closure_set(v___f_903_, 2, v_inst_835_);
lean_closure_set(v___f_903_, 3, v_toBind_902_);
lean_closure_set(v___f_903_, 4, v_inst_836_);
lean_closure_set(v___f_903_, 5, v_inst_837_);
v___x_904_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_905_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_906_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_836_, v_inst_837_, v___x_904_, v___x_905_, v___f_903_);
return v___x_906_;
}
case 2:
{
lean_object* v_toBind_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref_known(v_info_838_, 1);
lean_dec_ref(v___x_896_);
lean_dec_ref(v___x_880_);
v_toBind_907_ = lean_ctor_get(v_inst_837_, 1);
v___x_908_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_909_ = lean_box(0);
lean_inc_ref(v_inst_837_);
lean_inc_ref(v_inst_836_);
lean_inc(v_toBind_907_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17), 8, 7);
lean_closure_set(v___f_910_, 0, v___x_909_);
lean_closure_set(v___f_910_, 1, v_resTy_839_);
lean_closure_set(v___f_910_, 2, v_k_840_);
lean_closure_set(v___f_910_, 3, v_inst_835_);
lean_closure_set(v___f_910_, 4, v_toBind_907_);
lean_closure_set(v___f_910_, 5, v_inst_836_);
lean_closure_set(v___f_910_, 6, v_inst_837_);
v___x_911_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__12);
v___x_912_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_836_, v_inst_837_, v___x_908_, v___x_911_, v___f_910_);
return v___x_912_;
}
default: 
{
lean_object* v_toApplicative_913_; lean_object* v_matcherApp_914_; lean_object* v_toBind_915_; lean_object* v_toPure_916_; lean_object* v_toMatcherInfo_917_; lean_object* v_matcherName_918_; lean_object* v_matcherLevels_919_; lean_object* v_params_920_; lean_object* v_motive_921_; lean_object* v_discrs_922_; lean_object* v_alts_923_; lean_object* v___f_924_; lean_object* v___f_925_; lean_object* v___x_926_; lean_object* v___f_927_; lean_object* v___f_928_; lean_object* v___x_929_; size_t v_sz_930_; size_t v___x_931_; lean_object* v_discrDecls_932_; uint8_t v___x_933_; lean_object* v___x_934_; 
v_toApplicative_913_ = lean_ctor_get(v_inst_837_, 0);
v_matcherApp_914_ = lean_ctor_get(v_info_838_, 0);
lean_inc_ref(v_matcherApp_914_);
lean_dec_ref_known(v_info_838_, 1);
v_toBind_915_ = lean_ctor_get(v_inst_837_, 1);
v_toPure_916_ = lean_ctor_get(v_toApplicative_913_, 1);
v_toMatcherInfo_917_ = lean_ctor_get(v_matcherApp_914_, 0);
lean_inc_ref(v_toMatcherInfo_917_);
v_matcherName_918_ = lean_ctor_get(v_matcherApp_914_, 1);
lean_inc(v_matcherName_918_);
v_matcherLevels_919_ = lean_ctor_get(v_matcherApp_914_, 2);
lean_inc_ref(v_matcherLevels_919_);
v_params_920_ = lean_ctor_get(v_matcherApp_914_, 3);
lean_inc_ref(v_params_920_);
v_motive_921_ = lean_ctor_get(v_matcherApp_914_, 4);
lean_inc_ref(v_motive_921_);
v_discrs_922_ = lean_ctor_get(v_matcherApp_914_, 5);
lean_inc_ref_n(v_discrs_922_, 3);
v_alts_923_ = lean_ctor_get(v_matcherApp_914_, 6);
lean_inc_ref(v_alts_923_);
lean_dec_ref(v_matcherApp_914_);
lean_inc_ref(v_resTy_839_);
v___f_924_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18___boxed), 8, 1);
lean_closure_set(v___f_924_, 0, v_resTy_839_);
v___f_925_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__13));
v___x_926_ = l_Lean_instInhabitedExpr;
lean_inc(v_inst_835_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23), 6, 3);
lean_closure_set(v___f_927_, 0, v___x_926_);
lean_closure_set(v___f_927_, 1, v_discrs_922_);
lean_closure_set(v___f_927_, 2, v_inst_835_);
lean_inc(v_toPure_916_);
lean_inc_ref(v_inst_837_);
lean_inc_ref(v_inst_836_);
lean_inc(v_toBind_915_);
v___f_928_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__31___boxed), 18, 17);
lean_closure_set(v___f_928_, 0, v_toMatcherInfo_917_);
lean_closure_set(v___f_928_, 1, v_matcherName_918_);
lean_closure_set(v___f_928_, 2, v_params_920_);
lean_closure_set(v___f_928_, 3, v_k_840_);
lean_closure_set(v___f_928_, 4, v___x_880_);
lean_closure_set(v___f_928_, 5, v_inst_835_);
lean_closure_set(v___f_928_, 6, v_toBind_915_);
lean_closure_set(v___f_928_, 7, v___f_925_);
lean_closure_set(v___f_928_, 8, v_inst_836_);
lean_closure_set(v___f_928_, 9, v_inst_837_);
lean_closure_set(v___f_928_, 10, v_alts_923_);
lean_closure_set(v___f_928_, 11, v_toPure_916_);
lean_closure_set(v___f_928_, 12, v_matcherLevels_919_);
lean_closure_set(v___f_928_, 13, v_resTy_839_);
lean_closure_set(v___f_928_, 14, v___x_896_);
lean_closure_set(v___f_928_, 15, v_motive_921_);
lean_closure_set(v___f_928_, 16, v___f_924_);
v___x_929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_930_ = lean_array_size(v_discrs_922_);
v___x_931_ = ((size_t)0ULL);
v_discrDecls_932_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_929_, v_discrs_922_, v___f_927_, v_sz_930_, v___x_931_, v_discrs_922_);
lean_dec_ref(v_discrs_922_);
v___x_933_ = 0;
v___x_934_ = l_Lean_Meta_withLocalDeclsD___redArg(v_inst_836_, v_inst_837_, v_discrDecls_932_, v___f_928_, v___x_933_);
return v___x_934_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object* v_n_941_, lean_object* v_00_u03b1_942_, lean_object* v_inst_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_info_947_, lean_object* v_resTy_948_, lean_object* v_k_949_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(v_inst_943_, v_inst_944_, v_inst_945_, v_info_947_, v_resTy_948_, v_k_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object* v_n_951_, lean_object* v_00_u03b1_952_, lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_inst_955_, lean_object* v_inst_956_, lean_object* v_info_957_, lean_object* v_resTy_958_, lean_object* v_k_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(v_n_951_, v_00_u03b1_952_, v_inst_953_, v_inst_954_, v_inst_955_, v_inst_956_, v_info_957_, v_resTy_958_, v_k_959_);
lean_dec(v_inst_956_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object* v_u_961_, lean_object* v_resTy_962_, lean_object* v_c_963_, lean_object* v_h_964_, lean_object* v_t_965_, lean_object* v_toPure_966_, lean_object* v_e_967_){
_start:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_968_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_969_ = lean_box(0);
v___x_970_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_970_, 0, v_u_961_);
lean_ctor_set(v___x_970_, 1, v___x_969_);
v___x_971_ = l_Lean_mkConst(v___x_968_, v___x_970_);
v___x_972_ = l_Lean_mkApp5(v___x_971_, v_resTy_962_, v_c_963_, v_h_964_, v_t_965_, v_e_967_);
v___x_973_ = lean_apply_2(v_toPure_966_, lean_box(0), v___x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object* v_u_977_, lean_object* v_resTy_978_, lean_object* v_c_979_, lean_object* v_h_980_, lean_object* v_toPure_981_, lean_object* v_onAlt_982_, lean_object* v___x_983_, lean_object* v___x_984_, lean_object* v_toBind_985_, lean_object* v_t_986_){
_start:
{
lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_inc_ref(v_resTy_978_);
v___f_987_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0), 7, 6);
lean_closure_set(v___f_987_, 0, v_u_977_);
lean_closure_set(v___f_987_, 1, v_resTy_978_);
lean_closure_set(v___f_987_, 2, v_c_979_);
lean_closure_set(v___f_987_, 3, v_h_980_);
lean_closure_set(v___f_987_, 4, v_t_986_);
lean_closure_set(v___f_987_, 5, v_toPure_981_);
v___x_988_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_989_ = lean_apply_4(v_onAlt_982_, v___x_988_, v_resTy_978_, v___x_983_, v___x_984_);
v___x_990_ = lean_apply_4(v_toBind_985_, lean_box(0), lean_box(0), v___x_989_, v___f_987_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object* v___x_991_, uint8_t v_useSplitter_992_, lean_object* v_inst_993_, lean_object* v_____do__lift_994_){
_start:
{
uint8_t v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_995_ = 0;
v___x_996_ = 1;
v___x_997_ = lean_box(v___x_995_);
v___x_998_ = lean_box(v_useSplitter_992_);
v___x_999_ = lean_box(v___x_995_);
v___x_1000_ = lean_box(v_useSplitter_992_);
v___x_1001_ = lean_box(v___x_996_);
v___x_1002_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1002_, 0, v___x_991_);
lean_closure_set(v___x_1002_, 1, v_____do__lift_994_);
lean_closure_set(v___x_1002_, 2, v___x_997_);
lean_closure_set(v___x_1002_, 3, v___x_998_);
lean_closure_set(v___x_1002_, 4, v___x_999_);
lean_closure_set(v___x_1002_, 5, v___x_1000_);
lean_closure_set(v___x_1002_, 6, v___x_1001_);
v___x_1003_ = lean_apply_2(v_inst_993_, lean_box(0), v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object* v___x_1004_, lean_object* v_useSplitter_1005_, lean_object* v_inst_1006_, lean_object* v_____do__lift_1007_){
_start:
{
uint8_t v_useSplitter_boxed_1008_; lean_object* v_res_1009_; 
v_useSplitter_boxed_1008_ = lean_unbox(v_useSplitter_1005_);
v_res_1009_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(v___x_1004_, v_useSplitter_boxed_1008_, v_inst_1006_, v_____do__lift_1007_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object* v___x_1013_, uint8_t v_useSplitter_1014_, lean_object* v_inst_1015_, lean_object* v_onAlt_1016_, lean_object* v_resTy_1017_, lean_object* v_toBind_1018_, lean_object* v_h_1019_){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1023_ = lean_mk_empty_array_with_capacity(v___x_1013_);
v___x_1024_ = lean_array_push(v___x_1023_, v_h_1019_);
v___x_1025_ = lean_box(v_useSplitter_1014_);
lean_inc_ref(v___x_1024_);
v___f_1026_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1026_, 0, v___x_1024_);
lean_closure_set(v___f_1026_, 1, v___x_1025_);
lean_closure_set(v___f_1026_, 2, v_inst_1015_);
v___x_1027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1022_);
lean_ctor_set(v___x_1027_, 1, v___x_1024_);
lean_ctor_set(v___x_1027_, 2, v___x_1022_);
lean_ctor_set(v___x_1027_, 3, v___x_1022_);
lean_ctor_set(v___x_1027_, 4, v___x_1022_);
v___x_1028_ = lean_apply_4(v_onAlt_1016_, v___x_1020_, v_resTy_1017_, v___x_1021_, v___x_1027_);
v___x_1029_ = lean_apply_4(v_toBind_1018_, lean_box(0), lean_box(0), v___x_1028_, v___f_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object* v___x_1030_, lean_object* v_useSplitter_1031_, lean_object* v_inst_1032_, lean_object* v_onAlt_1033_, lean_object* v_resTy_1034_, lean_object* v_toBind_1035_, lean_object* v_h_1036_){
_start:
{
uint8_t v_useSplitter_boxed_1037_; lean_object* v_res_1038_; 
v_useSplitter_boxed_1037_ = lean_unbox(v_useSplitter_1031_);
v_res_1038_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(v___x_1030_, v_useSplitter_boxed_1037_, v_inst_1032_, v_onAlt_1033_, v_resTy_1034_, v_toBind_1035_, v_h_1036_);
lean_dec(v___x_1030_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object* v___x_1039_, uint8_t v_useSplitter_1040_, lean_object* v_inst_1041_, lean_object* v_onAlt_1042_, lean_object* v_resTy_1043_, lean_object* v_toBind_1044_, lean_object* v_h_1045_){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1048_ = lean_mk_empty_array_with_capacity(v___x_1039_);
v___x_1049_ = lean_array_push(v___x_1048_, v_h_1045_);
v___x_1050_ = lean_box(v_useSplitter_1040_);
lean_inc_ref(v___x_1049_);
v___f_1051_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_1051_, 0, v___x_1049_);
lean_closure_set(v___f_1051_, 1, v___x_1050_);
lean_closure_set(v___f_1051_, 2, v_inst_1041_);
v___x_1052_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1047_);
lean_ctor_set(v___x_1052_, 1, v___x_1049_);
lean_ctor_set(v___x_1052_, 2, v___x_1047_);
lean_ctor_set(v___x_1052_, 3, v___x_1047_);
lean_ctor_set(v___x_1052_, 4, v___x_1047_);
v___x_1053_ = lean_apply_4(v_onAlt_1042_, v___x_1046_, v_resTy_1043_, v___x_1039_, v___x_1052_);
v___x_1054_ = lean_apply_4(v_toBind_1044_, lean_box(0), lean_box(0), v___x_1053_, v___f_1051_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object* v___x_1055_, lean_object* v_useSplitter_1056_, lean_object* v_inst_1057_, lean_object* v_onAlt_1058_, lean_object* v_resTy_1059_, lean_object* v_toBind_1060_, lean_object* v_h_1061_){
_start:
{
uint8_t v_useSplitter_boxed_1062_; lean_object* v_res_1063_; 
v_useSplitter_boxed_1062_ = lean_unbox(v_useSplitter_1056_);
v_res_1063_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(v___x_1055_, v_useSplitter_boxed_1062_, v_inst_1057_, v_onAlt_1058_, v_resTy_1059_, v_toBind_1060_, v_h_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object* v_u_1064_, lean_object* v_resTy_1065_, lean_object* v_c_1066_, lean_object* v_h_1067_, lean_object* v_t_1068_, lean_object* v_toPure_1069_, lean_object* v_e_1070_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_u_1064_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l_Lean_mkConst(v___x_1071_, v___x_1073_);
v___x_1075_ = l_Lean_mkApp5(v___x_1074_, v_resTy_1065_, v_c_1066_, v_h_1067_, v_t_1068_, v_e_1070_);
v___x_1076_ = lean_apply_2(v_toPure_1069_, lean_box(0), v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object* v_u_1077_, lean_object* v_resTy_1078_, lean_object* v_c_1079_, lean_object* v_h_1080_, lean_object* v_toPure_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_n_1084_, uint8_t v___x_1085_, lean_object* v___f_1086_, uint8_t v___x_1087_, lean_object* v_toBind_1088_, lean_object* v_t_1089_){
_start:
{
lean_object* v___f_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_inc_ref(v_c_1079_);
v___f_1090_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4), 7, 6);
lean_closure_set(v___f_1090_, 0, v_u_1077_);
lean_closure_set(v___f_1090_, 1, v_resTy_1078_);
lean_closure_set(v___f_1090_, 2, v_c_1079_);
lean_closure_set(v___f_1090_, 3, v_h_1080_);
lean_closure_set(v___f_1090_, 4, v_t_1089_);
lean_closure_set(v___f_1090_, 5, v_toPure_1081_);
v___x_1091_ = l_Lean_mkNot(v_c_1079_);
v___x_1092_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1082_, v_inst_1083_, v_n_1084_, v___x_1085_, v___x_1091_, v___f_1086_, v___x_1087_);
v___x_1093_ = lean_apply_4(v_toBind_1088_, lean_box(0), lean_box(0), v___x_1092_, v___f_1090_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object* v_u_1094_, lean_object* v_resTy_1095_, lean_object* v_c_1096_, lean_object* v_h_1097_, lean_object* v_toPure_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_n_1101_, lean_object* v___x_1102_, lean_object* v___f_1103_, lean_object* v___x_1104_, lean_object* v_toBind_1105_, lean_object* v_t_1106_){
_start:
{
uint8_t v___x_1668__boxed_1107_; uint8_t v___x_1670__boxed_1108_; lean_object* v_res_1109_; 
v___x_1668__boxed_1107_ = lean_unbox(v___x_1102_);
v___x_1670__boxed_1108_ = lean_unbox(v___x_1104_);
v_res_1109_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(v_u_1094_, v_resTy_1095_, v_c_1096_, v_h_1097_, v_toPure_1098_, v_inst_1099_, v_inst_1100_, v_n_1101_, v___x_1668__boxed_1107_, v___f_1103_, v___x_1670__boxed_1108_, v_toBind_1105_, v_t_1106_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object* v_u_1110_, lean_object* v_resTy_1111_, lean_object* v_c_1112_, lean_object* v_h_1113_, lean_object* v_toPure_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_, lean_object* v___f_1117_, lean_object* v_toBind_1118_, lean_object* v___f_1119_, lean_object* v_n_1120_){
_start:
{
uint8_t v___x_1121_; uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1121_ = 0;
v___x_1122_ = 0;
v___x_1123_ = lean_box(v___x_1121_);
v___x_1124_ = lean_box(v___x_1122_);
lean_inc(v_toBind_1118_);
lean_inc(v_n_1120_);
lean_inc_ref(v_inst_1116_);
lean_inc_ref(v_inst_1115_);
lean_inc_ref(v_c_1112_);
v___f_1125_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1125_, 0, v_u_1110_);
lean_closure_set(v___f_1125_, 1, v_resTy_1111_);
lean_closure_set(v___f_1125_, 2, v_c_1112_);
lean_closure_set(v___f_1125_, 3, v_h_1113_);
lean_closure_set(v___f_1125_, 4, v_toPure_1114_);
lean_closure_set(v___f_1125_, 5, v_inst_1115_);
lean_closure_set(v___f_1125_, 6, v_inst_1116_);
lean_closure_set(v___f_1125_, 7, v_n_1120_);
lean_closure_set(v___f_1125_, 8, v___x_1123_);
lean_closure_set(v___f_1125_, 9, v___f_1117_);
lean_closure_set(v___f_1125_, 10, v___x_1124_);
lean_closure_set(v___f_1125_, 11, v_toBind_1118_);
v___x_1126_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1115_, v_inst_1116_, v_n_1120_, v___x_1121_, v_c_1112_, v___f_1119_, v___x_1122_);
v___x_1127_ = lean_apply_4(v_toBind_1118_, lean_box(0), lean_box(0), v___x_1126_, v___f_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object* v___x_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_Core_mkFreshUserName(v___x_1128_, v___y_1131_, v___y_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object* v___x_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v_res_1141_; 
v_res_1141_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(v___x_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
lean_dec(v___y_1137_);
lean_dec_ref(v___y_1136_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object* v_e_1149_, uint8_t v_useSplitter_1150_, lean_object* v_resTy_1151_, lean_object* v_toPure_1152_, lean_object* v_onAlt_1153_, lean_object* v_toBind_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_u_1158_){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v_c_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v_h_1167_; 
v___x_1159_ = lean_unsigned_to_nat(1u);
v___x_1160_ = l_Lean_Expr_getAppNumArgs(v_e_1149_);
v___x_1161_ = lean_nat_sub(v___x_1160_, v___x_1159_);
v___x_1162_ = lean_nat_sub(v___x_1161_, v___x_1159_);
lean_dec(v___x_1161_);
v_c_1163_ = l_Lean_Expr_getRevArg_x21(v_e_1149_, v___x_1162_);
v___x_1164_ = lean_unsigned_to_nat(2u);
v___x_1165_ = lean_nat_sub(v___x_1160_, v___x_1164_);
lean_dec(v___x_1160_);
v___x_1166_ = lean_nat_sub(v___x_1165_, v___x_1159_);
lean_dec(v___x_1165_);
v_h_1167_ = l_Lean_Expr_getRevArg_x21(v_e_1149_, v___x_1166_);
if (v_useSplitter_1150_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___f_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec_ref(v_inst_1157_);
lean_dec_ref(v_inst_1156_);
lean_dec(v_inst_1155_);
v___x_1168_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1154_);
lean_inc(v_onAlt_1153_);
lean_inc_ref(v_resTy_1151_);
v___f_1171_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1171_, 0, v_u_1158_);
lean_closure_set(v___f_1171_, 1, v_resTy_1151_);
lean_closure_set(v___f_1171_, 2, v_c_1163_);
lean_closure_set(v___f_1171_, 3, v_h_1167_);
lean_closure_set(v___f_1171_, 4, v_toPure_1152_);
lean_closure_set(v___f_1171_, 5, v_onAlt_1153_);
lean_closure_set(v___f_1171_, 6, v___x_1159_);
lean_closure_set(v___f_1171_, 7, v___x_1170_);
lean_closure_set(v___f_1171_, 8, v_toBind_1154_);
v___x_1172_ = lean_apply_4(v_onAlt_1153_, v___x_1168_, v_resTy_1151_, v___x_1169_, v___x_1170_);
v___x_1173_ = lean_apply_4(v_toBind_1154_, lean_box(0), lean_box(0), v___x_1172_, v___f_1171_);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1174_ = lean_box(v_useSplitter_1150_);
lean_inc_n(v_toBind_1154_, 3);
lean_inc_ref_n(v_resTy_1151_, 2);
lean_inc(v_onAlt_1153_);
lean_inc_n(v_inst_1155_, 2);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1175_, 0, v___x_1159_);
lean_closure_set(v___f_1175_, 1, v___x_1174_);
lean_closure_set(v___f_1175_, 2, v_inst_1155_);
lean_closure_set(v___f_1175_, 3, v_onAlt_1153_);
lean_closure_set(v___f_1175_, 4, v_resTy_1151_);
lean_closure_set(v___f_1175_, 5, v_toBind_1154_);
v___x_1176_ = lean_box(v_useSplitter_1150_);
v___f_1177_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1177_, 0, v___x_1159_);
lean_closure_set(v___f_1177_, 1, v___x_1176_);
lean_closure_set(v___f_1177_, 2, v_inst_1155_);
lean_closure_set(v___f_1177_, 3, v_onAlt_1153_);
lean_closure_set(v___f_1177_, 4, v_resTy_1151_);
lean_closure_set(v___f_1177_, 5, v_toBind_1154_);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1178_, 0, v_u_1158_);
lean_closure_set(v___f_1178_, 1, v_resTy_1151_);
lean_closure_set(v___f_1178_, 2, v_c_1163_);
lean_closure_set(v___f_1178_, 3, v_h_1167_);
lean_closure_set(v___f_1178_, 4, v_toPure_1152_);
lean_closure_set(v___f_1178_, 5, v_inst_1156_);
lean_closure_set(v___f_1178_, 6, v_inst_1157_);
lean_closure_set(v___f_1178_, 7, v___f_1177_);
lean_closure_set(v___f_1178_, 8, v_toBind_1154_);
lean_closure_set(v___f_1178_, 9, v___f_1175_);
v___f_1179_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1180_ = lean_apply_2(v_inst_1155_, lean_box(0), v___f_1179_);
v___x_1181_ = lean_apply_4(v_toBind_1154_, lean_box(0), lean_box(0), v___x_1180_, v___f_1178_);
return v___x_1181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object* v_e_1182_, lean_object* v_useSplitter_1183_, lean_object* v_resTy_1184_, lean_object* v_toPure_1185_, lean_object* v_onAlt_1186_, lean_object* v_toBind_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_inst_1190_, lean_object* v_u_1191_){
_start:
{
uint8_t v_useSplitter_boxed_1192_; lean_object* v_res_1193_; 
v_useSplitter_boxed_1192_ = lean_unbox(v_useSplitter_1183_);
v_res_1193_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(v_e_1182_, v_useSplitter_boxed_1192_, v_resTy_1184_, v_toPure_1185_, v_onAlt_1186_, v_toBind_1187_, v_inst_1188_, v_inst_1189_, v_inst_1190_, v_u_1191_);
lean_dec_ref(v_e_1182_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object* v___x_1194_, lean_object* v_inst_1195_, lean_object* v_____do__lift_1196_){
_start:
{
uint8_t v___x_1197_; uint8_t v___x_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1197_ = 0;
v___x_1198_ = 1;
v___x_1199_ = 1;
v___x_1200_ = lean_box(v___x_1197_);
v___x_1201_ = lean_box(v___x_1198_);
v___x_1202_ = lean_box(v___x_1197_);
v___x_1203_ = lean_box(v___x_1198_);
v___x_1204_ = lean_box(v___x_1199_);
v___x_1205_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1205_, 0, v___x_1194_);
lean_closure_set(v___x_1205_, 1, v_____do__lift_1196_);
lean_closure_set(v___x_1205_, 2, v___x_1200_);
lean_closure_set(v___x_1205_, 3, v___x_1201_);
lean_closure_set(v___x_1205_, 4, v___x_1202_);
lean_closure_set(v___x_1205_, 5, v___x_1203_);
lean_closure_set(v___x_1205_, 6, v___x_1204_);
v___x_1206_ = lean_apply_2(v_inst_1195_, lean_box(0), v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object* v_inst_1207_, lean_object* v_onAlt_1208_, lean_object* v_resTy_1209_, lean_object* v_toBind_1210_, lean_object* v_h_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___f_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1212_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_unsigned_to_nat(1u);
v___x_1215_ = lean_mk_empty_array_with_capacity(v___x_1214_);
v___x_1216_ = lean_array_push(v___x_1215_, v_h_1211_);
lean_inc_ref_n(v___x_1216_, 2);
v___f_1217_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1217_, 0, v___x_1216_);
lean_closure_set(v___f_1217_, 1, v_inst_1207_);
v___x_1218_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1216_);
lean_ctor_set(v___x_1219_, 1, v___x_1216_);
lean_ctor_set(v___x_1219_, 2, v___x_1218_);
lean_ctor_set(v___x_1219_, 3, v___x_1218_);
lean_ctor_set(v___x_1219_, 4, v___x_1218_);
v___x_1220_ = lean_apply_4(v_onAlt_1208_, v___x_1212_, v_resTy_1209_, v___x_1213_, v___x_1219_);
v___x_1221_ = lean_apply_4(v_toBind_1210_, lean_box(0), lean_box(0), v___x_1220_, v___f_1217_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object* v___x_1222_, lean_object* v_inst_1223_, lean_object* v_onAlt_1224_, lean_object* v_resTy_1225_, lean_object* v_toBind_1226_, lean_object* v_h_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___f_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1228_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1229_ = lean_mk_empty_array_with_capacity(v___x_1222_);
v___x_1230_ = lean_array_push(v___x_1229_, v_h_1227_);
lean_inc_ref_n(v___x_1230_, 2);
v___f_1231_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1231_, 0, v___x_1230_);
lean_closure_set(v___f_1231_, 1, v_inst_1223_);
v___x_1232_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24___closed__0));
v___x_1233_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1230_);
lean_ctor_set(v___x_1233_, 1, v___x_1230_);
lean_ctor_set(v___x_1233_, 2, v___x_1232_);
lean_ctor_set(v___x_1233_, 3, v___x_1232_);
lean_ctor_set(v___x_1233_, 4, v___x_1232_);
v___x_1234_ = lean_apply_4(v_onAlt_1224_, v___x_1228_, v_resTy_1225_, v___x_1222_, v___x_1233_);
v___x_1235_ = lean_apply_4(v_toBind_1226_, lean_box(0), lean_box(0), v___x_1234_, v___f_1231_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object* v_inst_1236_, lean_object* v_onAlt_1237_, lean_object* v_resTy_1238_, lean_object* v_toBind_1239_, lean_object* v_e_1240_, lean_object* v_toPure_1241_, lean_object* v_inst_1242_, lean_object* v_inst_1243_, lean_object* v___f_1244_, lean_object* v_u_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v___f_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v_c_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v_h_1255_; lean_object* v___f_1256_; lean_object* v___f_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1246_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_toBind_1239_, 2);
lean_inc_ref(v_resTy_1238_);
lean_inc(v_inst_1236_);
v___f_1247_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13), 6, 5);
lean_closure_set(v___f_1247_, 0, v___x_1246_);
lean_closure_set(v___f_1247_, 1, v_inst_1236_);
lean_closure_set(v___f_1247_, 2, v_onAlt_1237_);
lean_closure_set(v___f_1247_, 3, v_resTy_1238_);
lean_closure_set(v___f_1247_, 4, v_toBind_1239_);
v___x_1248_ = l_Lean_Expr_getAppNumArgs(v_e_1240_);
v___x_1249_ = lean_nat_sub(v___x_1248_, v___x_1246_);
v___x_1250_ = lean_nat_sub(v___x_1249_, v___x_1246_);
lean_dec(v___x_1249_);
v_c_1251_ = l_Lean_Expr_getRevArg_x21(v_e_1240_, v___x_1250_);
v___x_1252_ = lean_unsigned_to_nat(2u);
v___x_1253_ = lean_nat_sub(v___x_1248_, v___x_1252_);
lean_dec(v___x_1248_);
v___x_1254_ = lean_nat_sub(v___x_1253_, v___x_1246_);
lean_dec(v___x_1253_);
v_h_1255_ = l_Lean_Expr_getRevArg_x21(v_e_1240_, v___x_1254_);
v___f_1256_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1256_, 0, v_u_1245_);
lean_closure_set(v___f_1256_, 1, v_resTy_1238_);
lean_closure_set(v___f_1256_, 2, v_c_1251_);
lean_closure_set(v___f_1256_, 3, v_h_1255_);
lean_closure_set(v___f_1256_, 4, v_toPure_1241_);
lean_closure_set(v___f_1256_, 5, v_inst_1242_);
lean_closure_set(v___f_1256_, 6, v_inst_1243_);
lean_closure_set(v___f_1256_, 7, v___f_1247_);
lean_closure_set(v___f_1256_, 8, v_toBind_1239_);
lean_closure_set(v___f_1256_, 9, v___f_1244_);
v___f_1257_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1258_ = lean_apply_2(v_inst_1236_, lean_box(0), v___f_1257_);
v___x_1259_ = lean_apply_4(v_toBind_1239_, lean_box(0), lean_box(0), v___x_1258_, v___f_1256_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object* v_inst_1260_, lean_object* v_onAlt_1261_, lean_object* v_resTy_1262_, lean_object* v_toBind_1263_, lean_object* v_e_1264_, lean_object* v_toPure_1265_, lean_object* v_inst_1266_, lean_object* v_inst_1267_, lean_object* v___f_1268_, lean_object* v_u_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(v_inst_1260_, v_onAlt_1261_, v_resTy_1262_, v_toBind_1263_, v_e_1264_, v_toPure_1265_, v_inst_1266_, v_inst_1267_, v___f_1268_, v_u_1269_);
lean_dec_ref(v_e_1264_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object* v_u_1271_, lean_object* v_resTy_1272_, lean_object* v_c_1273_, lean_object* v_t_1274_, lean_object* v_toPure_1275_, lean_object* v_e_1276_){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1277_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_1278_ = lean_box(0);
v___x_1279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1279_, 0, v_u_1271_);
lean_ctor_set(v___x_1279_, 1, v___x_1278_);
v___x_1280_ = l_Lean_mkConst(v___x_1277_, v___x_1279_);
v___x_1281_ = l_Lean_mkApp4(v___x_1280_, v_resTy_1272_, v_c_1273_, v_t_1274_, v_e_1276_);
v___x_1282_ = lean_apply_2(v_toPure_1275_, lean_box(0), v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object* v_u_1283_, lean_object* v_resTy_1284_, lean_object* v_c_1285_, lean_object* v_toPure_1286_, lean_object* v_onAlt_1287_, lean_object* v___x_1288_, lean_object* v___x_1289_, lean_object* v_toBind_1290_, lean_object* v_t_1291_){
_start:
{
lean_object* v___f_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
lean_inc_ref(v_resTy_1284_);
v___f_1292_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12), 6, 5);
lean_closure_set(v___f_1292_, 0, v_u_1283_);
lean_closure_set(v___f_1292_, 1, v_resTy_1284_);
lean_closure_set(v___f_1292_, 2, v_c_1285_);
lean_closure_set(v___f_1292_, 3, v_t_1291_);
lean_closure_set(v___f_1292_, 4, v_toPure_1286_);
v___x_1293_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1294_ = lean_apply_4(v_onAlt_1287_, v___x_1293_, v_resTy_1284_, v___x_1288_, v___x_1289_);
v___x_1295_ = lean_apply_4(v_toBind_1290_, lean_box(0), lean_box(0), v___x_1294_, v___f_1292_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20(lean_object* v___x_1297_, lean_object* v_u_1298_, lean_object* v___x_1299_, lean_object* v_resTy_1300_, lean_object* v_c_1301_, lean_object* v_t_1302_, lean_object* v_toPure_1303_, lean_object* v_e_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1305_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20___closed__0));
v___x_1306_ = l_Lean_Name_mkStr2(v___x_1297_, v___x_1305_);
v___x_1307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_u_1298_);
lean_ctor_set(v___x_1307_, 1, v___x_1299_);
v___x_1308_ = l_Lean_mkConst(v___x_1306_, v___x_1307_);
v___x_1309_ = l_Lean_mkApp4(v___x_1308_, v_resTy_1300_, v_c_1301_, v_t_1302_, v_e_1304_);
v___x_1310_ = lean_apply_2(v_toPure_1303_, lean_box(0), v___x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object* v___x_1311_, lean_object* v_u_1312_, lean_object* v___x_1313_, lean_object* v_resTy_1314_, lean_object* v_c_1315_, lean_object* v_toPure_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_n_1319_, uint8_t v___x_1320_, lean_object* v_hFalse_1321_, lean_object* v___f_1322_, uint8_t v___x_1323_, lean_object* v_toBind_1324_, lean_object* v_t_1325_){
_start:
{
lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___f_1326_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__20), 8, 7);
lean_closure_set(v___f_1326_, 0, v___x_1311_);
lean_closure_set(v___f_1326_, 1, v_u_1312_);
lean_closure_set(v___f_1326_, 2, v___x_1313_);
lean_closure_set(v___f_1326_, 3, v_resTy_1314_);
lean_closure_set(v___f_1326_, 4, v_c_1315_);
lean_closure_set(v___f_1326_, 5, v_t_1325_);
lean_closure_set(v___f_1326_, 6, v_toPure_1316_);
v___x_1327_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1317_, v_inst_1318_, v_n_1319_, v___x_1320_, v_hFalse_1321_, v___f_1322_, v___x_1323_);
v___x_1328_ = lean_apply_4(v_toBind_1324_, lean_box(0), lean_box(0), v___x_1327_, v___f_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object* v___x_1329_, lean_object* v_u_1330_, lean_object* v___x_1331_, lean_object* v_resTy_1332_, lean_object* v_c_1333_, lean_object* v_toPure_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_n_1337_, lean_object* v___x_1338_, lean_object* v_hFalse_1339_, lean_object* v___f_1340_, lean_object* v___x_1341_, lean_object* v_toBind_1342_, lean_object* v_t_1343_){
_start:
{
uint8_t v___x_2001__boxed_1344_; uint8_t v___x_2003__boxed_1345_; lean_object* v_res_1346_; 
v___x_2001__boxed_1344_ = lean_unbox(v___x_1338_);
v___x_2003__boxed_1345_ = lean_unbox(v___x_1341_);
v_res_1346_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(v___x_1329_, v_u_1330_, v___x_1331_, v_resTy_1332_, v_c_1333_, v_toPure_1334_, v_inst_1335_, v_inst_1336_, v_n_1337_, v___x_2001__boxed_1344_, v_hFalse_1339_, v___f_1340_, v___x_2003__boxed_1345_, v_toBind_1342_, v_t_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16(lean_object* v___x_1347_, lean_object* v_u_1348_, lean_object* v___x_1349_, lean_object* v_resTy_1350_, lean_object* v_c_1351_, lean_object* v_toPure_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_n_1355_, lean_object* v___f_1356_, lean_object* v_toBind_1357_, lean_object* v_hTrue_1358_, lean_object* v___f_1359_, lean_object* v_hFalse_1360_){
_start:
{
uint8_t v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___f_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1361_ = 0;
v___x_1362_ = 0;
v___x_1363_ = lean_box(v___x_1361_);
v___x_1364_ = lean_box(v___x_1362_);
lean_inc(v_toBind_1357_);
lean_inc(v_n_1355_);
lean_inc_ref(v_inst_1354_);
lean_inc_ref(v_inst_1353_);
v___f_1365_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed), 15, 14);
lean_closure_set(v___f_1365_, 0, v___x_1347_);
lean_closure_set(v___f_1365_, 1, v_u_1348_);
lean_closure_set(v___f_1365_, 2, v___x_1349_);
lean_closure_set(v___f_1365_, 3, v_resTy_1350_);
lean_closure_set(v___f_1365_, 4, v_c_1351_);
lean_closure_set(v___f_1365_, 5, v_toPure_1352_);
lean_closure_set(v___f_1365_, 6, v_inst_1353_);
lean_closure_set(v___f_1365_, 7, v_inst_1354_);
lean_closure_set(v___f_1365_, 8, v_n_1355_);
lean_closure_set(v___f_1365_, 9, v___x_1363_);
lean_closure_set(v___f_1365_, 10, v_hFalse_1360_);
lean_closure_set(v___f_1365_, 11, v___f_1356_);
lean_closure_set(v___f_1365_, 12, v___x_1364_);
lean_closure_set(v___f_1365_, 13, v_toBind_1357_);
v___x_1366_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1353_, v_inst_1354_, v_n_1355_, v___x_1361_, v_hTrue_1358_, v___f_1359_, v___x_1362_);
v___x_1367_ = lean_apply_4(v_toBind_1357_, lean_box(0), lean_box(0), v___x_1366_, v___f_1365_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18(lean_object* v___x_1369_, lean_object* v_u_1370_, lean_object* v___x_1371_, lean_object* v_resTy_1372_, lean_object* v_c_1373_, lean_object* v_toPure_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_n_1377_, lean_object* v___f_1378_, lean_object* v_toBind_1379_, lean_object* v___f_1380_, lean_object* v_inst_1381_, lean_object* v_hTrue_1382_){
_start:
{
lean_object* v___f_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_inc(v_toBind_1379_);
lean_inc_ref(v_c_1373_);
lean_inc(v___x_1371_);
lean_inc_ref(v___x_1369_);
v___f_1383_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16), 14, 13);
lean_closure_set(v___f_1383_, 0, v___x_1369_);
lean_closure_set(v___f_1383_, 1, v_u_1370_);
lean_closure_set(v___f_1383_, 2, v___x_1371_);
lean_closure_set(v___f_1383_, 3, v_resTy_1372_);
lean_closure_set(v___f_1383_, 4, v_c_1373_);
lean_closure_set(v___f_1383_, 5, v_toPure_1374_);
lean_closure_set(v___f_1383_, 6, v_inst_1375_);
lean_closure_set(v___f_1383_, 7, v_inst_1376_);
lean_closure_set(v___f_1383_, 8, v_n_1377_);
lean_closure_set(v___f_1383_, 9, v___f_1378_);
lean_closure_set(v___f_1383_, 10, v_toBind_1379_);
lean_closure_set(v___f_1383_, 11, v_hTrue_1382_);
lean_closure_set(v___f_1383_, 12, v___f_1380_);
v___x_1384_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18___closed__0));
v___x_1385_ = l_Lean_Name_mkStr2(v___x_1369_, v___x_1384_);
v___x_1386_ = l_Lean_mkConst(v___x_1385_, v___x_1371_);
v___x_1387_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_1387_, 0, v_c_1373_);
lean_closure_set(v___x_1387_, 1, v___x_1386_);
v___x_1388_ = lean_apply_2(v_inst_1381_, lean_box(0), v___x_1387_);
v___x_1389_ = lean_apply_4(v_toBind_1379_, lean_box(0), lean_box(0), v___x_1388_, v___f_1383_);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = lean_box(0);
v___x_1395_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1));
v___x_1396_ = l_Lean_mkConst(v___x_1395_, v___x_1394_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19(lean_object* v_u_1397_, lean_object* v_resTy_1398_, lean_object* v_c_1399_, lean_object* v_toPure_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v___f_1403_, lean_object* v_toBind_1404_, lean_object* v___f_1405_, lean_object* v_inst_1406_, lean_object* v_n_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___f_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1408_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10));
v___x_1409_ = lean_box(0);
lean_inc(v_inst_1406_);
lean_inc(v_toBind_1404_);
lean_inc_ref(v_c_1399_);
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__18), 14, 13);
lean_closure_set(v___f_1410_, 0, v___x_1408_);
lean_closure_set(v___f_1410_, 1, v_u_1397_);
lean_closure_set(v___f_1410_, 2, v___x_1409_);
lean_closure_set(v___f_1410_, 3, v_resTy_1398_);
lean_closure_set(v___f_1410_, 4, v_c_1399_);
lean_closure_set(v___f_1410_, 5, v_toPure_1400_);
lean_closure_set(v___f_1410_, 6, v_inst_1401_);
lean_closure_set(v___f_1410_, 7, v_inst_1402_);
lean_closure_set(v___f_1410_, 8, v_n_1407_);
lean_closure_set(v___f_1410_, 9, v___f_1403_);
lean_closure_set(v___f_1410_, 10, v_toBind_1404_);
lean_closure_set(v___f_1410_, 11, v___f_1405_);
lean_closure_set(v___f_1410_, 12, v_inst_1406_);
v___x_1411_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2, &l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__2);
v___x_1412_ = lean_alloc_closure((void*)(l_Lean_Meta_mkEq___boxed), 7, 2);
lean_closure_set(v___x_1412_, 0, v_c_1399_);
lean_closure_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_apply_2(v_inst_1406_, lean_box(0), v___x_1412_);
v___x_1414_ = lean_apply_4(v_toBind_1404_, lean_box(0), lean_box(0), v___x_1413_, v___f_1410_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(lean_object* v_e_1415_, uint8_t v_useSplitter_1416_, lean_object* v_resTy_1417_, lean_object* v_toPure_1418_, lean_object* v_onAlt_1419_, lean_object* v_toBind_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_u_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v_c_1429_; 
v___x_1425_ = lean_unsigned_to_nat(1u);
v___x_1426_ = l_Lean_Expr_getAppNumArgs(v_e_1415_);
v___x_1427_ = lean_nat_sub(v___x_1426_, v___x_1425_);
lean_dec(v___x_1426_);
v___x_1428_ = lean_nat_sub(v___x_1427_, v___x_1425_);
lean_dec(v___x_1427_);
v_c_1429_ = l_Lean_Expr_getRevArg_x21(v_e_1415_, v___x_1428_);
if (v_useSplitter_1416_ == 0)
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___f_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec_ref(v_inst_1423_);
lean_dec_ref(v_inst_1422_);
lean_dec(v_inst_1421_);
v___x_1430_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1420_);
lean_inc(v_onAlt_1419_);
lean_inc_ref(v_resTy_1417_);
v___f_1433_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14), 9, 8);
lean_closure_set(v___f_1433_, 0, v_u_1424_);
lean_closure_set(v___f_1433_, 1, v_resTy_1417_);
lean_closure_set(v___f_1433_, 2, v_c_1429_);
lean_closure_set(v___f_1433_, 3, v_toPure_1418_);
lean_closure_set(v___f_1433_, 4, v_onAlt_1419_);
lean_closure_set(v___f_1433_, 5, v___x_1425_);
lean_closure_set(v___f_1433_, 6, v___x_1432_);
lean_closure_set(v___f_1433_, 7, v_toBind_1420_);
v___x_1434_ = lean_apply_4(v_onAlt_1419_, v___x_1430_, v_resTy_1417_, v___x_1431_, v___x_1432_);
v___x_1435_ = lean_apply_4(v_toBind_1420_, lean_box(0), lean_box(0), v___x_1434_, v___f_1433_);
return v___x_1435_;
}
else
{
lean_object* v___x_1436_; lean_object* v___f_1437_; lean_object* v___x_1438_; lean_object* v___f_1439_; lean_object* v___f_1440_; lean_object* v___f_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1436_ = lean_box(v_useSplitter_1416_);
lean_inc_n(v_toBind_1420_, 3);
lean_inc_ref_n(v_resTy_1417_, 2);
lean_inc(v_onAlt_1419_);
lean_inc_n(v_inst_1421_, 3);
v___f_1437_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1437_, 0, v___x_1425_);
lean_closure_set(v___f_1437_, 1, v___x_1436_);
lean_closure_set(v___f_1437_, 2, v_inst_1421_);
lean_closure_set(v___f_1437_, 3, v_onAlt_1419_);
lean_closure_set(v___f_1437_, 4, v_resTy_1417_);
lean_closure_set(v___f_1437_, 5, v_toBind_1420_);
v___x_1438_ = lean_box(v_useSplitter_1416_);
v___f_1439_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1439_, 0, v___x_1425_);
lean_closure_set(v___f_1439_, 1, v___x_1438_);
lean_closure_set(v___f_1439_, 2, v_inst_1421_);
lean_closure_set(v___f_1439_, 3, v_onAlt_1419_);
lean_closure_set(v___f_1439_, 4, v_resTy_1417_);
lean_closure_set(v___f_1439_, 5, v_toBind_1420_);
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19), 11, 10);
lean_closure_set(v___f_1440_, 0, v_u_1424_);
lean_closure_set(v___f_1440_, 1, v_resTy_1417_);
lean_closure_set(v___f_1440_, 2, v_c_1429_);
lean_closure_set(v___f_1440_, 3, v_toPure_1418_);
lean_closure_set(v___f_1440_, 4, v_inst_1422_);
lean_closure_set(v___f_1440_, 5, v_inst_1423_);
lean_closure_set(v___f_1440_, 6, v___f_1439_);
lean_closure_set(v___f_1440_, 7, v_toBind_1420_);
lean_closure_set(v___f_1440_, 8, v___f_1437_);
lean_closure_set(v___f_1440_, 9, v_inst_1421_);
v___f_1441_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1442_ = lean_apply_2(v_inst_1421_, lean_box(0), v___f_1441_);
v___x_1443_ = lean_apply_4(v_toBind_1420_, lean_box(0), lean_box(0), v___x_1442_, v___f_1440_);
return v___x_1443_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22___boxed(lean_object* v_e_1444_, lean_object* v_useSplitter_1445_, lean_object* v_resTy_1446_, lean_object* v_toPure_1447_, lean_object* v_onAlt_1448_, lean_object* v_toBind_1449_, lean_object* v_inst_1450_, lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_u_1453_){
_start:
{
uint8_t v_useSplitter_boxed_1454_; lean_object* v_res_1455_; 
v_useSplitter_boxed_1454_ = lean_unbox(v_useSplitter_1445_);
v_res_1455_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22(v_e_1444_, v_useSplitter_boxed_1454_, v_resTy_1446_, v_toPure_1447_, v_onAlt_1448_, v_toBind_1449_, v_inst_1450_, v_inst_1451_, v_inst_1452_, v_u_1453_);
lean_dec_ref(v_e_1444_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21(lean_object* v_onAlt_1456_, lean_object* v_idx_1457_, lean_object* v_expAltType_1458_, lean_object* v_altFVars_1459_, lean_object* v___alt_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1461_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2));
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_add(v_idx_1457_, v___x_1462_);
v___x_1464_ = lean_name_append_index_after(v___x_1461_, v___x_1463_);
v___x_1465_ = lean_apply_4(v_onAlt_1456_, v___x_1464_, v_expAltType_1458_, v_idx_1457_, v_altFVars_1459_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21___boxed(lean_object* v_onAlt_1466_, lean_object* v_idx_1467_, lean_object* v_expAltType_1468_, lean_object* v_altFVars_1469_, lean_object* v___alt_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21(v_onAlt_1466_, v_idx_1467_, v_expAltType_1468_, v_altFVars_1469_, v___alt_1470_);
lean_dec_ref(v___alt_1470_);
return v_res_1471_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(lean_object* v_toMatcherInfo_1472_, lean_object* v_i_1473_, lean_object* v_a_1474_, lean_object* v_x_1475_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = l_Lean_Expr_isFVar(v_a_1474_);
if (v___x_1476_ == 0)
{
return v___x_1476_;
}
else
{
lean_object* v_discrInfos_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; 
v_discrInfos_1477_ = lean_ctor_get(v_toMatcherInfo_1472_, 4);
v___x_1478_ = lean_array_get_size(v_discrInfos_1477_);
v___x_1479_ = lean_nat_dec_lt(v_i_1473_, v___x_1478_);
if (v___x_1479_ == 0)
{
return v___x_1476_;
}
else
{
lean_object* v___x_1480_; 
v___x_1480_ = lean_array_fget_borrowed(v_discrInfos_1477_, v_i_1473_);
if (lean_obj_tag(v___x_1480_) == 0)
{
return v___x_1476_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = 0;
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23___boxed(lean_object* v_toMatcherInfo_1482_, lean_object* v_i_1483_, lean_object* v_a_1484_, lean_object* v_x_1485_){
_start:
{
uint8_t v_res_1486_; lean_object* v_r_1487_; 
v_res_1486_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23(v_toMatcherInfo_1482_, v_i_1483_, v_a_1484_, v_x_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_i_1483_);
lean_dec_ref(v_toMatcherInfo_1482_);
v_r_1487_ = lean_box(v_res_1486_);
return v_r_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24(lean_object* v_mask_1488_, lean_object* v_absMotiveBody_1489_, lean_object* v_toPure_1490_, lean_object* v_xs_1491_, lean_object* v___body_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1493_ = l_Lean_Array_mask___redArg(v_mask_1488_, v_xs_1491_);
v___x_1494_ = lean_expr_instantiate_rev(v_absMotiveBody_1489_, v___x_1493_);
lean_dec(v___x_1493_);
v___x_1495_ = lean_apply_2(v_toPure_1490_, lean_box(0), v___x_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24___boxed(lean_object* v_mask_1496_, lean_object* v_absMotiveBody_1497_, lean_object* v_toPure_1498_, lean_object* v_xs_1499_, lean_object* v___body_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24(v_mask_1496_, v_absMotiveBody_1497_, v_toPure_1498_, v_xs_1499_, v___body_1500_);
lean_dec_ref(v___body_1500_);
lean_dec_ref(v_absMotiveBody_1497_);
lean_dec_ref(v_mask_1496_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(lean_object* v_toFunctor_1502_, lean_object* v_mask_1503_, lean_object* v_toPure_1504_, lean_object* v_inst_1505_, lean_object* v_inst_1506_, lean_object* v_inst_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_matcherApp_1510_, uint8_t v_useSplitter_1511_, lean_object* v___f_1512_, lean_object* v___f_1513_, lean_object* v_absMotiveBody_1514_){
_start:
{
lean_object* v_map_1515_; lean_object* v___f_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_map_1515_ = lean_ctor_get(v_toFunctor_1502_, 0);
lean_inc(v_map_1515_);
lean_dec_ref(v_toFunctor_1502_);
lean_inc(v_toPure_1504_);
v___f_1516_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__24___boxed), 5, 3);
lean_closure_set(v___f_1516_, 0, v_mask_1503_);
lean_closure_set(v___f_1516_, 1, v_absMotiveBody_1514_);
lean_closure_set(v___f_1516_, 2, v_toPure_1504_);
v___x_1517_ = lean_apply_1(v_toPure_1504_, lean_box(0));
lean_inc(v___x_1517_);
v___x_1518_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_1505_, v_inst_1506_, v_inst_1507_, v_inst_1508_, v_inst_1509_, v_matcherApp_1510_, v_useSplitter_1511_, v_useSplitter_1511_, v___x_1517_, v___f_1516_, v___f_1512_, v___x_1517_);
v___x_1519_ = lean_apply_4(v_map_1515_, lean_box(0), lean_box(0), v___f_1513_, v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25___boxed(lean_object* v_toFunctor_1520_, lean_object* v_mask_1521_, lean_object* v_toPure_1522_, lean_object* v_inst_1523_, lean_object* v_inst_1524_, lean_object* v_inst_1525_, lean_object* v_inst_1526_, lean_object* v_inst_1527_, lean_object* v_matcherApp_1528_, lean_object* v_useSplitter_1529_, lean_object* v___f_1530_, lean_object* v___f_1531_, lean_object* v_absMotiveBody_1532_){
_start:
{
uint8_t v_useSplitter_boxed_1533_; lean_object* v_res_1534_; 
v_useSplitter_boxed_1533_ = lean_unbox(v_useSplitter_1529_);
v_res_1534_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25(v_toFunctor_1520_, v_mask_1521_, v_toPure_1522_, v_inst_1523_, v_inst_1524_, v_inst_1525_, v_inst_1526_, v_inst_1527_, v_matcherApp_1528_, v_useSplitter_boxed_1533_, v___f_1530_, v___f_1531_, v_absMotiveBody_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object* v_inst_1536_, lean_object* v_inst_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_inst_1540_, lean_object* v_info_1541_, lean_object* v_resTy_1542_, lean_object* v_onAlt_1543_, uint8_t v_useSplitter_1544_){
_start:
{
switch(lean_obj_tag(v_info_1541_))
{
case 0:
{
lean_object* v_toApplicative_1545_; lean_object* v_toBind_1546_; lean_object* v_toPure_1547_; lean_object* v_e_1548_; lean_object* v___x_1549_; lean_object* v___f_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v_toApplicative_1545_ = lean_ctor_get(v_inst_1538_, 0);
lean_dec_ref(v_inst_1540_);
lean_dec_ref(v_inst_1539_);
v_toBind_1546_ = lean_ctor_get(v_inst_1538_, 1);
lean_inc_n(v_toBind_1546_, 2);
v_toPure_1547_ = lean_ctor_get(v_toApplicative_1545_, 1);
lean_inc(v_toPure_1547_);
v_e_1548_ = lean_ctor_get(v_info_1541_, 0);
lean_inc_ref(v_e_1548_);
lean_dec_ref_known(v_info_1541_, 1);
v___x_1549_ = lean_box(v_useSplitter_1544_);
lean_inc(v_inst_1536_);
lean_inc_ref(v_resTy_1542_);
v___f_1550_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1550_, 0, v_e_1548_);
lean_closure_set(v___f_1550_, 1, v___x_1549_);
lean_closure_set(v___f_1550_, 2, v_resTy_1542_);
lean_closure_set(v___f_1550_, 3, v_toPure_1547_);
lean_closure_set(v___f_1550_, 4, v_onAlt_1543_);
lean_closure_set(v___f_1550_, 5, v_toBind_1546_);
lean_closure_set(v___f_1550_, 6, v_inst_1536_);
lean_closure_set(v___f_1550_, 7, v_inst_1537_);
lean_closure_set(v___f_1550_, 8, v_inst_1538_);
v___x_1551_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1551_, 0, v_resTy_1542_);
v___x_1552_ = lean_apply_2(v_inst_1536_, lean_box(0), v___x_1551_);
v___x_1553_ = lean_apply_4(v_toBind_1546_, lean_box(0), lean_box(0), v___x_1552_, v___f_1550_);
return v___x_1553_;
}
case 1:
{
lean_object* v_toApplicative_1554_; lean_object* v_toBind_1555_; lean_object* v_toPure_1556_; lean_object* v_e_1557_; lean_object* v___f_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_toApplicative_1554_ = lean_ctor_get(v_inst_1538_, 0);
lean_dec_ref(v_inst_1540_);
lean_dec_ref(v_inst_1539_);
v_toBind_1555_ = lean_ctor_get(v_inst_1538_, 1);
lean_inc_n(v_toBind_1555_, 3);
v_toPure_1556_ = lean_ctor_get(v_toApplicative_1554_, 1);
lean_inc(v_toPure_1556_);
v_e_1557_ = lean_ctor_get(v_info_1541_, 0);
lean_inc_ref(v_e_1557_);
lean_dec_ref_known(v_info_1541_, 1);
lean_inc_ref_n(v_resTy_1542_, 2);
lean_inc(v_onAlt_1543_);
lean_inc_n(v_inst_1536_, 2);
v___f_1558_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11), 5, 4);
lean_closure_set(v___f_1558_, 0, v_inst_1536_);
lean_closure_set(v___f_1558_, 1, v_onAlt_1543_);
lean_closure_set(v___f_1558_, 2, v_resTy_1542_);
lean_closure_set(v___f_1558_, 3, v_toBind_1555_);
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed), 10, 9);
lean_closure_set(v___f_1559_, 0, v_inst_1536_);
lean_closure_set(v___f_1559_, 1, v_onAlt_1543_);
lean_closure_set(v___f_1559_, 2, v_resTy_1542_);
lean_closure_set(v___f_1559_, 3, v_toBind_1555_);
lean_closure_set(v___f_1559_, 4, v_e_1557_);
lean_closure_set(v___f_1559_, 5, v_toPure_1556_);
lean_closure_set(v___f_1559_, 6, v_inst_1537_);
lean_closure_set(v___f_1559_, 7, v_inst_1538_);
lean_closure_set(v___f_1559_, 8, v___f_1558_);
v___x_1560_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1560_, 0, v_resTy_1542_);
v___x_1561_ = lean_apply_2(v_inst_1536_, lean_box(0), v___x_1560_);
v___x_1562_ = lean_apply_4(v_toBind_1555_, lean_box(0), lean_box(0), v___x_1561_, v___f_1559_);
return v___x_1562_;
}
case 2:
{
lean_object* v_toApplicative_1563_; lean_object* v_toBind_1564_; lean_object* v_toPure_1565_; lean_object* v_e_1566_; lean_object* v___x_1567_; lean_object* v___f_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_toApplicative_1563_ = lean_ctor_get(v_inst_1538_, 0);
lean_dec_ref(v_inst_1540_);
lean_dec_ref(v_inst_1539_);
v_toBind_1564_ = lean_ctor_get(v_inst_1538_, 1);
lean_inc_n(v_toBind_1564_, 2);
v_toPure_1565_ = lean_ctor_get(v_toApplicative_1563_, 1);
lean_inc(v_toPure_1565_);
v_e_1566_ = lean_ctor_get(v_info_1541_, 0);
lean_inc_ref(v_e_1566_);
lean_dec_ref_known(v_info_1541_, 1);
v___x_1567_ = lean_box(v_useSplitter_1544_);
lean_inc(v_inst_1536_);
lean_inc_ref(v_resTy_1542_);
v___f_1568_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__22___boxed), 10, 9);
lean_closure_set(v___f_1568_, 0, v_e_1566_);
lean_closure_set(v___f_1568_, 1, v___x_1567_);
lean_closure_set(v___f_1568_, 2, v_resTy_1542_);
lean_closure_set(v___f_1568_, 3, v_toPure_1565_);
lean_closure_set(v___f_1568_, 4, v_onAlt_1543_);
lean_closure_set(v___f_1568_, 5, v_toBind_1564_);
lean_closure_set(v___f_1568_, 6, v_inst_1536_);
lean_closure_set(v___f_1568_, 7, v_inst_1537_);
lean_closure_set(v___f_1568_, 8, v_inst_1538_);
v___x_1569_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1569_, 0, v_resTy_1542_);
v___x_1570_ = lean_apply_2(v_inst_1536_, lean_box(0), v___x_1569_);
v___x_1571_ = lean_apply_4(v_toBind_1564_, lean_box(0), lean_box(0), v___x_1570_, v___f_1568_);
return v___x_1571_;
}
default: 
{
lean_object* v_toApplicative_1572_; lean_object* v_matcherApp_1573_; lean_object* v_toBind_1574_; lean_object* v_toFunctor_1575_; lean_object* v_toPure_1576_; lean_object* v_toMatcherInfo_1577_; lean_object* v_discrs_1578_; lean_object* v___f_1579_; lean_object* v___f_1580_; lean_object* v___f_1581_; lean_object* v___x_1582_; size_t v_sz_1583_; size_t v___x_1584_; lean_object* v_mask_1585_; lean_object* v___x_1586_; lean_object* v___f_1587_; lean_object* v_maskedDiscrs_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v_toApplicative_1572_ = lean_ctor_get(v_inst_1538_, 0);
v_matcherApp_1573_ = lean_ctor_get(v_info_1541_, 0);
lean_inc_ref(v_matcherApp_1573_);
lean_dec_ref_known(v_info_1541_, 1);
v_toBind_1574_ = lean_ctor_get(v_inst_1538_, 1);
lean_inc(v_toBind_1574_);
v_toFunctor_1575_ = lean_ctor_get(v_toApplicative_1572_, 0);
lean_inc_ref(v_toFunctor_1575_);
v_toPure_1576_ = lean_ctor_get(v_toApplicative_1572_, 1);
lean_inc(v_toPure_1576_);
v_toMatcherInfo_1577_ = lean_ctor_get(v_matcherApp_1573_, 0);
v_discrs_1578_ = lean_ctor_get(v_matcherApp_1573_, 5);
lean_inc_ref_n(v_discrs_1578_, 2);
v___f_1579_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__21___boxed), 5, 1);
lean_closure_set(v___f_1579_, 0, v_onAlt_1543_);
v___f_1580_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0));
lean_inc_ref(v_toMatcherInfo_1577_);
v___f_1581_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__23___boxed), 4, 1);
lean_closure_set(v___f_1581_, 0, v_toMatcherInfo_1577_);
v___x_1582_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___closed__9));
v_sz_1583_ = lean_array_size(v_discrs_1578_);
v___x_1584_ = ((size_t)0ULL);
v_mask_1585_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1582_, v_discrs_1578_, v___f_1581_, v_sz_1583_, v___x_1584_, v_discrs_1578_);
v___x_1586_ = lean_box(v_useSplitter_1544_);
lean_inc(v_inst_1536_);
lean_inc(v_mask_1585_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__25___boxed), 13, 12);
lean_closure_set(v___f_1587_, 0, v_toFunctor_1575_);
lean_closure_set(v___f_1587_, 1, v_mask_1585_);
lean_closure_set(v___f_1587_, 2, v_toPure_1576_);
lean_closure_set(v___f_1587_, 3, v_inst_1536_);
lean_closure_set(v___f_1587_, 4, v_inst_1537_);
lean_closure_set(v___f_1587_, 5, v_inst_1538_);
lean_closure_set(v___f_1587_, 6, v_inst_1539_);
lean_closure_set(v___f_1587_, 7, v_inst_1540_);
lean_closure_set(v___f_1587_, 8, v_matcherApp_1573_);
lean_closure_set(v___f_1587_, 9, v___x_1586_);
lean_closure_set(v___f_1587_, 10, v___f_1579_);
lean_closure_set(v___f_1587_, 11, v___f_1580_);
v_maskedDiscrs_1588_ = l_Lean_Array_mask___redArg(v_mask_1585_, v_discrs_1578_);
lean_dec(v_mask_1585_);
v___x_1589_ = lean_alloc_closure((void*)(l_Lean_Expr_abstractM___boxed), 7, 2);
lean_closure_set(v___x_1589_, 0, v_resTy_1542_);
lean_closure_set(v___x_1589_, 1, v_maskedDiscrs_1588_);
v___x_1590_ = lean_apply_2(v_inst_1536_, lean_box(0), v___x_1589_);
v___x_1591_ = lean_apply_4(v_toBind_1574_, lean_box(0), lean_box(0), v___x_1590_, v___f_1587_);
return v___x_1591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object* v_inst_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_info_1597_, lean_object* v_resTy_1598_, lean_object* v_onAlt_1599_, lean_object* v_useSplitter_1600_){
_start:
{
uint8_t v_useSplitter_boxed_1601_; lean_object* v_res_1602_; 
v_useSplitter_boxed_1601_ = lean_unbox(v_useSplitter_1600_);
v_res_1602_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1592_, v_inst_1593_, v_inst_1594_, v_inst_1595_, v_inst_1596_, v_info_1597_, v_resTy_1598_, v_onAlt_1599_, v_useSplitter_boxed_1601_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object* v_n_1603_, lean_object* v_inst_1604_, lean_object* v_inst_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_inst_1610_, lean_object* v_inst_1611_, lean_object* v_info_1612_, lean_object* v_resTy_1613_, lean_object* v_onAlt_1614_, uint8_t v_useSplitter_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1604_, v_inst_1605_, v_inst_1606_, v_inst_1607_, v_inst_1608_, v_info_1612_, v_resTy_1613_, v_onAlt_1614_, v_useSplitter_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object* v_n_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_, lean_object* v_info_1626_, lean_object* v_resTy_1627_, lean_object* v_onAlt_1628_, lean_object* v_useSplitter_1629_){
_start:
{
uint8_t v_useSplitter_boxed_1630_; lean_object* v_res_1631_; 
v_useSplitter_boxed_1630_ = lean_unbox(v_useSplitter_1629_);
v_res_1631_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(v_n_1617_, v_inst_1618_, v_inst_1619_, v_inst_1620_, v_inst_1621_, v_inst_1622_, v_inst_1623_, v_inst_1624_, v_inst_1625_, v_info_1626_, v_resTy_1627_, v_onAlt_1628_, v_useSplitter_boxed_1630_);
lean_dec_ref(v_inst_1625_);
lean_dec(v_inst_1624_);
lean_dec_ref(v_inst_1623_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object* v_info_1632_, lean_object* v_e_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
if (lean_obj_tag(v_info_1632_) == 3)
{
lean_object* v_matcherApp_1642_; lean_object* v_toMatcherInfo_1643_; lean_object* v___x_1644_; 
v_matcherApp_1642_ = lean_ctor_get(v_info_1632_, 0);
lean_inc_ref(v_matcherApp_1642_);
lean_dec_ref_known(v_info_1632_, 1);
v_toMatcherInfo_1643_ = lean_ctor_get(v_matcherApp_1642_, 0);
lean_inc_ref(v_toMatcherInfo_1643_);
lean_dec_ref(v_matcherApp_1642_);
v___x_1644_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_toMatcherInfo_1643_, v_e_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
return v___x_1644_;
}
else
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
lean_dec_ref(v_e_1633_);
lean_dec_ref(v_info_1632_);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
return v___x_1646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object* v_info_1647_, lean_object* v_e_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(v_info_1647_, v_e_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec_ref(v_a_1652_);
lean_dec(v_a_1651_);
lean_dec_ref(v_a_1650_);
lean_dec(v_a_1649_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object* v_declName_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v___x_1661_; lean_object* v_env_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1661_ = lean_st_ref_get(v___y_1659_);
v_env_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc_ref(v_env_1662_);
lean_dec(v___x_1661_);
v___x_1663_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1662_, v_declName_1658_);
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object* v_declName_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1665_, v___y_1666_);
lean_dec(v___y_1666_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; lean_object* v_env_1676_; uint8_t v___x_1677_; lean_object* v_env_1678_; lean_object* v___x_1679_; lean_object* v_toCold_1680_; lean_object* v_mctx_1681_; lean_object* v_lctx_1682_; lean_object* v_options_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1675_ = lean_st_ref_get(v___y_1673_);
v_env_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc_ref(v_env_1676_);
lean_dec(v___x_1675_);
v___x_1677_ = 0;
v_env_1678_ = l_Lean_Environment_setRecordingDeps(v_env_1676_, v___x_1677_);
v___x_1679_ = lean_st_ref_get(v___y_1671_);
v_toCold_1680_ = lean_ctor_get(v___y_1672_, 0);
v_mctx_1681_ = lean_ctor_get(v___x_1679_, 0);
lean_inc_ref(v_mctx_1681_);
lean_dec(v___x_1679_);
v_lctx_1682_ = lean_ctor_get(v___y_1670_, 2);
v_options_1683_ = lean_ctor_get(v_toCold_1680_, 2);
lean_inc_ref(v_options_1683_);
lean_inc_ref(v_lctx_1682_);
v___x_1684_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1684_, 0, v_env_1678_);
lean_ctor_set(v___x_1684_, 1, v_mctx_1681_);
lean_ctor_set(v___x_1684_, 2, v_lctx_1682_);
lean_ctor_set(v___x_1684_, 3, v_options_1683_);
v___x_1685_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1684_);
lean_ctor_set(v___x_1685_, 1, v_msgData_1669_);
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
v_ref_1700_ = lean_ctor_get(v___y_1697_, 2);
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
lean_object* v_toCold_1725_; lean_object* v_currRecDepth_1726_; lean_object* v_ref_1727_; uint16_t v_optionFlags_1728_; uint8_t v_suppressElabErrors_1729_; uint8_t v_isRecordingDeps_1730_; lean_object* v_ref_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_toCold_1725_ = lean_ctor_get(v___y_1722_, 0);
v_currRecDepth_1726_ = lean_ctor_get(v___y_1722_, 1);
v_ref_1727_ = lean_ctor_get(v___y_1722_, 2);
v_optionFlags_1728_ = lean_ctor_get_uint16(v___y_1722_, sizeof(void*)*3);
v_suppressElabErrors_1729_ = lean_ctor_get_uint8(v___y_1722_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1730_ = lean_ctor_get_uint8(v___y_1722_, sizeof(void*)*3 + 3);
v_ref_1731_ = l_Lean_replaceRef(v_ref_1718_, v_ref_1727_);
lean_inc(v_currRecDepth_1726_);
lean_inc_ref(v_toCold_1725_);
v___x_1732_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1732_, 0, v_toCold_1725_);
lean_ctor_set(v___x_1732_, 1, v_currRecDepth_1726_);
lean_ctor_set(v___x_1732_, 2, v_ref_1731_);
lean_ctor_set_uint16(v___x_1732_, sizeof(void*)*3, v_optionFlags_1728_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 2, v_suppressElabErrors_1729_);
lean_ctor_set_uint8(v___x_1732_, sizeof(void*)*3 + 3, v_isRecordingDeps_1730_);
v___x_1733_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1719_, v___y_1720_, v___y_1721_, v___x_1732_, v___y_1723_);
lean_dec_ref_known(v___x_1732_, 3);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1734_, lean_object* v_msg_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1734_, v_msg_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1739_);
lean_dec_ref(v___y_1738_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v_ref_1734_);
return v_res_1741_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1742_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1743_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1745_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1746_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1747_ = lean_unsigned_to_nat(0u);
v___x_1748_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v___x_1747_);
lean_ctor_set(v___x_1748_, 2, v___x_1747_);
lean_ctor_set(v___x_1748_, 3, v___x_1747_);
lean_ctor_set(v___x_1748_, 4, v___x_1746_);
lean_ctor_set(v___x_1748_, 5, v___x_1746_);
lean_ctor_set(v___x_1748_, 6, v___x_1746_);
lean_ctor_set(v___x_1748_, 7, v___x_1746_);
lean_ctor_set(v___x_1748_, 8, v___x_1746_);
lean_ctor_set(v___x_1748_, 9, v___x_1746_);
lean_ctor_set(v___x_1748_, 10, v___x_1746_);
lean_ctor_set(v___x_1748_, 11, v___x_1745_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1749_ = lean_unsigned_to_nat(32u);
v___x_1750_ = lean_mk_empty_array_with_capacity(v___x_1749_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
return v___x_1751_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
v___x_1752_ = ((size_t)5ULL);
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = lean_unsigned_to_nat(32u);
v___x_1755_ = lean_mk_empty_array_with_capacity(v___x_1754_);
v___x_1756_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_1757_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1757_, 0, v___x_1756_);
lean_ctor_set(v___x_1757_, 1, v___x_1755_);
lean_ctor_set(v___x_1757_, 2, v___x_1753_);
lean_ctor_set(v___x_1757_, 3, v___x_1753_);
lean_ctor_set_usize(v___x_1757_, 4, v___x_1752_);
return v___x_1757_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1758_ = lean_box(1);
v___x_1759_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_1760_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
lean_ctor_set(v___x_1761_, 1, v___x_1759_);
lean_ctor_set(v___x_1761_, 2, v___x_1758_);
return v___x_1761_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; 
v___x_1763_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_1764_ = l_Lean_stringToMessageData(v___x_1763_);
return v___x_1764_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_1767_ = l_Lean_stringToMessageData(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_1770_ = l_Lean_stringToMessageData(v___x_1769_);
return v___x_1770_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_1773_ = l_Lean_stringToMessageData(v___x_1772_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_1776_ = l_Lean_stringToMessageData(v___x_1775_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_1779_ = l_Lean_stringToMessageData(v___x_1778_);
return v___x_1779_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_1782_ = l_Lean_stringToMessageData(v___x_1781_);
return v___x_1782_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__20));
v___x_1785_ = l_Lean_stringToMessageData(v___x_1784_);
return v___x_1785_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1787_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__22));
v___x_1788_ = l_Lean_stringToMessageData(v___x_1787_);
return v___x_1788_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1790_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__24));
v___x_1791_ = l_Lean_stringToMessageData(v___x_1790_);
return v___x_1791_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27(void){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1793_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__26));
v___x_1794_ = l_Lean_stringToMessageData(v___x_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_1795_, lean_object* v_declHint_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v_env_1801_; uint8_t v___x_1802_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_st_ref_get(v___y_1797_);
v_env_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc_ref(v_env_1801_);
lean_dec(v___x_1800_);
v___x_1802_ = l_Lean_Name_isAnonymous(v_declHint_1796_);
if (v___x_1802_ == 0)
{
uint8_t v_isExporting_1803_; 
v_isExporting_1803_ = lean_ctor_get_uint8(v_env_1801_, sizeof(void*)*13);
if (v_isExporting_1803_ == 0)
{
lean_object* v___x_1804_; 
lean_dec_ref(v_env_1801_);
lean_dec(v_declHint_1796_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_msg_1795_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
lean_inc_ref(v_env_1801_);
v___x_1805_ = l_Lean_Environment_setExporting(v_env_1801_, v___x_1802_);
lean_inc(v_declHint_1796_);
lean_inc_ref(v___x_1805_);
v___x_1806_ = l_Lean_Environment_contains(v___x_1805_, v_declHint_1796_, v_isExporting_1803_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v___x_1805_);
lean_dec_ref(v_env_1801_);
lean_dec(v_declHint_1796_);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_msg_1795_);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_c_1813_; lean_object* v___x_1814_; 
v___x_1808_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_1809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_1810_ = l_Lean_Options_empty;
v___x_1811_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1805_);
lean_ctor_set(v___x_1811_, 1, v___x_1808_);
lean_ctor_set(v___x_1811_, 2, v___x_1809_);
lean_ctor_set(v___x_1811_, 3, v___x_1810_);
lean_inc(v_declHint_1796_);
v___x_1812_ = l_Lean_MessageData_ofConstName(v_declHint_1796_, v___x_1802_);
v_c_1813_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1813_, 0, v___x_1811_);
lean_ctor_set(v_c_1813_, 1, v___x_1812_);
v___x_1814_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1801_, v_declHint_1796_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec_ref(v_env_1801_);
lean_dec(v_declHint_1796_);
v___x_1815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1815_);
lean_ctor_set(v___x_1816_, 1, v_c_1813_);
v___x_1817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_1818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = l_Lean_MessageData_note(v___x_1818_);
v___x_1820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1820_, 0, v_msg_1795_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v___x_1821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
else
{
lean_object* v_val_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1878_; 
v_val_1822_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1824_ = v___x_1814_;
v_isShared_1825_ = v_isSharedCheck_1878_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_val_1822_);
lean_dec(v___x_1814_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1878_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1826_; lean_object* v_modules_1827_; lean_object* v_moduleNames_1828_; lean_object* v_mod_1829_; uint8_t v___y_1831_; uint8_t v___x_1861_; 
v___x_1826_ = l_Lean_Environment_header(v_env_1801_);
lean_dec_ref(v_env_1801_);
v_modules_1827_ = lean_ctor_get(v___x_1826_, 3);
lean_inc_ref(v_modules_1827_);
v_moduleNames_1828_ = lean_ctor_get(v___x_1826_, 4);
lean_inc_ref(v_moduleNames_1828_);
lean_dec_ref(v___x_1826_);
v_mod_1829_ = lean_array_get(v___x_1799_, v_moduleNames_1828_, v_val_1822_);
lean_dec_ref(v_moduleNames_1828_);
v___x_1861_ = l_Lean_isPrivateName(v_declHint_1796_);
lean_dec(v_declHint_1796_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = lean_array_get_size(v_modules_1827_);
v___x_1863_ = lean_nat_dec_lt(v_val_1822_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_dec_ref(v_modules_1827_);
lean_dec(v_val_1822_);
v___y_1831_ = v___x_1861_;
goto v___jp_1830_;
}
else
{
lean_object* v___x_1864_; lean_object* v_toImport_1865_; uint8_t v_isExported_1866_; 
v___x_1864_ = lean_array_fget(v_modules_1827_, v_val_1822_);
lean_dec(v_val_1822_);
lean_dec_ref(v_modules_1827_);
v_toImport_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc_ref(v_toImport_1865_);
lean_dec(v___x_1864_);
v_isExported_1866_ = lean_ctor_get_uint8(v_toImport_1865_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1865_);
v___y_1831_ = v_isExported_1866_;
goto v___jp_1830_;
}
}
else
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
lean_dec_ref(v_modules_1827_);
lean_del_object(v___x_1824_);
lean_dec(v_val_1822_);
v___x_1867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v_c_1813_);
v___x_1869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__25);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1868_);
lean_ctor_set(v___x_1870_, 1, v___x_1869_);
v___x_1871_ = l_Lean_MessageData_ofName(v_mod_1829_);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__27);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1872_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = l_Lean_MessageData_note(v___x_1874_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v_msg_1795_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
return v___x_1877_;
}
v___jp_1830_:
{
if (v___y_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v_c_1813_);
v___x_1834_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_MessageData_ofName(v_mod_1829_);
v___x_1837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v___x_1838_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_1839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1837_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
v___x_1840_ = l_Lean_MessageData_note(v___x_1839_);
v___x_1841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1841_, 0, v_msg_1795_);
lean_ctor_set(v___x_1841_, 1, v___x_1840_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1841_);
v___x_1843_ = v___x_1824_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1841_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
else
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1845_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_1846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v_c_1813_);
v___x_1847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_1848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1846_);
lean_ctor_set(v___x_1848_, 1, v___x_1847_);
v___x_1849_ = l_Lean_MessageData_ofName(v_mod_1829_);
lean_inc_ref(v___x_1849_);
v___x_1850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1848_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__21);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v___x_1849_);
v___x_1854_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__23);
v___x_1855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1853_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = l_Lean_MessageData_note(v___x_1855_);
v___x_1857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1857_, 0, v_msg_1795_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
if (v_isShared_1825_ == 0)
{
lean_ctor_set_tag(v___x_1824_, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1857_);
v___x_1859_ = v___x_1824_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
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
lean_object* v___x_1879_; 
lean_dec_ref(v_env_1801_);
lean_dec(v_declHint_1796_);
v___x_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1879_, 0, v_msg_1795_);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1880_, lean_object* v_declHint_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1880_, v_declHint_1881_, v___y_1882_);
lean_dec(v___y_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object* v_msg_1885_, lean_object* v_declHint_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1902_; 
v___x_1892_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1885_, v_declHint_1886_, v___y_1890_);
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1902_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1902_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1900_; 
v___x_1897_ = l_Lean_unknownIdentifierMessageTag;
v___x_1898_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1897_);
lean_ctor_set(v___x_1898_, 1, v_a_1893_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1898_);
v___x_1900_ = v___x_1895_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v___x_1898_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1903_, lean_object* v_declHint_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1903_, v_declHint_1904_, v___y_1905_, v___y_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1911_, lean_object* v_msg_1912_, lean_object* v_declHint_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v___x_1919_; lean_object* v_a_1920_; lean_object* v___x_1921_; 
v___x_1919_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1912_, v_declHint_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc(v_a_1920_);
lean_dec_ref(v___x_1919_);
v___x_1921_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1911_, v_a_1920_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1922_, lean_object* v_msg_1923_, lean_object* v_declHint_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1922_, v_msg_1923_, v_declHint_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v_ref_1922_);
return v_res_1930_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_1933_ = l_Lean_stringToMessageData(v___x_1932_);
return v___x_1933_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2));
v___x_1936_ = l_Lean_stringToMessageData(v___x_1935_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1937_, lean_object* v_constName_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; uint8_t v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1944_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1945_ = 0;
lean_inc(v_constName_1938_);
v___x_1946_ = l_Lean_MessageData_ofConstName(v_constName_1938_, v___x_1945_);
v___x_1947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1944_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
v___x_1948_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1937_, v___x_1949_, v_constName_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1951_, lean_object* v_constName_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1951_, v_constName_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v_ref_1951_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_ref_1965_; lean_object* v___x_1966_; 
v_ref_1965_ = lean_ctor_get(v___y_1962_, 2);
v___x_1966_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1965_, v_constName_1959_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object* v_constName_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_){
_start:
{
lean_object* v___x_1980_; lean_object* v_env_1981_; uint8_t v___x_1982_; lean_object* v___x_1983_; 
v___x_1980_ = lean_st_ref_get(v___y_1978_);
v_env_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc_ref(v_env_1981_);
lean_dec(v___x_1980_);
v___x_1982_ = 0;
lean_inc(v_constName_1974_);
v___x_1983_ = l_Lean_Environment_find_x3f(v_env_1981_, v_constName_1974_, v___x_1982_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v___x_1984_; 
v___x_1984_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
return v___x_1984_;
}
else
{
lean_object* v_val_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_constName_1974_);
v_val_1985_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1983_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_val_1985_);
lean_dec(v___x_1983_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 0);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_val_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_1993_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v___y_1995_);
lean_dec_ref(v___y_1994_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object* v_msg_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
lean_object* v___x_2006_; lean_object* v_toApplicative_2007_; lean_object* v_toFunctor_2008_; lean_object* v_toSeq_2009_; lean_object* v_toSeqLeft_2010_; lean_object* v_toSeqRight_2011_; lean_object* v___f_2012_; lean_object* v___f_2013_; lean_object* v___f_2014_; lean_object* v___f_2015_; lean_object* v___x_2016_; lean_object* v___f_2017_; lean_object* v___f_2018_; lean_object* v___f_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v_toApplicative_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2054_; 
v___x_2006_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_2007_ = lean_ctor_get(v___x_2006_, 0);
v_toFunctor_2008_ = lean_ctor_get(v_toApplicative_2007_, 0);
v_toSeq_2009_ = lean_ctor_get(v_toApplicative_2007_, 2);
v_toSeqLeft_2010_ = lean_ctor_get(v_toApplicative_2007_, 3);
v_toSeqRight_2011_ = lean_ctor_get(v_toApplicative_2007_, 4);
v___f_2012_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_2013_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2008_, 2);
v___f_2014_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2014_, 0, v_toFunctor_2008_);
v___f_2015_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2015_, 0, v_toFunctor_2008_);
v___x_2016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2016_, 0, v___f_2014_);
lean_ctor_set(v___x_2016_, 1, v___f_2015_);
lean_inc(v_toSeqRight_2011_);
v___f_2017_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2017_, 0, v_toSeqRight_2011_);
lean_inc(v_toSeqLeft_2010_);
v___f_2018_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2018_, 0, v_toSeqLeft_2010_);
lean_inc(v_toSeq_2009_);
v___f_2019_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2019_, 0, v_toSeq_2009_);
v___x_2020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2020_, 0, v___x_2016_);
lean_ctor_set(v___x_2020_, 1, v___f_2012_);
lean_ctor_set(v___x_2020_, 2, v___f_2019_);
lean_ctor_set(v___x_2020_, 3, v___f_2018_);
lean_ctor_set(v___x_2020_, 4, v___f_2017_);
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set(v___x_2021_, 1, v___f_2013_);
v___x_2022_ = l_StateRefT_x27_instMonad___redArg(v___x_2021_);
v_toApplicative_2023_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2054_ == 0)
{
lean_object* v_unused_2055_; 
v_unused_2055_ = lean_ctor_get(v___x_2022_, 1);
lean_dec(v_unused_2055_);
v___x_2025_ = v___x_2022_;
v_isShared_2026_ = v_isSharedCheck_2054_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_toApplicative_2023_);
lean_dec(v___x_2022_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2054_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v_toFunctor_2027_; lean_object* v_toSeq_2028_; lean_object* v_toSeqLeft_2029_; lean_object* v_toSeqRight_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2052_; 
v_toFunctor_2027_ = lean_ctor_get(v_toApplicative_2023_, 0);
v_toSeq_2028_ = lean_ctor_get(v_toApplicative_2023_, 2);
v_toSeqLeft_2029_ = lean_ctor_get(v_toApplicative_2023_, 3);
v_toSeqRight_2030_ = lean_ctor_get(v_toApplicative_2023_, 4);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_toApplicative_2023_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v_toApplicative_2023_, 1);
lean_dec(v_unused_2053_);
v___x_2032_ = v_toApplicative_2023_;
v_isShared_2033_ = v_isSharedCheck_2052_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_toSeqRight_2030_);
lean_inc(v_toSeqLeft_2029_);
lean_inc(v_toSeq_2028_);
lean_inc(v_toFunctor_2027_);
lean_dec(v_toApplicative_2023_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2052_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___f_2034_; lean_object* v___f_2035_; lean_object* v___f_2036_; lean_object* v___f_2037_; lean_object* v___x_2038_; lean_object* v___f_2039_; lean_object* v___f_2040_; lean_object* v___f_2041_; lean_object* v___x_2043_; 
v___f_2034_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_2035_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_2027_);
v___f_2036_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2036_, 0, v_toFunctor_2027_);
v___f_2037_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2037_, 0, v_toFunctor_2027_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___f_2036_);
lean_ctor_set(v___x_2038_, 1, v___f_2037_);
v___f_2039_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2039_, 0, v_toSeqRight_2030_);
v___f_2040_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2040_, 0, v_toSeqLeft_2029_);
v___f_2041_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2041_, 0, v_toSeq_2028_);
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 4, v___f_2039_);
lean_ctor_set(v___x_2032_, 3, v___f_2040_);
lean_ctor_set(v___x_2032_, 2, v___f_2041_);
lean_ctor_set(v___x_2032_, 1, v___f_2034_);
lean_ctor_set(v___x_2032_, 0, v___x_2038_);
v___x_2043_ = v___x_2032_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___f_2034_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v___f_2041_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v___f_2040_);
lean_ctor_set(v_reuseFailAlloc_2051_, 4, v___f_2039_);
v___x_2043_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2045_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 1, v___f_2035_);
lean_ctor_set(v___x_2025_, 0, v___x_2043_);
v___x_2045_ = v___x_2025_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v___f_2035_);
v___x_2045_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2732__overap_2048_; lean_object* v___x_2049_; 
v___x_2046_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_2047_ = l_instInhabitedOfMonad___redArg(v___x_2045_, v___x_2046_);
v___x_2732__overap_2048_ = lean_panic_fn_borrowed(v___x_2047_, v_msg_2000_);
lean_dec(v___x_2047_);
lean_inc(v___y_2004_);
lean_inc_ref(v___y_2003_);
lean_inc(v___y_2002_);
lean_inc_ref(v___y_2001_);
v___x_2049_ = lean_apply_5(v___x_2732__overap_2048_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, lean_box(0));
return v___x_2049_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object* v_msg_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
return v_res_2062_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2));
v___x_2067_ = lean_unsigned_to_nat(53u);
v___x_2068_ = lean_unsigned_to_nat(62u);
v___x_2069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1));
v___x_2070_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0));
v___x_2071_ = l_mkPanicMessageWithDecl(v___x_2070_, v___x_2069_, v___x_2068_, v___x_2067_, v___x_2066_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t v_sz_2072_, size_t v_i_2073_, lean_object* v_bs_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
uint8_t v___x_2080_; 
v___x_2080_ = lean_usize_dec_lt(v_i_2073_, v_sz_2072_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; 
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_bs_2074_);
return v___x_2081_;
}
else
{
lean_object* v_v_2082_; lean_object* v___x_2083_; lean_object* v_bs_x27_2084_; lean_object* v_a_2086_; lean_object* v___x_2091_; 
v_v_2082_ = lean_array_uget(v_bs_2074_, v_i_2073_);
v___x_2083_ = lean_unsigned_to_nat(0u);
v_bs_x27_2084_ = lean_array_uset(v_bs_2074_, v_i_2073_, v___x_2083_);
v___x_2091_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_2082_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_a_2092_);
lean_dec_ref_known(v___x_2091_, 1);
if (lean_obj_tag(v_a_2092_) == 6)
{
lean_object* v_val_2093_; lean_object* v_numFields_2094_; uint8_t v___x_2095_; lean_object* v___x_2096_; 
v_val_2093_ = lean_ctor_get(v_a_2092_, 0);
lean_inc_ref(v_val_2093_);
lean_dec_ref_known(v_a_2092_, 1);
v_numFields_2094_ = lean_ctor_get(v_val_2093_, 4);
lean_inc(v_numFields_2094_);
lean_dec_ref(v_val_2093_);
v___x_2095_ = 0;
v___x_2096_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2096_, 0, v_numFields_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2083_);
lean_ctor_set_uint8(v___x_2096_, sizeof(void*)*2, v___x_2095_);
v_a_2086_ = v___x_2096_;
goto v___jp_2085_;
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
lean_dec(v_a_2092_);
v___x_2097_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
v___x_2098_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_2097_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v_a_2086_ = v_a_2099_;
goto v___jp_2085_;
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v_bs_x27_2084_);
v_a_2100_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2098_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2098_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref(v_bs_x27_2084_);
v_a_2108_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2091_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2091_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
v___jp_2085_:
{
size_t v___x_2087_; size_t v___x_2088_; lean_object* v___x_2089_; 
v___x_2087_ = ((size_t)1ULL);
v___x_2088_ = lean_usize_add(v_i_2073_, v___x_2087_);
v___x_2089_ = lean_array_uset(v_bs_x27_2084_, v_i_2073_, v_a_2086_);
v_i_2073_ = v___x_2088_;
v_bs_2074_ = v___x_2089_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object* v_sz_2116_, lean_object* v_i_2117_, lean_object* v_bs_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
size_t v_sz_boxed_2124_; size_t v_i_boxed_2125_; lean_object* v_res_2126_; 
v_sz_boxed_2124_ = lean_unbox_usize(v_sz_2116_);
lean_dec(v_sz_2116_);
v_i_boxed_2125_ = lean_unbox_usize(v_i_2117_);
lean_dec(v_i_2117_);
v_res_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_2124_, v_i_boxed_2125_, v_bs_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
return v_res_2126_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2127_; lean_object* v_dummy_2128_; 
v___x_2127_ = lean_box(0);
v_dummy_2128_ = l_Lean_Expr_sort___override(v___x_2127_);
return v_dummy_2128_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_box(0);
v___x_2130_ = lean_unsigned_to_nat(16u);
v___x_2131_ = lean_mk_array(v___x_2130_, v___x_2129_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
v___x_2133_ = lean_unsigned_to_nat(0u);
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
lean_ctor_set(v___x_2134_, 1, v___x_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object* v_e_2137_, uint8_t v_alsoCasesOn_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v___x_2147_; 
v___x_2147_ = l_Lean_Expr_isApp(v_e_2137_);
if (v___x_2147_ == 0)
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec_ref(v_e_2137_);
v___x_2148_ = lean_box(0);
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2148_);
return v___x_2149_;
}
else
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_Expr_getAppFn(v_e_2137_);
if (lean_obj_tag(v___x_2150_) == 4)
{
lean_object* v_declName_2151_; lean_object* v_us_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2307_; 
v_declName_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc_n(v_declName_2151_, 2);
v_us_2152_ = lean_ctor_get(v___x_2150_, 1);
lean_inc(v_us_2152_);
lean_dec_ref_known(v___x_2150_, 2);
v___x_2153_ = l_Lean_instInhabitedExpr;
v___x_2154_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2151_, v___y_2142_);
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2157_ = v___x_2154_;
v_isShared_2158_ = v_isSharedCheck_2307_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2307_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
if (lean_obj_tag(v_a_2155_) == 1)
{
lean_object* v_val_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2200_; 
v_val_2159_ = lean_ctor_get(v_a_2155_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v_a_2155_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2161_ = v_a_2155_;
v_isShared_2162_ = v_isSharedCheck_2200_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_val_2159_);
lean_dec(v_a_2155_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2200_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v_dummy_2163_; lean_object* v_nargs_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_args_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; uint8_t v___x_2171_; 
v_dummy_2163_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
v_nargs_2164_ = l_Lean_Expr_getAppNumArgs(v_e_2137_);
lean_inc(v_nargs_2164_);
v___x_2165_ = lean_mk_array(v_nargs_2164_, v_dummy_2163_);
v___x_2166_ = lean_unsigned_to_nat(1u);
v___x_2167_ = lean_nat_sub(v_nargs_2164_, v___x_2166_);
lean_dec(v_nargs_2164_);
v_args_2168_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2137_, v___x_2165_, v___x_2167_);
v___x_2169_ = lean_array_get_size(v_args_2168_);
v___x_2170_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2159_);
v___x_2171_ = lean_nat_dec_lt(v___x_2169_, v___x_2170_);
lean_dec(v___x_2170_);
if (v___x_2171_ == 0)
{
lean_object* v_numParams_2172_; lean_object* v_numDiscrs_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
v_numParams_2172_ = lean_ctor_get(v_val_2159_, 0);
v_numDiscrs_2173_ = lean_ctor_get(v_val_2159_, 1);
v___x_2174_ = lean_array_mk(v_us_2152_);
v___x_2175_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2172_);
v___x_2176_ = l_Array_extract___redArg(v_args_2168_, v___x_2175_, v_numParams_2172_);
v___x_2177_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2159_);
v___x_2178_ = lean_array_get(v___x_2153_, v_args_2168_, v___x_2177_);
lean_dec(v___x_2177_);
v___x_2179_ = lean_nat_add(v_numParams_2172_, v___x_2166_);
v___x_2180_ = lean_nat_add(v___x_2179_, v_numDiscrs_2173_);
lean_inc(v___x_2180_);
lean_inc_ref_n(v_args_2168_, 2);
v___x_2181_ = l_Array_toSubarray___redArg(v_args_2168_, v___x_2179_, v___x_2180_);
v___x_2182_ = l_Subarray_copy___redArg(v___x_2181_);
v___x_2183_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2159_);
v___x_2184_ = lean_nat_add(v___x_2180_, v___x_2183_);
lean_dec(v___x_2183_);
lean_inc(v___x_2184_);
v___x_2185_ = l_Array_toSubarray___redArg(v_args_2168_, v___x_2180_, v___x_2184_);
v___x_2186_ = l_Subarray_copy___redArg(v___x_2185_);
v___x_2187_ = l_Array_toSubarray___redArg(v_args_2168_, v___x_2184_, v___x_2169_);
v___x_2188_ = l_Subarray_copy___redArg(v___x_2187_);
v___x_2189_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2189_, 0, v_val_2159_);
lean_ctor_set(v___x_2189_, 1, v_declName_2151_);
lean_ctor_set(v___x_2189_, 2, v___x_2174_);
lean_ctor_set(v___x_2189_, 3, v___x_2176_);
lean_ctor_set(v___x_2189_, 4, v___x_2178_);
lean_ctor_set(v___x_2189_, 5, v___x_2182_);
lean_ctor_set(v___x_2189_, 6, v___x_2186_);
lean_ctor_set(v___x_2189_, 7, v___x_2188_);
if (v_isShared_2162_ == 0)
{
lean_ctor_set(v___x_2161_, 0, v___x_2189_);
v___x_2191_ = v___x_2161_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2189_);
v___x_2191_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2193_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2191_);
v___x_2193_ = v___x_2157_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v___x_2191_);
v___x_2193_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
return v___x_2193_;
}
}
}
else
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
lean_dec_ref(v_args_2168_);
lean_del_object(v___x_2161_);
lean_dec(v_val_2159_);
lean_dec(v_us_2152_);
lean_dec(v_declName_2151_);
v___x_2196_ = lean_box(0);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 0, v___x_2196_);
v___x_2198_ = v___x_2157_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_object* v___x_2201_; 
lean_del_object(v___x_2157_);
lean_dec(v_a_2155_);
v___x_2201_ = lean_st_ref_get(v___y_2142_);
if (v_alsoCasesOn_2138_ == 0)
{
lean_dec(v___x_2201_);
lean_dec(v_us_2152_);
lean_dec(v_declName_2151_);
lean_dec_ref(v_e_2137_);
goto v___jp_2144_;
}
else
{
lean_object* v_env_2202_; uint8_t v___x_2203_; 
v_env_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc_ref(v_env_2202_);
lean_dec(v___x_2201_);
lean_inc(v_declName_2151_);
v___x_2203_ = l_Lean_isCasesOnRecursor(v_env_2202_, v_declName_2151_);
if (v___x_2203_ == 0)
{
lean_dec(v_us_2152_);
lean_dec(v_declName_2151_);
lean_dec_ref(v_e_2137_);
goto v___jp_2144_;
}
else
{
lean_object* v_indName_2204_; lean_object* v___x_2205_; 
v_indName_2204_ = l_Lean_Name_getPrefix(v_declName_2151_);
v___x_2205_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_2204_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2298_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2208_ = v___x_2205_;
v_isShared_2209_ = v_isSharedCheck_2298_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2298_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
if (lean_obj_tag(v_a_2206_) == 5)
{
lean_object* v_val_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2293_; 
v_val_2210_ = lean_ctor_get(v_a_2206_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v_a_2206_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2212_ = v_a_2206_;
v_isShared_2213_ = v_isSharedCheck_2293_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_val_2210_);
lean_dec(v_a_2206_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2293_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v_toConstantVal_2214_; lean_object* v_numParams_2215_; lean_object* v_numIndices_2216_; lean_object* v_ctors_2217_; lean_object* v_nargs_2218_; lean_object* v_dummy_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v_args_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; 
v_toConstantVal_2214_ = lean_ctor_get(v_val_2210_, 0);
lean_inc_ref(v_toConstantVal_2214_);
v_numParams_2215_ = lean_ctor_get(v_val_2210_, 1);
lean_inc(v_numParams_2215_);
v_numIndices_2216_ = lean_ctor_get(v_val_2210_, 2);
lean_inc(v_numIndices_2216_);
v_ctors_2217_ = lean_ctor_get(v_val_2210_, 4);
lean_inc(v_ctors_2217_);
v_nargs_2218_ = l_Lean_Expr_getAppNumArgs(v_e_2137_);
v_dummy_2219_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
lean_inc(v_nargs_2218_);
v___x_2220_ = lean_mk_array(v_nargs_2218_, v_dummy_2219_);
v___x_2221_ = lean_unsigned_to_nat(1u);
v___x_2222_ = lean_nat_sub(v_nargs_2218_, v___x_2221_);
lean_dec(v_nargs_2218_);
v_args_2223_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2137_, v___x_2220_, v___x_2222_);
v___x_2224_ = lean_nat_add(v_numParams_2215_, v___x_2221_);
v___x_2225_ = lean_nat_add(v___x_2224_, v_numIndices_2216_);
v___x_2226_ = lean_nat_add(v___x_2225_, v___x_2221_);
lean_dec(v___x_2225_);
v___x_2227_ = l_Lean_InductiveVal_numCtors(v_val_2210_);
lean_dec_ref(v_val_2210_);
v___x_2228_ = lean_nat_add(v___x_2226_, v___x_2227_);
lean_dec(v___x_2227_);
v___x_2229_ = lean_array_get_size(v_args_2223_);
v___x_2230_ = lean_nat_dec_le(v___x_2228_, v___x_2229_);
if (v___x_2230_ == 0)
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
lean_dec(v___x_2228_);
lean_dec(v___x_2226_);
lean_dec(v___x_2224_);
lean_dec_ref(v_args_2223_);
lean_dec(v_ctors_2217_);
lean_dec(v_numIndices_2216_);
lean_dec(v_numParams_2215_);
lean_dec_ref(v_toConstantVal_2214_);
lean_del_object(v___x_2212_);
lean_dec(v_us_2152_);
lean_dec(v_declName_2151_);
v___x_2231_ = lean_box(0);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2231_);
v___x_2233_ = v___x_2208_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
else
{
lean_object* v___x_2235_; lean_object* v_params_2236_; lean_object* v_motive_2237_; lean_object* v_discrs_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v_discrInfos_2241_; lean_object* v_alts_2242_; lean_object* v___y_2244_; lean_object* v___y_2245_; lean_object* v_lower_2284_; lean_object* v_upper_2285_; uint8_t v___x_2292_; 
lean_del_object(v___x_2208_);
v___x_2235_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_2215_);
lean_inc_ref_n(v_args_2223_, 3);
v_params_2236_ = l_Array_toSubarray___redArg(v_args_2223_, v___x_2235_, v_numParams_2215_);
v_motive_2237_ = lean_array_get(v___x_2153_, v_args_2223_, v_numParams_2215_);
lean_dec(v_numParams_2215_);
lean_inc(v___x_2226_);
v_discrs_2238_ = l_Array_toSubarray___redArg(v_args_2223_, v___x_2224_, v___x_2226_);
v___x_2239_ = lean_nat_add(v_numIndices_2216_, v___x_2221_);
lean_dec(v_numIndices_2216_);
v___x_2240_ = lean_box(0);
v_discrInfos_2241_ = lean_mk_array(v___x_2239_, v___x_2240_);
lean_inc(v___x_2228_);
v_alts_2242_ = l_Array_toSubarray___redArg(v_args_2223_, v___x_2226_, v___x_2228_);
v___x_2292_ = lean_nat_dec_le(v___x_2228_, v___x_2235_);
if (v___x_2292_ == 0)
{
v_lower_2284_ = v___x_2228_;
v_upper_2285_ = v___x_2229_;
goto v___jp_2283_;
}
else
{
lean_dec(v___x_2228_);
v_lower_2284_ = v___x_2235_;
v_upper_2285_ = v___x_2229_;
goto v___jp_2283_;
}
v___jp_2243_:
{
lean_object* v___x_2246_; size_t v_sz_2247_; size_t v___x_2248_; lean_object* v___x_2249_; 
v___x_2246_ = lean_array_mk(v_ctors_2217_);
v_sz_2247_ = lean_array_size(v___x_2246_);
v___x_2248_ = ((size_t)0ULL);
v___x_2249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_2247_, v___x_2248_, v___x_2246_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2274_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2252_ = v___x_2249_;
v_isShared_2253_ = v_isSharedCheck_2274_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2249_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2274_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v_start_2254_; lean_object* v_stop_2255_; lean_object* v_start_2256_; lean_object* v_stop_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2269_; 
v_start_2254_ = lean_ctor_get(v_params_2236_, 1);
v_stop_2255_ = lean_ctor_get(v_params_2236_, 2);
v_start_2256_ = lean_ctor_get(v_discrs_2238_, 1);
v_stop_2257_ = lean_ctor_get(v_discrs_2238_, 2);
v___x_2258_ = lean_nat_sub(v_stop_2255_, v_start_2254_);
v___x_2259_ = lean_nat_sub(v_stop_2257_, v_start_2256_);
v___x_2260_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2);
v___x_2261_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2258_);
lean_ctor_set(v___x_2261_, 1, v___x_2259_);
lean_ctor_set(v___x_2261_, 2, v_a_2250_);
lean_ctor_set(v___x_2261_, 3, v___y_2245_);
lean_ctor_set(v___x_2261_, 4, v_discrInfos_2241_);
lean_ctor_set(v___x_2261_, 5, v___x_2260_);
v___x_2262_ = lean_array_mk(v_us_2152_);
v___x_2263_ = l_Subarray_copy___redArg(v_params_2236_);
v___x_2264_ = l_Subarray_copy___redArg(v_discrs_2238_);
v___x_2265_ = l_Subarray_copy___redArg(v_alts_2242_);
v___x_2266_ = l_Subarray_copy___redArg(v___y_2244_);
v___x_2267_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2261_);
lean_ctor_set(v___x_2267_, 1, v_declName_2151_);
lean_ctor_set(v___x_2267_, 2, v___x_2262_);
lean_ctor_set(v___x_2267_, 3, v___x_2263_);
lean_ctor_set(v___x_2267_, 4, v_motive_2237_);
lean_ctor_set(v___x_2267_, 5, v___x_2264_);
lean_ctor_set(v___x_2267_, 6, v___x_2265_);
lean_ctor_set(v___x_2267_, 7, v___x_2266_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set_tag(v___x_2212_, 1);
lean_ctor_set(v___x_2212_, 0, v___x_2267_);
v___x_2269_ = v___x_2212_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2267_);
v___x_2269_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v___x_2269_);
v___x_2271_ = v___x_2252_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec_ref(v_alts_2242_);
lean_dec_ref(v_discrInfos_2241_);
lean_dec_ref(v_discrs_2238_);
lean_dec(v_motive_2237_);
lean_dec_ref(v_params_2236_);
lean_del_object(v___x_2212_);
lean_dec(v_us_2152_);
lean_dec(v_declName_2151_);
v_a_2275_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2249_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2249_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
v___jp_2283_:
{
lean_object* v_levelParams_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; 
v_levelParams_2286_ = lean_ctor_get(v_toConstantVal_2214_, 1);
lean_inc(v_levelParams_2286_);
lean_dec_ref(v_toConstantVal_2214_);
v___x_2287_ = l_Array_toSubarray___redArg(v_args_2223_, v_lower_2284_, v_upper_2285_);
v___x_2288_ = l_List_lengthTR___redArg(v_levelParams_2286_);
lean_dec(v_levelParams_2286_);
v___x_2289_ = l_List_lengthTR___redArg(v_us_2152_);
v___x_2290_ = lean_nat_dec_eq(v___x_2288_, v___x_2289_);
lean_dec(v___x_2289_);
lean_dec(v___x_2288_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; 
v___x_2291_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3));
v___y_2244_ = v___x_2287_;
v___y_2245_ = v___x_2291_;
goto v___jp_2243_;
}
else
{
v___y_2244_ = v___x_2287_;
v___y_2245_ = v___x_2240_;
goto v___jp_2243_;
}
}
}
}
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2296_; 
lean_dec(v_a_2206_);
lean_dec(v_us_2152_);
lean_dec(v_declName_2151_);
lean_dec_ref(v_e_2137_);
v___x_2294_ = lean_box(0);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2294_);
v___x_2296_ = v___x_2208_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
lean_dec(v_us_2152_);
lean_dec(v_declName_2151_);
lean_dec_ref(v_e_2137_);
v_a_2299_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2205_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2205_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
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
}
}
}
}
else
{
lean_dec_ref(v___x_2150_);
lean_dec_ref(v_e_2137_);
goto v___jp_2144_;
}
}
v___jp_2144_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2145_ = lean_box(0);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object* v_e_2308_, lean_object* v_alsoCasesOn_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2315_; lean_object* v_res_2316_; 
v_alsoCasesOn_boxed_2315_ = lean_unbox(v_alsoCasesOn_2309_);
v_res_2316_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_2308_, v_alsoCasesOn_boxed_2315_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object* v_e_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2323_; uint8_t v___x_2324_; 
v___x_2323_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2324_ = l_Lean_Expr_isAppOf(v_e_2317_, v___x_2323_);
if (v___x_2324_ == 0)
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2326_ = l_Lean_Expr_isAppOf(v_e_2317_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
v___x_2327_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_2328_ = l_Lean_Expr_isAppOf(v_e_2317_, v___x_2327_);
if (v___x_2328_ == 0)
{
uint8_t v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = 1;
v___x_2330_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_2317_, v___x_2329_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2351_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2351_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2351_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
if (lean_obj_tag(v_a_2331_) == 1)
{
lean_object* v_val_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2346_; 
v_val_2335_ = lean_ctor_get(v_a_2331_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v_a_2331_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2337_ = v_a_2331_;
v_isShared_2338_ = v_isSharedCheck_2346_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_val_2335_);
lean_dec(v_a_2331_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2346_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2339_, 0, v_val_2335_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v___x_2339_);
v___x_2341_ = v___x_2337_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2339_);
v___x_2341_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2343_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2341_);
v___x_2343_ = v___x_2333_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
lean_dec(v_a_2331_);
v___x_2347_ = lean_box(0);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v___x_2347_);
v___x_2349_ = v___x_2333_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
v_a_2352_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2330_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2330_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2360_, 0, v_e_2317_);
v___x_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v___x_2361_);
return v___x_2362_;
}
}
else
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2363_, 0, v_e_2317_);
v___x_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
v___x_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
}
else
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2366_, 0, v_e_2317_);
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
v___x_2368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object* v_e_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object* v_declName_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2376_, v___y_2380_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object* v_declName_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2390_, lean_object* v_constName_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2398_, lean_object* v_constName_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2398_, v_constName_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2406_, lean_object* v_ref_2407_, lean_object* v_constName_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2407_, v_constName_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2415_, lean_object* v_ref_2416_, lean_object* v_constName_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2415_, v_ref_2416_, v_constName_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_ref_2416_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2424_, lean_object* v_ref_2425_, lean_object* v_msg_2426_, lean_object* v_declHint_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2425_, v_msg_2426_, v_declHint_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2434_, lean_object* v_ref_2435_, lean_object* v_msg_2436_, lean_object* v_declHint_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2434_, v_ref_2435_, v_msg_2436_, v_declHint_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v_ref_2435_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_2444_, lean_object* v_declHint_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2444_, v_declHint_2445_, v___y_2449_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_2452_, lean_object* v_declHint_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_2452_, v_declHint_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2460_, lean_object* v_ref_2461_, lean_object* v_msg_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_2461_, v_msg_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2469_, lean_object* v_ref_2470_, lean_object* v_msg_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2469_, v_ref_2470_, v_msg_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v_ref_2470_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_2478_, lean_object* v_msg_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2486_, lean_object* v_msg_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_2486_, v_msg_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
return v_res_2493_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1(void){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0));
v___x_2496_ = l_Lean_stringToMessageData(v___x_2495_);
return v___x_2496_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3(void){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__2));
v___x_2499_ = l_Lean_stringToMessageData(v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object* v_idx_2503_, lean_object* v_e_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
lean_object* v___y_2511_; lean_object* v___y_2530_; lean_object* v___y_2531_; uint8_t v___y_2562_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2583_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2584_ = l_Lean_Expr_isAppOf(v_e_2504_, v___x_2583_);
if (v___x_2584_ == 0)
{
lean_object* v___x_2585_; uint8_t v___x_2586_; 
v___x_2585_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2586_ = l_Lean_Expr_isAppOf(v_e_2504_, v___x_2585_);
v___y_2562_ = v___x_2586_;
goto v___jp_2561_;
}
else
{
v___y_2562_ = v___x_2584_;
goto v___jp_2561_;
}
v___jp_2510_:
{
lean_object* v___x_2512_; 
lean_inc_ref(v___y_2511_);
v___x_2512_ = l_Lean_Meta_findLocalDeclWithType_x3f(v___y_2511_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
if (lean_obj_tag(v_a_2513_) == 1)
{
lean_object* v_val_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_dec_ref(v___y_2511_);
v_val_2514_ = lean_ctor_get(v_a_2513_, 0);
lean_inc(v_val_2514_);
lean_dec_ref_known(v_a_2513_, 1);
v___x_2515_ = l_Lean_mkFVar(v_val_2514_);
v___x_2516_ = l_Lean_Meta_rwIfWith(v___x_2515_, v_e_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2516_;
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_dec(v_a_2513_);
lean_dec_ref(v_e_2504_);
v___x_2517_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1);
v___x_2518_ = l_Lean_MessageData_ofExpr(v___y_2511_);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2519_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2520_;
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v___y_2511_);
lean_dec_ref(v_e_2504_);
v_a_2521_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2512_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2512_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
v___jp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = lean_box(0);
lean_inc(v___y_2531_);
v___x_2533_ = l_Lean_mkConst(v___y_2531_, v___x_2532_);
v___x_2534_ = l_Lean_Meta_mkEq(v___y_2530_, v___x_2533_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2536_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
lean_inc_n(v_a_2535_, 2);
lean_dec_ref_known(v___x_2534_, 1);
v___x_2536_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_a_2535_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___x_2536_, 1);
if (lean_obj_tag(v_a_2537_) == 1)
{
lean_object* v_val_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
lean_dec(v_a_2535_);
v_val_2538_ = lean_ctor_get(v_a_2537_, 0);
lean_inc(v_val_2538_);
lean_dec_ref_known(v_a_2537_, 1);
v___x_2539_ = l_Lean_mkFVar(v_val_2538_);
v___x_2540_ = l_Lean_Meta_rwIfWith(v___x_2539_, v_e_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2540_;
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_dec(v_a_2537_);
lean_dec_ref(v_e_2504_);
v___x_2541_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__3);
v___x_2542_ = l_Lean_MessageData_ofExpr(v_a_2535_);
v___x_2543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2541_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2543_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2544_;
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_a_2535_);
lean_dec_ref(v_e_2504_);
v_a_2545_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2536_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2536_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec_ref(v_e_2504_);
v_a_2553_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2534_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2534_);
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
v___jp_2561_:
{
if (v___y_2562_ == 0)
{
lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_2564_ = l_Lean_Expr_isAppOf(v_e_2504_, v___x_2563_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Meta_rwMatcher(v_idx_2503_, v_e_2504_, v_a_2505_, v_a_2506_, v_a_2507_, v_a_2508_);
return v___x_2565_;
}
else
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v_c_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2566_ = lean_unsigned_to_nat(1u);
v___x_2567_ = l_Lean_Expr_getAppNumArgs(v_e_2504_);
v___x_2568_ = lean_nat_sub(v___x_2567_, v___x_2566_);
lean_dec(v___x_2567_);
v___x_2569_ = lean_nat_sub(v___x_2568_, v___x_2566_);
lean_dec(v___x_2568_);
v_c_2570_ = l_Lean_Expr_getRevArg_x21(v_e_2504_, v___x_2569_);
v___x_2571_ = lean_unsigned_to_nat(0u);
v___x_2572_ = lean_nat_dec_eq(v_idx_2503_, v___x_2571_);
lean_dec(v_idx_2503_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__4));
v___y_2530_ = v_c_2570_;
v___y_2531_ = v___x_2573_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2574_; 
v___x_2574_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__19___closed__1));
v___y_2530_ = v_c_2570_;
v___y_2531_ = v___x_2574_;
goto v___jp_2529_;
}
}
}
else
{
lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v_c_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2575_ = lean_unsigned_to_nat(1u);
v___x_2576_ = l_Lean_Expr_getAppNumArgs(v_e_2504_);
v___x_2577_ = lean_nat_sub(v___x_2576_, v___x_2575_);
lean_dec(v___x_2576_);
v___x_2578_ = lean_nat_sub(v___x_2577_, v___x_2575_);
lean_dec(v___x_2577_);
v_c_2579_ = l_Lean_Expr_getRevArg_x21(v_e_2504_, v___x_2578_);
v___x_2580_ = lean_unsigned_to_nat(0u);
v___x_2581_ = lean_nat_dec_eq(v_idx_2503_, v___x_2580_);
lean_dec(v_idx_2503_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
v___x_2582_ = l_Lean_mkNot(v_c_2579_);
v___y_2511_ = v___x_2582_;
goto v___jp_2510_;
}
else
{
v___y_2511_ = v_c_2579_;
goto v___jp_2510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object* v_idx_2587_, lean_object* v_e_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(v_idx_2587_, v_e_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
return v_res_2594_;
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
