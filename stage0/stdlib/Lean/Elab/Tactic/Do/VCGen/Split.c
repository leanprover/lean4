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
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclsDND___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_inferArgumentTypesN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_altNumParams(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_MatcherApp_toExpr(lean_object*);
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
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_withLocalDeclsD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_rwIfWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_rwMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "alt"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 128, 245, 49, 225, 62, 36, 86)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "discr"};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__0_value),LEAN_SCALAR_PTR_LITERAL(193, 61, 20, 168, 108, 94, 13, 165)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_etaExpand___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__4_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__5_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__1_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__7_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__3_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__4_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__8_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__6_value)}};
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object**);
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
static const lean_closure_object l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10_value;
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
static const lean_ctor_object l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value),((lean_object*)&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0_value)}};
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorIdx(v_x_5_);
lean_dec_ref(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
lean_object* v_e_9_; lean_object* v___x_10_; 
v_e_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc_ref(v_e_9_);
lean_dec_ref(v_t_7_);
v___x_10_ = lean_apply_1(v_k_8_, v_e_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim___redArg(lean_object* v_t_23_, lean_object* v_ite_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_23_, v_ite_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_ite_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_ite_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_27_, v_ite_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim___redArg(lean_object* v_t_31_, lean_object* v_dite_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_31_, v_dite_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_dite_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_dite_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_35_, v_dite_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim___redArg(lean_object* v_t_39_, lean_object* v_matcher_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_39_, v_matcher_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_matcher_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_matcher_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_Elab_Tactic_Do_SplitInfo_ctorElim___redArg(v_t_43_, v_matcher_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_box(0);
v___x_51_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__1));
v___x_52_ = l_Lean_Expr_const___override(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2, &l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2_once, _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__2);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default(void){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3, &l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3_once, _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default___closed__3);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Elab_Tactic_Do_instInhabitedSplitInfo_default;
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_zero_59_; uint8_t v_isZero_60_; 
v_zero_59_ = lean_unsigned_to_nat(0u);
v_isZero_60_ = lean_nat_dec_eq(v_x_57_, v_zero_59_);
if (v_isZero_60_ == 1)
{
lean_dec(v_x_57_);
return v_x_58_;
}
else
{
lean_object* v_one_61_; lean_object* v_n_62_; 
v_one_61_ = lean_unsigned_to_nat(1u);
v_n_62_ = lean_nat_sub(v_x_57_, v_one_61_);
lean_dec(v_x_57_);
if (lean_obj_tag(v_x_58_) == 1)
{
lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_74_; 
v_val_63_ = lean_ctor_get(v_x_58_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_74_ == 0)
{
v___x_65_ = v_x_58_;
v_isShared_66_ = v_isSharedCheck_74_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_dec(v_x_58_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_74_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
if (lean_obj_tag(v_val_63_) == 6)
{
lean_object* v_body_67_; lean_object* v___x_69_; 
v_body_67_ = lean_ctor_get(v_val_63_, 2);
lean_inc_ref(v_body_67_);
lean_dec_ref_known(v_val_63_, 3);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v_body_67_);
v___x_69_ = v___x_65_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_body_67_);
v___x_69_ = v_reuseFailAlloc_71_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
v_x_57_ = v_n_62_;
v_x_58_ = v___x_69_;
goto _start;
}
}
else
{
lean_object* v___x_72_; 
lean_del_object(v___x_65_);
lean_dec(v_val_63_);
v___x_72_ = lean_box(0);
v_x_57_ = v_n_62_;
v_x_58_ = v___x_72_;
goto _start;
}
}
}
else
{
lean_object* v___x_75_; 
lean_dec(v_x_58_);
v___x_75_ = lean_box(0);
v_x_57_ = v_n_62_;
v_x_58_ = v___x_75_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_resTy(lean_object* v_info_77_){
_start:
{
lean_object* v_e_79_; 
if (lean_obj_tag(v_info_77_) == 2)
{
lean_object* v_matcherApp_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_102_; 
v_matcherApp_85_ = lean_ctor_get(v_info_77_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v_info_77_);
if (v_isSharedCheck_102_ == 0)
{
v___x_87_ = v_info_77_;
v_isShared_88_ = v_isSharedCheck_102_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_matcherApp_85_);
lean_dec(v_info_77_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_102_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v_toMatcherInfo_89_; lean_object* v_motive_90_; lean_object* v_discrInfos_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v_toMatcherInfo_89_ = lean_ctor_get(v_matcherApp_85_, 0);
lean_inc_ref(v_toMatcherInfo_89_);
v_motive_90_ = lean_ctor_get(v_matcherApp_85_, 4);
lean_inc_ref_n(v_motive_90_, 2);
lean_dec_ref(v_matcherApp_85_);
v_discrInfos_91_ = lean_ctor_get(v_toMatcherInfo_89_, 4);
lean_inc_ref(v_discrInfos_91_);
lean_dec_ref(v_toMatcherInfo_89_);
v___x_92_ = lean_array_get_size(v_discrInfos_91_);
lean_dec_ref(v_discrInfos_91_);
if (v_isShared_88_ == 0)
{
lean_ctor_set_tag(v___x_87_, 1);
lean_ctor_set(v___x_87_, 0, v_motive_90_);
v___x_94_ = v___x_87_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_motive_90_);
v___x_94_ = v_reuseFailAlloc_101_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; 
v___x_95_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lean_Elab_Tactic_Do_SplitInfo_resTy_spec__0(v___x_92_, v___x_94_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_dec_ref(v_motive_90_);
return v___x_95_;
}
else
{
lean_object* v_val_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v_val_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_val_96_);
v___x_97_ = l_Lean_Expr_looseBVarRange(v_val_96_);
lean_dec(v_val_96_);
v___x_98_ = l_Lean_Expr_looseBVarRange(v_motive_90_);
lean_dec_ref(v_motive_90_);
v___x_99_ = lean_nat_dec_eq(v___x_97_, v___x_98_);
lean_dec(v___x_98_);
lean_dec(v___x_97_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; 
lean_dec_ref_known(v___x_95_, 1);
v___x_100_ = lean_box(0);
return v___x_100_;
}
else
{
return v___x_95_;
}
}
}
}
}
else
{
lean_object* v_e_103_; 
v_e_103_ = lean_ctor_get(v_info_77_, 0);
lean_inc_ref(v_e_103_);
lean_dec_ref(v_info_77_);
v_e_79_ = v_e_103_;
goto v___jp_78_;
}
v___jp_78_:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_80_ = l_Lean_Expr_getAppNumArgs(v_e_79_);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_sub(v___x_80_, v___x_81_);
lean_dec(v___x_80_);
v___x_83_ = l_Lean_Expr_getRevArg_x21(v_e_79_, v___x_82_);
lean_dec_ref(v_e_79_);
v___x_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(lean_object* v_matcherApp_104_, size_t v_sz_105_, size_t v_i_106_, lean_object* v_bs_107_){
_start:
{
uint8_t v___x_108_; 
v___x_108_ = lean_usize_dec_lt(v_i_106_, v_sz_105_);
if (v___x_108_ == 0)
{
return v_bs_107_;
}
else
{
lean_object* v_v_109_; lean_object* v_alts_110_; lean_object* v___x_111_; lean_object* v_bs_x27_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; size_t v___x_117_; size_t v___x_118_; lean_object* v___x_119_; 
v_v_109_ = lean_array_uget(v_bs_107_, v_i_106_);
v_alts_110_ = lean_ctor_get(v_matcherApp_104_, 6);
v___x_111_ = lean_unsigned_to_nat(0u);
v_bs_x27_112_ = lean_array_uset(v_bs_107_, v_i_106_, v___x_111_);
v___x_113_ = l_Lean_instInhabitedExpr;
v___x_114_ = lean_usize_to_nat(v_i_106_);
v___x_115_ = lean_array_get_borrowed(v___x_113_, v_alts_110_, v___x_114_);
lean_dec(v___x_114_);
lean_inc(v___x_115_);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v_v_109_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = ((size_t)1ULL);
v___x_118_ = lean_usize_add(v_i_106_, v___x_117_);
v___x_119_ = lean_array_uset(v_bs_x27_112_, v_i_106_, v___x_116_);
v_i_106_ = v___x_118_;
v_bs_107_ = v___x_119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg___boxed(lean_object* v_matcherApp_121_, lean_object* v_sz_122_, lean_object* v_i_123_, lean_object* v_bs_124_){
_start:
{
size_t v_sz_boxed_125_; size_t v_i_boxed_126_; lean_object* v_res_127_; 
v_sz_boxed_125_ = lean_unbox_usize(v_sz_122_);
lean_dec(v_sz_122_);
v_i_boxed_126_ = lean_unbox_usize(v_i_123_);
lean_dec(v_i_123_);
v_res_127_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_121_, v_sz_boxed_125_, v_i_boxed_126_, v_bs_124_);
lean_dec_ref(v_matcherApp_121_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_altInfos(lean_object* v_info_128_){
_start:
{
switch(lean_obj_tag(v_info_128_))
{
case 0:
{
lean_object* v_e_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v_e_129_ = lean_ctor_get(v_info_128_, 0);
lean_inc_ref(v_e_129_);
lean_dec_ref_known(v_info_128_, 1);
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_unsigned_to_nat(3u);
v___x_132_ = l_Lean_Expr_getAppNumArgs(v_e_129_);
v___x_133_ = lean_nat_sub(v___x_132_, v___x_131_);
v___x_134_ = lean_unsigned_to_nat(1u);
v___x_135_ = lean_nat_sub(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
v___x_136_ = l_Lean_Expr_getRevArg_x21(v_e_129_, v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_130_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_unsigned_to_nat(4u);
v___x_139_ = lean_nat_sub(v___x_132_, v___x_138_);
lean_dec(v___x_132_);
v___x_140_ = lean_nat_sub(v___x_139_, v___x_134_);
lean_dec(v___x_139_);
v___x_141_ = l_Lean_Expr_getRevArg_x21(v_e_129_, v___x_140_);
lean_dec_ref(v_e_129_);
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_130_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_unsigned_to_nat(2u);
v___x_144_ = lean_mk_empty_array_with_capacity(v___x_143_);
v___x_145_ = lean_array_push(v___x_144_, v___x_137_);
v___x_146_ = lean_array_push(v___x_145_, v___x_142_);
return v___x_146_;
}
case 1:
{
lean_object* v_e_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_e_147_ = lean_ctor_get(v_info_128_, 0);
lean_inc_ref(v_e_147_);
lean_dec_ref_known(v_info_128_, 1);
v___x_148_ = lean_unsigned_to_nat(1u);
v___x_149_ = lean_unsigned_to_nat(3u);
v___x_150_ = l_Lean_Expr_getAppNumArgs(v_e_147_);
v___x_151_ = lean_nat_sub(v___x_150_, v___x_149_);
v___x_152_ = lean_nat_sub(v___x_151_, v___x_148_);
lean_dec(v___x_151_);
v___x_153_ = l_Lean_Expr_getRevArg_x21(v_e_147_, v___x_152_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_148_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(4u);
v___x_156_ = lean_nat_sub(v___x_150_, v___x_155_);
lean_dec(v___x_150_);
v___x_157_ = lean_nat_sub(v___x_156_, v___x_148_);
lean_dec(v___x_156_);
v___x_158_ = l_Lean_Expr_getRevArg_x21(v_e_147_, v___x_157_);
lean_dec_ref(v_e_147_);
v___x_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_148_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_unsigned_to_nat(2u);
v___x_161_ = lean_mk_empty_array_with_capacity(v___x_160_);
v___x_162_ = lean_array_push(v___x_161_, v___x_154_);
v___x_163_ = lean_array_push(v___x_162_, v___x_159_);
return v___x_163_;
}
default: 
{
lean_object* v_matcherApp_164_; lean_object* v___x_165_; size_t v_sz_166_; size_t v___x_167_; lean_object* v___x_168_; 
v_matcherApp_164_ = lean_ctor_get(v_info_128_, 0);
lean_inc_ref_n(v_matcherApp_164_, 2);
lean_dec_ref_known(v_info_128_, 1);
v___x_165_ = l_Lean_Meta_MatcherApp_altNumParams(v_matcherApp_164_);
v_sz_166_ = lean_array_size(v___x_165_);
v___x_167_ = ((size_t)0ULL);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_164_, v_sz_166_, v___x_167_, v___x_165_);
lean_dec_ref(v_matcherApp_164_);
return v___x_168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(lean_object* v_matcherApp_169_, lean_object* v_as_170_, size_t v_sz_171_, size_t v_i_172_, lean_object* v_bs_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___redArg(v_matcherApp_169_, v_sz_171_, v_i_172_, v_bs_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0___boxed(lean_object* v_matcherApp_175_, lean_object* v_as_176_, lean_object* v_sz_177_, lean_object* v_i_178_, lean_object* v_bs_179_){
_start:
{
size_t v_sz_boxed_180_; size_t v_i_boxed_181_; lean_object* v_res_182_; 
v_sz_boxed_180_ = lean_unbox_usize(v_sz_177_);
lean_dec(v_sz_177_);
v_i_boxed_181_ = lean_unbox_usize(v_i_178_);
lean_dec(v_i_178_);
v_res_182_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_Tactic_Do_SplitInfo_altInfos_spec__0(v_matcherApp_175_, v_as_176_, v_sz_boxed_180_, v_i_boxed_181_, v_bs_179_);
lean_dec_ref(v_as_176_);
lean_dec_ref(v_matcherApp_175_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_expr(lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_183_) == 2)
{
lean_object* v_matcherApp_184_; lean_object* v___x_185_; 
v_matcherApp_184_ = lean_ctor_get(v_x_183_, 0);
lean_inc_ref(v_matcherApp_184_);
lean_dec_ref_known(v_x_183_, 1);
v___x_185_ = l_Lean_Meta_MatcherApp_toExpr(v_matcherApp_184_);
return v___x_185_;
}
else
{
lean_object* v_e_186_; 
v_e_186_ = lean_ctor_get(v_x_183_, 0);
lean_inc_ref(v_e_186_);
lean_dec_ref(v_x_183_);
return v_e_186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0(lean_object* v___x_190_, lean_object* v_resTy_191_, lean_object* v_c_192_, lean_object* v_dec_193_, lean_object* v_t_194_, lean_object* v_e_195_, lean_object* v_k_196_, lean_object* v_u_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_198_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_199_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_199_, 0, v_u_197_);
lean_ctor_set(v___x_199_, 1, v___x_190_);
v___x_200_ = l_Lean_mkConst(v___x_198_, v___x_199_);
lean_inc_ref(v_e_195_);
lean_inc_ref(v_t_194_);
lean_inc_ref(v_dec_193_);
lean_inc_ref(v_c_192_);
v___x_201_ = l_Lean_mkApp5(v___x_200_, v_resTy_191_, v_c_192_, v_dec_193_, v_t_194_, v_e_195_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
v___x_203_ = lean_unsigned_to_nat(4u);
v___x_204_ = lean_mk_empty_array_with_capacity(v___x_203_);
v___x_205_ = lean_array_push(v___x_204_, v_c_192_);
v___x_206_ = lean_array_push(v___x_205_, v_dec_193_);
v___x_207_ = lean_array_push(v___x_206_, v_t_194_);
v___x_208_ = lean_array_push(v___x_207_, v_e_195_);
v___x_209_ = lean_apply_2(v_k_196_, v___x_202_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1(lean_object* v___x_210_, lean_object* v_resTy_211_, lean_object* v_c_212_, lean_object* v_dec_213_, lean_object* v_t_214_, lean_object* v_k_215_, lean_object* v_inst_216_, lean_object* v_toBind_217_, lean_object* v_e_218_){
_start:
{
lean_object* v___f_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
lean_inc_ref(v_resTy_211_);
v___f_219_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0), 8, 7);
lean_closure_set(v___f_219_, 0, v___x_210_);
lean_closure_set(v___f_219_, 1, v_resTy_211_);
lean_closure_set(v___f_219_, 2, v_c_212_);
lean_closure_set(v___f_219_, 3, v_dec_213_);
lean_closure_set(v___f_219_, 4, v_t_214_);
lean_closure_set(v___f_219_, 5, v_e_218_);
lean_closure_set(v___f_219_, 6, v_k_215_);
v___x_220_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_220_, 0, v_resTy_211_);
v___x_221_ = lean_apply_2(v_inst_216_, lean_box(0), v___x_220_);
v___x_222_ = lean_apply_4(v_toBind_217_, lean_box(0), lean_box(0), v___x_221_, v___f_219_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2(lean_object* v___x_226_, lean_object* v_resTy_227_, lean_object* v_c_228_, lean_object* v_dec_229_, lean_object* v_k_230_, lean_object* v_inst_231_, lean_object* v_toBind_232_, lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_t_235_){
_start:
{
lean_object* v___f_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
lean_inc_ref(v_resTy_227_);
v___f_236_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__1), 9, 8);
lean_closure_set(v___f_236_, 0, v___x_226_);
lean_closure_set(v___f_236_, 1, v_resTy_227_);
lean_closure_set(v___f_236_, 2, v_c_228_);
lean_closure_set(v___f_236_, 3, v_dec_229_);
lean_closure_set(v___f_236_, 4, v_t_235_);
lean_closure_set(v___f_236_, 5, v_k_230_);
lean_closure_set(v___f_236_, 6, v_inst_231_);
lean_closure_set(v___f_236_, 7, v_toBind_232_);
v___x_237_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_238_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_233_, v_inst_234_, v___x_237_, v_resTy_227_, v___f_236_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3(lean_object* v___x_242_, lean_object* v_resTy_243_, lean_object* v_c_244_, lean_object* v_k_245_, lean_object* v_inst_246_, lean_object* v_toBind_247_, lean_object* v_inst_248_, lean_object* v_inst_249_, lean_object* v_dec_250_){
_start:
{
lean_object* v___f_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
lean_inc_ref(v_inst_249_);
lean_inc_ref(v_inst_248_);
lean_inc_ref(v_resTy_243_);
v___f_251_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2), 10, 9);
lean_closure_set(v___f_251_, 0, v___x_242_);
lean_closure_set(v___f_251_, 1, v_resTy_243_);
lean_closure_set(v___f_251_, 2, v_c_244_);
lean_closure_set(v___f_251_, 3, v_dec_250_);
lean_closure_set(v___f_251_, 4, v_k_245_);
lean_closure_set(v___f_251_, 5, v_inst_246_);
lean_closure_set(v___f_251_, 6, v_toBind_247_);
lean_closure_set(v___f_251_, 7, v_inst_248_);
lean_closure_set(v___f_251_, 8, v_inst_249_);
v___x_252_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_253_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_248_, v_inst_249_, v___x_252_, v_resTy_243_, v___f_251_);
return v___x_253_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_260_ = lean_box(0);
v___x_261_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__3));
v___x_262_ = l_Lean_mkConst(v___x_261_, v___x_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4(lean_object* v_resTy_263_, lean_object* v_k_264_, lean_object* v_inst_265_, lean_object* v_toBind_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_c_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___f_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_270_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_271_ = lean_box(0);
lean_inc_ref(v_inst_268_);
lean_inc_ref(v_inst_267_);
lean_inc_ref(v_c_269_);
v___f_272_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3), 9, 8);
lean_closure_set(v___f_272_, 0, v___x_271_);
lean_closure_set(v___f_272_, 1, v_resTy_263_);
lean_closure_set(v___f_272_, 2, v_c_269_);
lean_closure_set(v___f_272_, 3, v_k_264_);
lean_closure_set(v___f_272_, 4, v_inst_265_);
lean_closure_set(v___f_272_, 5, v_toBind_266_);
lean_closure_set(v___f_272_, 6, v_inst_267_);
lean_closure_set(v___f_272_, 7, v_inst_268_);
v___x_273_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_274_ = l_Lean_Expr_app___override(v___x_273_, v_c_269_);
v___x_275_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_267_, v_inst_268_, v___x_270_, v___x_274_, v___f_272_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(lean_object* v_c_276_, lean_object* v_resTy_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_mkArrow(v_c_276_, v_resTy_277_, v___y_280_, v___y_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed(lean_object* v_c_284_, lean_object* v_resTy_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5(v_c_284_, v_resTy_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6(lean_object* v___x_295_, lean_object* v_resTy_296_, lean_object* v_c_297_, lean_object* v_dec_298_, lean_object* v_t_299_, lean_object* v_e_300_, lean_object* v_k_301_, lean_object* v_u_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_303_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_304_, 0, v_u_302_);
lean_ctor_set(v___x_304_, 1, v___x_295_);
v___x_305_ = l_Lean_mkConst(v___x_303_, v___x_304_);
lean_inc_ref(v_e_300_);
lean_inc_ref(v_t_299_);
lean_inc_ref(v_dec_298_);
lean_inc_ref(v_c_297_);
v___x_306_ = l_Lean_mkApp5(v___x_305_, v_resTy_296_, v_c_297_, v_dec_298_, v_t_299_, v_e_300_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(4u);
v___x_309_ = lean_mk_empty_array_with_capacity(v___x_308_);
v___x_310_ = lean_array_push(v___x_309_, v_c_297_);
v___x_311_ = lean_array_push(v___x_310_, v_dec_298_);
v___x_312_ = lean_array_push(v___x_311_, v_t_299_);
v___x_313_ = lean_array_push(v___x_312_, v_e_300_);
v___x_314_ = lean_apply_2(v_k_301_, v___x_307_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7(lean_object* v___x_315_, lean_object* v_resTy_316_, lean_object* v_c_317_, lean_object* v_dec_318_, lean_object* v_t_319_, lean_object* v_k_320_, lean_object* v_inst_321_, lean_object* v_toBind_322_, lean_object* v_e_323_){
_start:
{
lean_object* v___f_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_inc_ref(v_resTy_316_);
v___f_324_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6), 8, 7);
lean_closure_set(v___f_324_, 0, v___x_315_);
lean_closure_set(v___f_324_, 1, v_resTy_316_);
lean_closure_set(v___f_324_, 2, v_c_317_);
lean_closure_set(v___f_324_, 3, v_dec_318_);
lean_closure_set(v___f_324_, 4, v_t_319_);
lean_closure_set(v___f_324_, 5, v_e_323_);
lean_closure_set(v___f_324_, 6, v_k_320_);
v___x_325_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_325_, 0, v_resTy_316_);
v___x_326_ = lean_apply_2(v_inst_321_, lean_box(0), v___x_325_);
v___x_327_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v___x_326_, v___f_324_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8(lean_object* v___x_328_, lean_object* v_resTy_329_, lean_object* v_c_330_, lean_object* v_dec_331_, lean_object* v_k_332_, lean_object* v_inst_333_, lean_object* v_toBind_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_eTy_337_, lean_object* v_t_338_){
_start:
{
lean_object* v___f_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___f_339_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__7), 9, 8);
lean_closure_set(v___f_339_, 0, v___x_328_);
lean_closure_set(v___f_339_, 1, v_resTy_329_);
lean_closure_set(v___f_339_, 2, v_c_330_);
lean_closure_set(v___f_339_, 3, v_dec_331_);
lean_closure_set(v___f_339_, 4, v_t_338_);
lean_closure_set(v___f_339_, 5, v_k_332_);
lean_closure_set(v___f_339_, 6, v_inst_333_);
lean_closure_set(v___f_339_, 7, v_toBind_334_);
v___x_340_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__2___closed__1));
v___x_341_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_335_, v_inst_336_, v___x_340_, v_eTy_337_, v___f_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9(lean_object* v___x_342_, lean_object* v_resTy_343_, lean_object* v_c_344_, lean_object* v_dec_345_, lean_object* v_k_346_, lean_object* v_inst_347_, lean_object* v_toBind_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_tTy_351_, lean_object* v_eTy_352_){
_start:
{
lean_object* v___f_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_inc_ref(v_inst_350_);
lean_inc_ref(v_inst_349_);
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__8), 11, 10);
lean_closure_set(v___f_353_, 0, v___x_342_);
lean_closure_set(v___f_353_, 1, v_resTy_343_);
lean_closure_set(v___f_353_, 2, v_c_344_);
lean_closure_set(v___f_353_, 3, v_dec_345_);
lean_closure_set(v___f_353_, 4, v_k_346_);
lean_closure_set(v___f_353_, 5, v_inst_347_);
lean_closure_set(v___f_353_, 6, v_toBind_348_);
lean_closure_set(v___f_353_, 7, v_inst_349_);
lean_closure_set(v___f_353_, 8, v_inst_350_);
lean_closure_set(v___f_353_, 9, v_eTy_352_);
v___x_354_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__3___closed__1));
v___x_355_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_349_, v_inst_350_, v___x_354_, v_tTy_351_, v___f_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(lean_object* v___x_356_, lean_object* v_resTy_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_mkArrow(v___x_356_, v_resTy_357_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed(lean_object* v___x_364_, lean_object* v_resTy_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10(v___x_364_, v_resTy_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11(lean_object* v___x_372_, lean_object* v_resTy_373_, lean_object* v_c_374_, lean_object* v_dec_375_, lean_object* v_k_376_, lean_object* v_inst_377_, lean_object* v_toBind_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_tTy_381_){
_start:
{
lean_object* v___f_382_; lean_object* v___x_383_; lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_inc(v_toBind_378_);
lean_inc(v_inst_377_);
lean_inc_ref(v_c_374_);
lean_inc_ref(v_resTy_373_);
v___f_382_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__9), 11, 10);
lean_closure_set(v___f_382_, 0, v___x_372_);
lean_closure_set(v___f_382_, 1, v_resTy_373_);
lean_closure_set(v___f_382_, 2, v_c_374_);
lean_closure_set(v___f_382_, 3, v_dec_375_);
lean_closure_set(v___f_382_, 4, v_k_376_);
lean_closure_set(v___f_382_, 5, v_inst_377_);
lean_closure_set(v___f_382_, 6, v_toBind_378_);
lean_closure_set(v___f_382_, 7, v_inst_379_);
lean_closure_set(v___f_382_, 8, v_inst_380_);
lean_closure_set(v___f_382_, 9, v_tTy_381_);
v___x_383_ = l_Lean_mkNot(v_c_374_);
v___f_384_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__10___boxed), 7, 2);
lean_closure_set(v___f_384_, 0, v___x_383_);
lean_closure_set(v___f_384_, 1, v_resTy_373_);
v___x_385_ = lean_apply_2(v_inst_377_, lean_box(0), v___f_384_);
v___x_386_ = lean_apply_4(v_toBind_378_, lean_box(0), lean_box(0), v___x_385_, v___f_382_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12(lean_object* v___x_387_, lean_object* v_resTy_388_, lean_object* v_c_389_, lean_object* v_k_390_, lean_object* v_inst_391_, lean_object* v_toBind_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v___f_395_, lean_object* v_dec_396_){
_start:
{
lean_object* v___f_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_inc(v_toBind_392_);
lean_inc(v_inst_391_);
v___f_397_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__11), 10, 9);
lean_closure_set(v___f_397_, 0, v___x_387_);
lean_closure_set(v___f_397_, 1, v_resTy_388_);
lean_closure_set(v___f_397_, 2, v_c_389_);
lean_closure_set(v___f_397_, 3, v_dec_396_);
lean_closure_set(v___f_397_, 4, v_k_390_);
lean_closure_set(v___f_397_, 5, v_inst_391_);
lean_closure_set(v___f_397_, 6, v_toBind_392_);
lean_closure_set(v___f_397_, 7, v_inst_393_);
lean_closure_set(v___f_397_, 8, v_inst_394_);
v___x_398_ = lean_apply_2(v_inst_391_, lean_box(0), v___f_395_);
v___x_399_ = lean_apply_4(v_toBind_392_, lean_box(0), lean_box(0), v___x_398_, v___f_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13(lean_object* v_resTy_400_, lean_object* v_k_401_, lean_object* v_inst_402_, lean_object* v_toBind_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_c_406_){
_start:
{
lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
lean_inc_ref(v_resTy_400_);
lean_inc_ref_n(v_c_406_, 2);
v___f_407_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__5___boxed), 7, 2);
lean_closure_set(v___f_407_, 0, v_c_406_);
lean_closure_set(v___f_407_, 1, v_resTy_400_);
v___x_408_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__1));
v___x_409_ = lean_box(0);
lean_inc_ref(v_inst_405_);
lean_inc_ref(v_inst_404_);
v___f_410_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__12), 10, 9);
lean_closure_set(v___f_410_, 0, v___x_409_);
lean_closure_set(v___f_410_, 1, v_resTy_400_);
lean_closure_set(v___f_410_, 2, v_c_406_);
lean_closure_set(v___f_410_, 3, v_k_401_);
lean_closure_set(v___f_410_, 4, v_inst_402_);
lean_closure_set(v___f_410_, 5, v_toBind_403_);
lean_closure_set(v___f_410_, 6, v_inst_404_);
lean_closure_set(v___f_410_, 7, v_inst_405_);
lean_closure_set(v___f_410_, 8, v___f_407_);
v___x_411_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4___closed__4);
v___x_412_ = l_Lean_Expr_app___override(v___x_411_, v_c_406_);
v___x_413_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_404_, v_inst_405_, v___x_408_, v___x_412_, v___f_410_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(lean_object* v_i_417_, lean_object* v_a_418_, lean_object* v_x_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_420_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___closed__1));
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = lean_nat_add(v_i_417_, v___x_421_);
v___x_423_ = lean_name_append_index_after(v___x_420_, v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
lean_ctor_set(v___x_424_, 1, v_a_418_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14___boxed(lean_object* v_i_425_, lean_object* v_a_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__14(v_i_425_, v_a_426_, v_x_427_);
lean_dec(v_i_425_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(lean_object* v_resTy_429_, lean_object* v_motiveArgs_430_, lean_object* v_x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
uint8_t v___x_437_; uint8_t v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; 
v___x_437_ = 0;
v___x_438_ = 1;
v___x_439_ = 1;
v___x_440_ = l_Lean_Meta_mkLambdaFVars(v_motiveArgs_430_, v_resTy_429_, v___x_437_, v___x_438_, v___x_437_, v___x_438_, v___x_439_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed(lean_object* v_resTy_441_, lean_object* v_motiveArgs_442_, lean_object* v_x_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15(v_resTy_441_, v_motiveArgs_442_, v_x_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec_ref(v_x_443_);
lean_dec_ref(v_motiveArgs_442_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(lean_object* v_i_450_, lean_object* v___x_451_, lean_object* v_discrs_452_, lean_object* v_prior_453_, lean_object* v_next_454_, lean_object* v_acc_455_, lean_object* v_h_456_, lean_object* v_G_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_a_464_; uint8_t v___x_468_; 
v___x_468_ = lean_nat_dec_lt(v_next_454_, v_i_450_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
lean_dec_ref(v_G_457_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v_acc_455_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_470_ = lean_array_get_borrowed(v___x_451_, v_discrs_452_, v_next_454_);
v___x_471_ = l_Lean_Expr_isFVar(v___x_470_);
if (v___x_471_ == 0)
{
v_a_464_ = v_acc_455_;
goto v___jp_463_;
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = lean_array_get_borrowed(v___x_451_, v_prior_453_, v_next_454_);
lean_inc(v___x_470_);
v___x_473_ = l_Lean_Expr_replaceFVar(v_acc_455_, v___x_470_, v___x_472_);
lean_dec_ref(v_acc_455_);
v_a_464_ = v___x_473_;
goto v___jp_463_;
}
}
v___jp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_add(v_next_454_, v___x_465_);
lean_inc(v___y_461_);
lean_inc_ref(v___y_460_);
lean_inc(v___y_459_);
lean_inc_ref(v___y_458_);
v___x_467_ = lean_apply_9(v_G_457_, v___x_466_, v_a_464_, lean_box(0), lean_box(0), v___y_458_, v___y_459_, v___y_460_, v___y_461_, lean_box(0));
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed(lean_object* v_i_474_, lean_object* v___x_475_, lean_object* v_discrs_476_, lean_object* v_prior_477_, lean_object* v_next_478_, lean_object* v_acc_479_, lean_object* v_h_480_, lean_object* v_G_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16(v_i_474_, v___x_475_, v_discrs_476_, v_prior_477_, v_next_478_, v_acc_479_, v_h_480_, v_G_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v_next_478_);
lean_dec_ref(v_prior_477_);
lean_dec_ref(v_discrs_476_);
lean_dec_ref(v___x_475_);
lean_dec(v_i_474_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(lean_object* v_a_488_, lean_object* v___f_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v___x_495_; 
lean_inc(v___y_493_);
lean_inc_ref(v___y_492_);
lean_inc(v___y_491_);
lean_inc_ref(v___y_490_);
v___x_495_ = lean_infer_type(v_a_488_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___x_497_; lean_object* v___x_2358__overap_498_; lean_object* v___x_499_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_a_496_);
lean_dec_ref_known(v___x_495_, 1);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_2358__overap_498_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_489_, v___x_497_, v_a_496_, lean_box(0));
v___x_499_ = lean_apply_5(v___x_2358__overap_498_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, lean_box(0));
return v___x_499_;
}
else
{
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec_ref(v___f_489_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17___boxed(lean_object* v_a_500_, lean_object* v___f_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17(v_a_500_, v___f_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18(lean_object* v_i_508_, lean_object* v___x_509_, lean_object* v_discrs_510_, lean_object* v_a_511_, lean_object* v_inst_512_, lean_object* v_prior_513_){
_start:
{
lean_object* v___f_514_; lean_object* v___f_515_; lean_object* v___x_516_; 
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__16___boxed), 13, 4);
lean_closure_set(v___f_514_, 0, v_i_508_);
lean_closure_set(v___f_514_, 1, v___x_509_);
lean_closure_set(v___f_514_, 2, v_discrs_510_);
lean_closure_set(v___f_514_, 3, v_prior_513_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__17___boxed), 7, 2);
lean_closure_set(v___f_515_, 0, v_a_511_);
lean_closure_set(v___f_515_, 1, v___f_514_);
v___x_516_ = lean_apply_2(v_inst_512_, lean_box(0), v___f_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19(lean_object* v___x_520_, lean_object* v_discrs_521_, lean_object* v_inst_522_, lean_object* v_i_523_, lean_object* v_a_524_, lean_object* v_x_525_){
_start:
{
lean_object* v___f_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
lean_inc(v_i_523_);
v___f_526_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__18), 6, 5);
lean_closure_set(v___f_526_, 0, v_i_523_);
lean_closure_set(v___f_526_, 1, v___x_520_);
lean_closure_set(v___f_526_, 2, v_discrs_521_);
lean_closure_set(v___f_526_, 3, v_a_524_);
lean_closure_set(v___f_526_, 4, v_inst_522_);
v___x_527_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19___closed__1));
v___x_528_ = lean_unsigned_to_nat(1u);
v___x_529_ = lean_nat_add(v_i_523_, v___x_528_);
lean_dec(v_i_523_);
v___x_530_ = lean_name_append_index_after(v___x_527_, v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___f_526_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(lean_object* v_toMatcherInfo_534_, lean_object* v_matcherName_535_, lean_object* v_matcherLevels_536_, lean_object* v_params_537_, lean_object* v_motive_538_, lean_object* v_discrs_539_, lean_object* v_alts_540_, lean_object* v_k_541_, lean_object* v_____do__lift_542_){
_start:
{
lean_object* v___x_543_; lean_object* v_abstractMatcherApp_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_543_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
lean_inc_ref(v_discrs_539_);
v_abstractMatcherApp_544_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_abstractMatcherApp_544_, 0, v_toMatcherInfo_534_);
lean_ctor_set(v_abstractMatcherApp_544_, 1, v_matcherName_535_);
lean_ctor_set(v_abstractMatcherApp_544_, 2, v_matcherLevels_536_);
lean_ctor_set(v_abstractMatcherApp_544_, 3, v_params_537_);
lean_ctor_set(v_abstractMatcherApp_544_, 4, v_motive_538_);
lean_ctor_set(v_abstractMatcherApp_544_, 5, v_discrs_539_);
lean_ctor_set(v_abstractMatcherApp_544_, 6, v_____do__lift_542_);
lean_ctor_set(v_abstractMatcherApp_544_, 7, v___x_543_);
v___x_545_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_545_, 0, v_abstractMatcherApp_544_);
v___x_546_ = l_Array_append___redArg(v_discrs_539_, v_alts_540_);
v___x_547_ = lean_apply_2(v_k_541_, v___x_545_, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed(lean_object* v_toMatcherInfo_548_, lean_object* v_matcherName_549_, lean_object* v_matcherLevels_550_, lean_object* v_params_551_, lean_object* v_motive_552_, lean_object* v_discrs_553_, lean_object* v_alts_554_, lean_object* v_k_555_, lean_object* v_____do__lift_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20(v_toMatcherInfo_548_, v_matcherName_549_, v_matcherLevels_550_, v_params_551_, v_motive_552_, v_discrs_553_, v_alts_554_, v_k_555_, v_____do__lift_556_);
lean_dec_ref(v_alts_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21(lean_object* v_toMatcherInfo_559_, lean_object* v_matcherName_560_, lean_object* v_matcherLevels_561_, lean_object* v_params_562_, lean_object* v_motive_563_, lean_object* v_discrs_564_, lean_object* v_k_565_, lean_object* v___x_566_, lean_object* v_inst_567_, lean_object* v_toBind_568_, lean_object* v_alts_569_){
_start:
{
lean_object* v___f_570_; lean_object* v___x_571_; size_t v_sz_572_; size_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
lean_inc_ref(v_alts_569_);
v___f_570_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___boxed), 9, 8);
lean_closure_set(v___f_570_, 0, v_toMatcherInfo_559_);
lean_closure_set(v___f_570_, 1, v_matcherName_560_);
lean_closure_set(v___f_570_, 2, v_matcherLevels_561_);
lean_closure_set(v___f_570_, 3, v_params_562_);
lean_closure_set(v___f_570_, 4, v_motive_563_);
lean_closure_set(v___f_570_, 5, v_discrs_564_);
lean_closure_set(v___f_570_, 6, v_alts_569_);
lean_closure_set(v___f_570_, 7, v_k_565_);
v___x_571_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21___closed__0));
v_sz_572_ = lean_array_size(v_alts_569_);
v___x_573_ = ((size_t)0ULL);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_566_, v___x_571_, v_sz_572_, v___x_573_, v_alts_569_);
v___x_575_ = lean_apply_2(v_inst_567_, lean_box(0), v___x_574_);
v___x_576_ = lean_apply_4(v_toBind_568_, lean_box(0), lean_box(0), v___x_575_, v___f_570_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22(lean_object* v___f_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v___f_599_, lean_object* v_origAltTypes_600_){
_start:
{
lean_object* v___x_601_; size_t v_sz_602_; size_t v___x_603_; lean_object* v_altNamesTypes_604_; uint8_t v___x_605_; lean_object* v___x_606_; 
v___x_601_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9));
v_sz_602_ = lean_array_size(v_origAltTypes_600_);
v___x_603_ = ((size_t)0ULL);
lean_inc_ref(v_origAltTypes_600_);
v_altNamesTypes_604_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_601_, v_origAltTypes_600_, v___f_596_, v_sz_602_, v___x_603_, v_origAltTypes_600_);
lean_dec_ref(v_origAltTypes_600_);
v___x_605_ = 0;
v___x_606_ = l_Lean_Meta_withLocalDeclsDND___redArg(v_inst_597_, v_inst_598_, v_altNamesTypes_604_, v___f_599_, v___x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(lean_object* v_toMatcherInfo_607_, lean_object* v_matcherName_608_, lean_object* v_params_609_, lean_object* v_motive_610_, lean_object* v_discrs_611_, lean_object* v_k_612_, lean_object* v___x_613_, lean_object* v_inst_614_, lean_object* v_toBind_615_, lean_object* v___f_616_, lean_object* v_inst_617_, lean_object* v_inst_618_, lean_object* v_alts_619_, lean_object* v_matcherLevels_620_){
_start:
{
lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_matcherPartial_625_; lean_object* v_matcherPartial_626_; lean_object* v_matcherPartial_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
lean_inc(v_toBind_615_);
lean_inc(v_inst_614_);
lean_inc_ref(v_discrs_611_);
lean_inc_ref(v_motive_610_);
lean_inc_ref(v_params_609_);
lean_inc_ref(v_matcherLevels_620_);
lean_inc(v_matcherName_608_);
v___f_621_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__21), 11, 10);
lean_closure_set(v___f_621_, 0, v_toMatcherInfo_607_);
lean_closure_set(v___f_621_, 1, v_matcherName_608_);
lean_closure_set(v___f_621_, 2, v_matcherLevels_620_);
lean_closure_set(v___f_621_, 3, v_params_609_);
lean_closure_set(v___f_621_, 4, v_motive_610_);
lean_closure_set(v___f_621_, 5, v_discrs_611_);
lean_closure_set(v___f_621_, 6, v_k_612_);
lean_closure_set(v___f_621_, 7, v___x_613_);
lean_closure_set(v___f_621_, 8, v_inst_614_);
lean_closure_set(v___f_621_, 9, v_toBind_615_);
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22), 5, 4);
lean_closure_set(v___f_622_, 0, v___f_616_);
lean_closure_set(v___f_622_, 1, v_inst_617_);
lean_closure_set(v___f_622_, 2, v_inst_618_);
lean_closure_set(v___f_622_, 3, v___f_621_);
v___x_623_ = lean_array_to_list(v_matcherLevels_620_);
v___x_624_ = l_Lean_mkConst(v_matcherName_608_, v___x_623_);
v_matcherPartial_625_ = l_Lean_mkAppN(v___x_624_, v_params_609_);
lean_dec_ref(v_params_609_);
v_matcherPartial_626_ = l_Lean_Expr_app___override(v_matcherPartial_625_, v_motive_610_);
v_matcherPartial_627_ = l_Lean_mkAppN(v_matcherPartial_626_, v_discrs_611_);
lean_dec_ref(v_discrs_611_);
v___x_628_ = lean_array_get_size(v_alts_619_);
v___x_629_ = lean_alloc_closure((void*)(l_Lean_Meta_inferArgumentTypesN___boxed), 7, 2);
lean_closure_set(v___x_629_, 0, v___x_628_);
lean_closure_set(v___x_629_, 1, v_matcherPartial_627_);
v___x_630_ = lean_apply_2(v_inst_614_, lean_box(0), v___x_629_);
v___x_631_ = lean_apply_4(v_toBind_615_, lean_box(0), lean_box(0), v___x_630_, v___f_622_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___boxed(lean_object* v_toMatcherInfo_632_, lean_object* v_matcherName_633_, lean_object* v_params_634_, lean_object* v_motive_635_, lean_object* v_discrs_636_, lean_object* v_k_637_, lean_object* v___x_638_, lean_object* v_inst_639_, lean_object* v_toBind_640_, lean_object* v___f_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_alts_644_, lean_object* v_matcherLevels_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23(v_toMatcherInfo_632_, v_matcherName_633_, v_params_634_, v_motive_635_, v_discrs_636_, v_k_637_, v___x_638_, v_inst_639_, v_toBind_640_, v___f_641_, v_inst_642_, v_inst_643_, v_alts_644_, v_matcherLevels_645_);
lean_dec_ref(v_alts_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24(lean_object* v___f_647_, lean_object* v_matcherLevels_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_apply_1(v___f_647_, v_matcherLevels_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(lean_object* v_matcherLevels_650_, lean_object* v_val_651_, lean_object* v_toPure_652_, lean_object* v_toBind_653_, lean_object* v___f_654_, lean_object* v_uElim_655_){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_656_ = lean_array_set(v_matcherLevels_650_, v_val_651_, v_uElim_655_);
v___x_657_ = lean_apply_2(v_toPure_652_, lean_box(0), v___x_656_);
v___x_658_ = lean_apply_4(v_toBind_653_, lean_box(0), lean_box(0), v___x_657_, v___f_654_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___boxed(lean_object* v_matcherLevels_659_, lean_object* v_val_660_, lean_object* v_toPure_661_, lean_object* v_toBind_662_, lean_object* v___f_663_, lean_object* v_uElim_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26(v_matcherLevels_659_, v_val_660_, v_toPure_661_, v_toBind_662_, v___f_663_, v_uElim_664_);
lean_dec(v_val_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25(lean_object* v_toMatcherInfo_666_, lean_object* v_matcherName_667_, lean_object* v_params_668_, lean_object* v_discrs_669_, lean_object* v_k_670_, lean_object* v___x_671_, lean_object* v_inst_672_, lean_object* v_toBind_673_, lean_object* v___f_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_alts_677_, lean_object* v_toPure_678_, lean_object* v_matcherLevels_679_, lean_object* v_resTy_680_, lean_object* v_motive_681_){
_start:
{
lean_object* v_uElimPos_x3f_682_; lean_object* v___f_683_; 
v_uElimPos_x3f_682_ = lean_ctor_get(v_toMatcherInfo_666_, 3);
lean_inc(v_uElimPos_x3f_682_);
lean_inc(v_toBind_673_);
lean_inc(v_inst_672_);
v___f_683_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__23___boxed), 14, 13);
lean_closure_set(v___f_683_, 0, v_toMatcherInfo_666_);
lean_closure_set(v___f_683_, 1, v_matcherName_667_);
lean_closure_set(v___f_683_, 2, v_params_668_);
lean_closure_set(v___f_683_, 3, v_motive_681_);
lean_closure_set(v___f_683_, 4, v_discrs_669_);
lean_closure_set(v___f_683_, 5, v_k_670_);
lean_closure_set(v___f_683_, 6, v___x_671_);
lean_closure_set(v___f_683_, 7, v_inst_672_);
lean_closure_set(v___f_683_, 8, v_toBind_673_);
lean_closure_set(v___f_683_, 9, v___f_674_);
lean_closure_set(v___f_683_, 10, v_inst_675_);
lean_closure_set(v___f_683_, 11, v_inst_676_);
lean_closure_set(v___f_683_, 12, v_alts_677_);
if (lean_obj_tag(v_uElimPos_x3f_682_) == 0)
{
lean_object* v___f_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec_ref(v_resTy_680_);
lean_dec(v_inst_672_);
v___f_684_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24), 2, 1);
lean_closure_set(v___f_684_, 0, v___f_683_);
v___x_685_ = lean_apply_2(v_toPure_678_, lean_box(0), v_matcherLevels_679_);
v___x_686_ = lean_apply_4(v_toBind_673_, lean_box(0), lean_box(0), v___x_685_, v___f_684_);
return v___x_686_;
}
else
{
lean_object* v_val_687_; lean_object* v___f_688_; lean_object* v___f_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v_val_687_ = lean_ctor_get(v_uElimPos_x3f_682_, 0);
lean_inc(v_val_687_);
lean_dec_ref_known(v_uElimPos_x3f_682_, 1);
v___f_688_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__24), 2, 1);
lean_closure_set(v___f_688_, 0, v___f_683_);
lean_inc(v_toBind_673_);
v___f_689_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__26___boxed), 6, 5);
lean_closure_set(v___f_689_, 0, v_matcherLevels_679_);
lean_closure_set(v___f_689_, 1, v_val_687_);
lean_closure_set(v___f_689_, 2, v_toPure_678_);
lean_closure_set(v___f_689_, 3, v_toBind_673_);
lean_closure_set(v___f_689_, 4, v___f_688_);
v___x_690_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_690_, 0, v_resTy_680_);
v___x_691_ = lean_apply_2(v_inst_672_, lean_box(0), v___x_690_);
v___x_692_ = lean_apply_4(v_toBind_673_, lean_box(0), lean_box(0), v___x_691_, v___f_689_);
return v___x_692_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(lean_object* v_toMatcherInfo_693_, lean_object* v_matcherName_694_, lean_object* v_params_695_, lean_object* v_k_696_, lean_object* v___x_697_, lean_object* v_inst_698_, lean_object* v_toBind_699_, lean_object* v___f_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_alts_703_, lean_object* v_toPure_704_, lean_object* v_matcherLevels_705_, lean_object* v_resTy_706_, lean_object* v___x_707_, lean_object* v_motive_708_, lean_object* v___f_709_, lean_object* v_discrs_710_){
_start:
{
lean_object* v___f_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_inc(v_toBind_699_);
lean_inc(v_inst_698_);
lean_inc_ref(v___x_697_);
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__25), 16, 15);
lean_closure_set(v___f_711_, 0, v_toMatcherInfo_693_);
lean_closure_set(v___f_711_, 1, v_matcherName_694_);
lean_closure_set(v___f_711_, 2, v_params_695_);
lean_closure_set(v___f_711_, 3, v_discrs_710_);
lean_closure_set(v___f_711_, 4, v_k_696_);
lean_closure_set(v___f_711_, 5, v___x_697_);
lean_closure_set(v___f_711_, 6, v_inst_698_);
lean_closure_set(v___f_711_, 7, v_toBind_699_);
lean_closure_set(v___f_711_, 8, v___f_700_);
lean_closure_set(v___f_711_, 9, v_inst_701_);
lean_closure_set(v___f_711_, 10, v_inst_702_);
lean_closure_set(v___f_711_, 11, v_alts_703_);
lean_closure_set(v___f_711_, 12, v_toPure_704_);
lean_closure_set(v___f_711_, 13, v_matcherLevels_705_);
lean_closure_set(v___f_711_, 14, v_resTy_706_);
v___x_712_ = 0;
v___x_713_ = l_Lean_Meta_lambdaTelescope___redArg(v___x_707_, v___x_697_, v_motive_708_, v___f_709_, v___x_712_);
v___x_714_ = lean_apply_2(v_inst_698_, lean_box(0), v___x_713_);
v___x_715_ = lean_apply_4(v_toBind_699_, lean_box(0), lean_box(0), v___x_714_, v___f_711_);
return v___x_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed(lean_object** _args){
lean_object* v_toMatcherInfo_716_ = _args[0];
lean_object* v_matcherName_717_ = _args[1];
lean_object* v_params_718_ = _args[2];
lean_object* v_k_719_ = _args[3];
lean_object* v___x_720_ = _args[4];
lean_object* v_inst_721_ = _args[5];
lean_object* v_toBind_722_ = _args[6];
lean_object* v___f_723_ = _args[7];
lean_object* v_inst_724_ = _args[8];
lean_object* v_inst_725_ = _args[9];
lean_object* v_alts_726_ = _args[10];
lean_object* v_toPure_727_ = _args[11];
lean_object* v_matcherLevels_728_ = _args[12];
lean_object* v_resTy_729_ = _args[13];
lean_object* v___x_730_ = _args[14];
lean_object* v_motive_731_ = _args[15];
lean_object* v___f_732_ = _args[16];
lean_object* v_discrs_733_ = _args[17];
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27(v_toMatcherInfo_716_, v_matcherName_717_, v_params_718_, v_k_719_, v___x_720_, v_inst_721_, v_toBind_722_, v___f_723_, v_inst_724_, v_inst_725_, v_alts_726_, v_toPure_727_, v_matcherLevels_728_, v_resTy_729_, v___x_730_, v_motive_731_, v___f_732_, v_discrs_733_);
return v_res_734_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0(void){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_instMonadEIO(lean_box(0));
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__0);
v___x_737_ = l_StateRefT_x27_instMonad___redArg(v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = l_Lean_Level_ofNat(v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__8);
v___x_748_ = l_Lean_mkSort(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_info_753_, lean_object* v_resTy_754_, lean_object* v_k_755_){
_start:
{
lean_object* v___x_756_; lean_object* v_toApplicative_757_; lean_object* v_toFunctor_758_; lean_object* v_toSeq_759_; lean_object* v_toSeqLeft_760_; lean_object* v_toSeqRight_761_; lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___f_764_; lean_object* v___f_765_; lean_object* v___x_766_; lean_object* v___f_767_; lean_object* v___f_768_; lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v_toApplicative_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_848_; 
v___x_756_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_757_ = lean_ctor_get(v___x_756_, 0);
v_toFunctor_758_ = lean_ctor_get(v_toApplicative_757_, 0);
v_toSeq_759_ = lean_ctor_get(v_toApplicative_757_, 2);
v_toSeqLeft_760_ = lean_ctor_get(v_toApplicative_757_, 3);
v_toSeqRight_761_ = lean_ctor_get(v_toApplicative_757_, 4);
v___f_762_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_763_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_758_, 2);
v___f_764_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_764_, 0, v_toFunctor_758_);
v___f_765_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_765_, 0, v_toFunctor_758_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___f_764_);
lean_ctor_set(v___x_766_, 1, v___f_765_);
lean_inc(v_toSeqRight_761_);
v___f_767_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_767_, 0, v_toSeqRight_761_);
lean_inc(v_toSeqLeft_760_);
v___f_768_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_768_, 0, v_toSeqLeft_760_);
lean_inc(v_toSeq_759_);
v___f_769_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_769_, 0, v_toSeq_759_);
v___x_770_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_770_, 0, v___x_766_);
lean_ctor_set(v___x_770_, 1, v___f_762_);
lean_ctor_set(v___x_770_, 2, v___f_769_);
lean_ctor_set(v___x_770_, 3, v___f_768_);
lean_ctor_set(v___x_770_, 4, v___f_767_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_770_);
lean_ctor_set(v___x_771_, 1, v___f_763_);
v___x_772_ = l_StateRefT_x27_instMonad___redArg(v___x_771_);
v_toApplicative_773_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v___x_772_, 1);
lean_dec(v_unused_849_);
v___x_775_ = v___x_772_;
v_isShared_776_ = v_isSharedCheck_848_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_toApplicative_773_);
lean_dec(v___x_772_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_848_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_toFunctor_777_; lean_object* v_toSeq_778_; lean_object* v_toSeqLeft_779_; lean_object* v_toSeqRight_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_846_; 
v_toFunctor_777_ = lean_ctor_get(v_toApplicative_773_, 0);
v_toSeq_778_ = lean_ctor_get(v_toApplicative_773_, 2);
v_toSeqLeft_779_ = lean_ctor_get(v_toApplicative_773_, 3);
v_toSeqRight_780_ = lean_ctor_get(v_toApplicative_773_, 4);
v_isSharedCheck_846_ = !lean_is_exclusive(v_toApplicative_773_);
if (v_isSharedCheck_846_ == 0)
{
lean_object* v_unused_847_; 
v_unused_847_ = lean_ctor_get(v_toApplicative_773_, 1);
lean_dec(v_unused_847_);
v___x_782_ = v_toApplicative_773_;
v_isShared_783_ = v_isSharedCheck_846_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_toSeqRight_780_);
lean_inc(v_toSeqLeft_779_);
lean_inc(v_toSeq_778_);
lean_inc(v_toFunctor_777_);
lean_dec(v_toApplicative_773_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_846_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___f_784_; lean_object* v___f_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___x_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___x_793_; 
v___f_784_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_785_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_777_);
v___f_786_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_786_, 0, v_toFunctor_777_);
v___f_787_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_787_, 0, v_toFunctor_777_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___f_786_);
lean_ctor_set(v___x_788_, 1, v___f_787_);
v___f_789_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_789_, 0, v_toSeqRight_780_);
v___f_790_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_790_, 0, v_toSeqLeft_779_);
v___f_791_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_791_, 0, v_toSeq_778_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 4, v___f_789_);
lean_ctor_set(v___x_782_, 3, v___f_790_);
lean_ctor_set(v___x_782_, 2, v___f_791_);
lean_ctor_set(v___x_782_, 1, v___f_784_);
lean_ctor_set(v___x_782_, 0, v___x_788_);
v___x_793_ = v___x_782_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v___f_784_);
lean_ctor_set(v_reuseFailAlloc_845_, 2, v___f_791_);
lean_ctor_set(v_reuseFailAlloc_845_, 3, v___f_790_);
lean_ctor_set(v_reuseFailAlloc_845_, 4, v___f_789_);
v___x_793_ = v_reuseFailAlloc_845_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v___f_785_);
lean_ctor_set(v___x_775_, 0, v___x_793_);
v___x_795_ = v___x_775_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___f_785_);
v___x_795_ = v_reuseFailAlloc_844_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v_toApplicative_796_; lean_object* v_toFunctor_797_; lean_object* v_toSeq_798_; lean_object* v_toSeqLeft_799_; lean_object* v_toSeqRight_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_toApplicative_796_ = lean_ctor_get(v___x_756_, 0);
v_toFunctor_797_ = lean_ctor_get(v_toApplicative_796_, 0);
v_toSeq_798_ = lean_ctor_get(v_toApplicative_796_, 2);
v_toSeqLeft_799_ = lean_ctor_get(v_toApplicative_796_, 3);
v_toSeqRight_800_ = lean_ctor_get(v_toApplicative_796_, 4);
lean_inc_ref_n(v_toFunctor_797_, 2);
v___f_801_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_801_, 0, v_toFunctor_797_);
v___f_802_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_802_, 0, v_toFunctor_797_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___f_801_);
lean_ctor_set(v___x_803_, 1, v___f_802_);
lean_inc(v_toSeqRight_800_);
v___f_804_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_804_, 0, v_toSeqRight_800_);
lean_inc(v_toSeqLeft_799_);
v___f_805_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_805_, 0, v_toSeqLeft_799_);
lean_inc(v_toSeq_798_);
v___f_806_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_806_, 0, v_toSeq_798_);
v___x_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_807_, 0, v___x_803_);
lean_ctor_set(v___x_807_, 1, v___f_762_);
lean_ctor_set(v___x_807_, 2, v___f_806_);
lean_ctor_set(v___x_807_, 3, v___f_805_);
lean_ctor_set(v___x_807_, 4, v___f_804_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___f_763_);
v___x_809_ = l_StateRefT_x27_instMonad___redArg(v___x_808_);
v___x_810_ = lean_alloc_closure((void*)(l_ReaderT_pure___boxed), 6, 3);
lean_closure_set(v___x_810_, 0, lean_box(0));
lean_closure_set(v___x_810_, 1, lean_box(0));
lean_closure_set(v___x_810_, 2, v___x_809_);
v___x_811_ = l_instMonadControlTOfPure___redArg(v___x_810_);
switch(lean_obj_tag(v_info_753_))
{
case 0:
{
lean_object* v_toBind_812_; lean_object* v___f_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec_ref_known(v_info_753_, 1);
lean_dec_ref(v___x_811_);
lean_dec_ref(v___x_795_);
v_toBind_812_ = lean_ctor_get(v_inst_752_, 1);
lean_inc_ref(v_inst_752_);
lean_inc_ref(v_inst_751_);
lean_inc(v_toBind_812_);
v___f_813_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__4), 7, 6);
lean_closure_set(v___f_813_, 0, v_resTy_754_);
lean_closure_set(v___f_813_, 1, v_k_755_);
lean_closure_set(v___f_813_, 2, v_inst_750_);
lean_closure_set(v___f_813_, 3, v_toBind_812_);
lean_closure_set(v___f_813_, 4, v_inst_751_);
lean_closure_set(v___f_813_, 5, v_inst_752_);
v___x_814_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_815_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_816_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_751_, v_inst_752_, v___x_814_, v___x_815_, v___f_813_);
return v___x_816_;
}
case 1:
{
lean_object* v_toBind_817_; lean_object* v___f_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec_ref_known(v_info_753_, 1);
lean_dec_ref(v___x_811_);
lean_dec_ref(v___x_795_);
v_toBind_817_ = lean_ctor_get(v_inst_752_, 1);
lean_inc_ref(v_inst_752_);
lean_inc_ref(v_inst_751_);
lean_inc(v_toBind_817_);
v___f_818_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__13), 7, 6);
lean_closure_set(v___f_818_, 0, v_resTy_754_);
lean_closure_set(v___f_818_, 1, v_k_755_);
lean_closure_set(v___f_818_, 2, v_inst_750_);
lean_closure_set(v___f_818_, 3, v_toBind_817_);
lean_closure_set(v___f_818_, 4, v_inst_751_);
lean_closure_set(v___f_818_, 5, v_inst_752_);
v___x_819_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__7));
v___x_820_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__9);
v___x_821_ = l_Lean_Meta_withLocalDeclD___redArg(v_inst_751_, v_inst_752_, v___x_819_, v___x_820_, v___f_818_);
return v___x_821_;
}
default: 
{
lean_object* v_toApplicative_822_; lean_object* v_matcherApp_823_; lean_object* v_toBind_824_; lean_object* v_toPure_825_; lean_object* v_toMatcherInfo_826_; lean_object* v_matcherName_827_; lean_object* v_matcherLevels_828_; lean_object* v_params_829_; lean_object* v_motive_830_; lean_object* v_discrs_831_; lean_object* v_alts_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___f_836_; lean_object* v___f_837_; lean_object* v___x_838_; size_t v_sz_839_; size_t v___x_840_; lean_object* v_discrDecls_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v_toApplicative_822_ = lean_ctor_get(v_inst_752_, 0);
v_matcherApp_823_ = lean_ctor_get(v_info_753_, 0);
lean_inc_ref(v_matcherApp_823_);
lean_dec_ref_known(v_info_753_, 1);
v_toBind_824_ = lean_ctor_get(v_inst_752_, 1);
v_toPure_825_ = lean_ctor_get(v_toApplicative_822_, 1);
v_toMatcherInfo_826_ = lean_ctor_get(v_matcherApp_823_, 0);
lean_inc_ref(v_toMatcherInfo_826_);
v_matcherName_827_ = lean_ctor_get(v_matcherApp_823_, 1);
lean_inc(v_matcherName_827_);
v_matcherLevels_828_ = lean_ctor_get(v_matcherApp_823_, 2);
lean_inc_ref(v_matcherLevels_828_);
v_params_829_ = lean_ctor_get(v_matcherApp_823_, 3);
lean_inc_ref(v_params_829_);
v_motive_830_ = lean_ctor_get(v_matcherApp_823_, 4);
lean_inc_ref(v_motive_830_);
v_discrs_831_ = lean_ctor_get(v_matcherApp_823_, 5);
lean_inc_ref_n(v_discrs_831_, 3);
v_alts_832_ = lean_ctor_get(v_matcherApp_823_, 6);
lean_inc_ref(v_alts_832_);
lean_dec_ref(v_matcherApp_823_);
v___f_833_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__10));
lean_inc_ref(v_resTy_754_);
v___f_834_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__15___boxed), 8, 1);
lean_closure_set(v___f_834_, 0, v_resTy_754_);
v___x_835_ = l_Lean_instInhabitedExpr;
lean_inc(v_inst_750_);
v___f_836_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__19), 6, 3);
lean_closure_set(v___f_836_, 0, v___x_835_);
lean_closure_set(v___f_836_, 1, v_discrs_831_);
lean_closure_set(v___f_836_, 2, v_inst_750_);
lean_inc(v_toPure_825_);
lean_inc_ref(v_inst_752_);
lean_inc_ref(v_inst_751_);
lean_inc(v_toBind_824_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__27___boxed), 18, 17);
lean_closure_set(v___f_837_, 0, v_toMatcherInfo_826_);
lean_closure_set(v___f_837_, 1, v_matcherName_827_);
lean_closure_set(v___f_837_, 2, v_params_829_);
lean_closure_set(v___f_837_, 3, v_k_755_);
lean_closure_set(v___f_837_, 4, v___x_795_);
lean_closure_set(v___f_837_, 5, v_inst_750_);
lean_closure_set(v___f_837_, 6, v_toBind_824_);
lean_closure_set(v___f_837_, 7, v___f_833_);
lean_closure_set(v___f_837_, 8, v_inst_751_);
lean_closure_set(v___f_837_, 9, v_inst_752_);
lean_closure_set(v___f_837_, 10, v_alts_832_);
lean_closure_set(v___f_837_, 11, v_toPure_825_);
lean_closure_set(v___f_837_, 12, v_matcherLevels_828_);
lean_closure_set(v___f_837_, 13, v_resTy_754_);
lean_closure_set(v___f_837_, 14, v___x_811_);
lean_closure_set(v___f_837_, 15, v_motive_830_);
lean_closure_set(v___f_837_, 16, v___f_834_);
v___x_838_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9));
v_sz_839_ = lean_array_size(v_discrs_831_);
v___x_840_ = ((size_t)0ULL);
v_discrDecls_841_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_838_, v_discrs_831_, v___f_836_, v_sz_839_, v___x_840_, v_discrs_831_);
lean_dec_ref(v_discrs_831_);
v___x_842_ = 0;
v___x_843_ = l_Lean_Meta_withLocalDeclsD___redArg(v_inst_751_, v_inst_752_, v_discrDecls_841_, v___f_837_, v___x_842_);
return v___x_843_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(lean_object* v_n_850_, lean_object* v_00_u03b1_851_, lean_object* v_inst_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_info_856_, lean_object* v_resTy_857_, lean_object* v_k_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg(v_inst_852_, v_inst_853_, v_inst_854_, v_info_856_, v_resTy_857_, v_k_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___boxed(lean_object* v_n_860_, lean_object* v_00_u03b1_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_info_866_, lean_object* v_resTy_867_, lean_object* v_k_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract(v_n_860_, v_00_u03b1_861_, v_inst_862_, v_inst_863_, v_inst_864_, v_inst_865_, v_info_866_, v_resTy_867_, v_k_868_);
lean_dec(v_inst_865_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0(lean_object* v_u_870_, lean_object* v_resTy_871_, lean_object* v_c_872_, lean_object* v_h_873_, lean_object* v_t_874_, lean_object* v_toPure_875_, lean_object* v_e_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_877_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_878_ = lean_box(0);
v___x_879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_879_, 0, v_u_870_);
lean_ctor_set(v___x_879_, 1, v___x_878_);
v___x_880_ = l_Lean_mkConst(v___x_877_, v___x_879_);
v___x_881_ = l_Lean_mkApp5(v___x_880_, v_resTy_871_, v_c_872_, v_h_873_, v_t_874_, v_e_876_);
v___x_882_ = lean_apply_2(v_toPure_875_, lean_box(0), v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1(lean_object* v_u_886_, lean_object* v_resTy_887_, lean_object* v_c_888_, lean_object* v_h_889_, lean_object* v_toPure_890_, lean_object* v_onAlt_891_, lean_object* v___x_892_, lean_object* v___x_893_, lean_object* v_toBind_894_, lean_object* v_t_895_){
_start:
{
lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_inc_ref(v_resTy_887_);
v___f_896_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__0), 7, 6);
lean_closure_set(v___f_896_, 0, v_u_886_);
lean_closure_set(v___f_896_, 1, v_resTy_887_);
lean_closure_set(v___f_896_, 2, v_c_888_);
lean_closure_set(v___f_896_, 3, v_h_889_);
lean_closure_set(v___f_896_, 4, v_t_895_);
lean_closure_set(v___f_896_, 5, v_toPure_890_);
v___x_897_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_898_ = lean_apply_4(v_onAlt_891_, v___x_897_, v_resTy_887_, v___x_892_, v___x_893_);
v___x_899_ = lean_apply_4(v_toBind_894_, lean_box(0), lean_box(0), v___x_898_, v___f_896_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(lean_object* v___x_900_, uint8_t v_useSplitter_901_, lean_object* v_inst_902_, lean_object* v_____do__lift_903_){
_start:
{
uint8_t v___x_904_; uint8_t v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_904_ = 0;
v___x_905_ = 1;
v___x_906_ = lean_box(v___x_904_);
v___x_907_ = lean_box(v_useSplitter_901_);
v___x_908_ = lean_box(v___x_904_);
v___x_909_ = lean_box(v_useSplitter_901_);
v___x_910_ = lean_box(v___x_905_);
v___x_911_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_911_, 0, v___x_900_);
lean_closure_set(v___x_911_, 1, v_____do__lift_903_);
lean_closure_set(v___x_911_, 2, v___x_906_);
lean_closure_set(v___x_911_, 3, v___x_907_);
lean_closure_set(v___x_911_, 4, v___x_908_);
lean_closure_set(v___x_911_, 5, v___x_909_);
lean_closure_set(v___x_911_, 6, v___x_910_);
v___x_912_ = lean_apply_2(v_inst_902_, lean_box(0), v___x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed(lean_object* v___x_913_, lean_object* v_useSplitter_914_, lean_object* v_inst_915_, lean_object* v_____do__lift_916_){
_start:
{
uint8_t v_useSplitter_boxed_917_; lean_object* v_res_918_; 
v_useSplitter_boxed_917_ = lean_unbox(v_useSplitter_914_);
v_res_918_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2(v___x_913_, v_useSplitter_boxed_917_, v_inst_915_, v_____do__lift_916_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(lean_object* v___x_922_, uint8_t v_useSplitter_923_, lean_object* v_inst_924_, lean_object* v_onAlt_925_, lean_object* v_resTy_926_, lean_object* v_toBind_927_, lean_object* v_h_928_){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___f_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_932_ = lean_mk_empty_array_with_capacity(v___x_922_);
v___x_933_ = lean_array_push(v___x_932_, v_h_928_);
v___x_934_ = lean_box(v_useSplitter_923_);
lean_inc_ref(v___x_933_);
v___f_935_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_935_, 0, v___x_933_);
lean_closure_set(v___f_935_, 1, v___x_934_);
lean_closure_set(v___f_935_, 2, v_inst_924_);
v___x_936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_936_, 0, v___x_931_);
lean_ctor_set(v___x_936_, 1, v___x_933_);
lean_ctor_set(v___x_936_, 2, v___x_931_);
lean_ctor_set(v___x_936_, 3, v___x_931_);
lean_ctor_set(v___x_936_, 4, v___x_931_);
v___x_937_ = lean_apply_4(v_onAlt_925_, v___x_929_, v_resTy_926_, v___x_930_, v___x_936_);
v___x_938_ = lean_apply_4(v_toBind_927_, lean_box(0), lean_box(0), v___x_937_, v___f_935_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed(lean_object* v___x_939_, lean_object* v_useSplitter_940_, lean_object* v_inst_941_, lean_object* v_onAlt_942_, lean_object* v_resTy_943_, lean_object* v_toBind_944_, lean_object* v_h_945_){
_start:
{
uint8_t v_useSplitter_boxed_946_; lean_object* v_res_947_; 
v_useSplitter_boxed_946_ = lean_unbox(v_useSplitter_940_);
v_res_947_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3(v___x_939_, v_useSplitter_boxed_946_, v_inst_941_, v_onAlt_942_, v_resTy_943_, v_toBind_944_, v_h_945_);
lean_dec(v___x_939_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(lean_object* v___x_948_, uint8_t v_useSplitter_949_, lean_object* v_inst_950_, lean_object* v_onAlt_951_, lean_object* v_resTy_952_, lean_object* v_toBind_953_, lean_object* v_h_954_){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___f_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_955_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_956_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_957_ = lean_mk_empty_array_with_capacity(v___x_948_);
v___x_958_ = lean_array_push(v___x_957_, v_h_954_);
v___x_959_ = lean_box(v_useSplitter_949_);
lean_inc_ref(v___x_958_);
v___f_960_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_960_, 0, v___x_958_);
lean_closure_set(v___f_960_, 1, v___x_959_);
lean_closure_set(v___f_960_, 2, v_inst_950_);
v___x_961_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_961_, 0, v___x_956_);
lean_ctor_set(v___x_961_, 1, v___x_958_);
lean_ctor_set(v___x_961_, 2, v___x_956_);
lean_ctor_set(v___x_961_, 3, v___x_956_);
lean_ctor_set(v___x_961_, 4, v___x_956_);
v___x_962_ = lean_apply_4(v_onAlt_951_, v___x_955_, v_resTy_952_, v___x_948_, v___x_961_);
v___x_963_ = lean_apply_4(v_toBind_953_, lean_box(0), lean_box(0), v___x_962_, v___f_960_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed(lean_object* v___x_964_, lean_object* v_useSplitter_965_, lean_object* v_inst_966_, lean_object* v_onAlt_967_, lean_object* v_resTy_968_, lean_object* v_toBind_969_, lean_object* v_h_970_){
_start:
{
uint8_t v_useSplitter_boxed_971_; lean_object* v_res_972_; 
v_useSplitter_boxed_971_ = lean_unbox(v_useSplitter_965_);
v_res_972_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5(v___x_964_, v_useSplitter_boxed_971_, v_inst_966_, v_onAlt_967_, v_resTy_968_, v_toBind_969_, v_h_970_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4(lean_object* v_u_973_, lean_object* v_resTy_974_, lean_object* v_c_975_, lean_object* v_h_976_, lean_object* v_t_977_, lean_object* v_toPure_978_, lean_object* v_e_979_){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_980_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_982_, 0, v_u_973_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Lean_mkConst(v___x_980_, v___x_982_);
v___x_984_ = l_Lean_mkApp5(v___x_983_, v_resTy_974_, v_c_975_, v_h_976_, v_t_977_, v_e_979_);
v___x_985_ = lean_apply_2(v_toPure_978_, lean_box(0), v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(lean_object* v_u_986_, lean_object* v_resTy_987_, lean_object* v_c_988_, lean_object* v_h_989_, lean_object* v_toPure_990_, lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_n_993_, uint8_t v___x_994_, lean_object* v___f_995_, uint8_t v___x_996_, lean_object* v_toBind_997_, lean_object* v_t_998_){
_start:
{
lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_inc_ref(v_c_988_);
v___f_999_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__4), 7, 6);
lean_closure_set(v___f_999_, 0, v_u_986_);
lean_closure_set(v___f_999_, 1, v_resTy_987_);
lean_closure_set(v___f_999_, 2, v_c_988_);
lean_closure_set(v___f_999_, 3, v_h_989_);
lean_closure_set(v___f_999_, 4, v_t_998_);
lean_closure_set(v___f_999_, 5, v_toPure_990_);
v___x_1000_ = l_Lean_mkNot(v_c_988_);
v___x_1001_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_991_, v_inst_992_, v_n_993_, v___x_994_, v___x_1000_, v___f_995_, v___x_996_);
v___x_1002_ = lean_apply_4(v_toBind_997_, lean_box(0), lean_box(0), v___x_1001_, v___f_999_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed(lean_object* v_u_1003_, lean_object* v_resTy_1004_, lean_object* v_c_1005_, lean_object* v_h_1006_, lean_object* v_toPure_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_n_1010_, lean_object* v___x_1011_, lean_object* v___f_1012_, lean_object* v___x_1013_, lean_object* v_toBind_1014_, lean_object* v_t_1015_){
_start:
{
uint8_t v___x_1387__boxed_1016_; uint8_t v___x_1389__boxed_1017_; lean_object* v_res_1018_; 
v___x_1387__boxed_1016_ = lean_unbox(v___x_1011_);
v___x_1389__boxed_1017_ = lean_unbox(v___x_1013_);
v_res_1018_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6(v_u_1003_, v_resTy_1004_, v_c_1005_, v_h_1006_, v_toPure_1007_, v_inst_1008_, v_inst_1009_, v_n_1010_, v___x_1387__boxed_1016_, v___f_1012_, v___x_1389__boxed_1017_, v_toBind_1014_, v_t_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7(lean_object* v_u_1019_, lean_object* v_resTy_1020_, lean_object* v_c_1021_, lean_object* v_h_1022_, lean_object* v_toPure_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v___f_1026_, lean_object* v_toBind_1027_, lean_object* v___f_1028_, lean_object* v_n_1029_){
_start:
{
uint8_t v___x_1030_; uint8_t v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___f_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1030_ = 0;
v___x_1031_ = 0;
v___x_1032_ = lean_box(v___x_1030_);
v___x_1033_ = lean_box(v___x_1031_);
lean_inc(v_toBind_1027_);
lean_inc(v_n_1029_);
lean_inc_ref(v_inst_1025_);
lean_inc_ref(v_inst_1024_);
lean_inc_ref(v_c_1021_);
v___f_1034_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1034_, 0, v_u_1019_);
lean_closure_set(v___f_1034_, 1, v_resTy_1020_);
lean_closure_set(v___f_1034_, 2, v_c_1021_);
lean_closure_set(v___f_1034_, 3, v_h_1022_);
lean_closure_set(v___f_1034_, 4, v_toPure_1023_);
lean_closure_set(v___f_1034_, 5, v_inst_1024_);
lean_closure_set(v___f_1034_, 6, v_inst_1025_);
lean_closure_set(v___f_1034_, 7, v_n_1029_);
lean_closure_set(v___f_1034_, 8, v___x_1032_);
lean_closure_set(v___f_1034_, 9, v___f_1026_);
lean_closure_set(v___f_1034_, 10, v___x_1033_);
lean_closure_set(v___f_1034_, 11, v_toBind_1027_);
v___x_1035_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_1024_, v_inst_1025_, v_n_1029_, v___x_1030_, v_c_1021_, v___f_1028_, v___x_1031_);
v___x_1036_ = lean_apply_4(v_toBind_1027_, lean_box(0), lean_box(0), v___x_1035_, v___f_1034_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(lean_object* v___x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Lean_Core_mkFreshUserName(v___x_1037_, v___y_1040_, v___y_1041_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8___boxed(lean_object* v___x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__8(v___x_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(lean_object* v_e_1058_, uint8_t v_useSplitter_1059_, lean_object* v_resTy_1060_, lean_object* v_toPure_1061_, lean_object* v_onAlt_1062_, lean_object* v_toBind_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_u_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v_c_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_h_1076_; 
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = l_Lean_Expr_getAppNumArgs(v_e_1058_);
v___x_1070_ = lean_nat_sub(v___x_1069_, v___x_1068_);
v___x_1071_ = lean_nat_sub(v___x_1070_, v___x_1068_);
lean_dec(v___x_1070_);
v_c_1072_ = l_Lean_Expr_getRevArg_x21(v_e_1058_, v___x_1071_);
v___x_1073_ = lean_unsigned_to_nat(2u);
v___x_1074_ = lean_nat_sub(v___x_1069_, v___x_1073_);
lean_dec(v___x_1069_);
v___x_1075_ = lean_nat_sub(v___x_1074_, v___x_1068_);
lean_dec(v___x_1074_);
v_h_1076_ = l_Lean_Expr_getRevArg_x21(v_e_1058_, v___x_1075_);
if (v_useSplitter_1059_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref(v_inst_1066_);
lean_dec_ref(v_inst_1065_);
lean_dec(v_inst_1064_);
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__0));
lean_inc(v_toBind_1063_);
lean_inc(v_onAlt_1062_);
lean_inc_ref(v_resTy_1060_);
v___f_1080_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1), 10, 9);
lean_closure_set(v___f_1080_, 0, v_u_1067_);
lean_closure_set(v___f_1080_, 1, v_resTy_1060_);
lean_closure_set(v___f_1080_, 2, v_c_1072_);
lean_closure_set(v___f_1080_, 3, v_h_1076_);
lean_closure_set(v___f_1080_, 4, v_toPure_1061_);
lean_closure_set(v___f_1080_, 5, v_onAlt_1062_);
lean_closure_set(v___f_1080_, 6, v___x_1068_);
lean_closure_set(v___f_1080_, 7, v___x_1079_);
lean_closure_set(v___f_1080_, 8, v_toBind_1063_);
v___x_1081_ = lean_apply_4(v_onAlt_1062_, v___x_1077_, v_resTy_1060_, v___x_1078_, v___x_1079_);
v___x_1082_ = lean_apply_4(v_toBind_1063_, lean_box(0), lean_box(0), v___x_1081_, v___f_1080_);
return v___x_1082_;
}
else
{
lean_object* v___x_1083_; lean_object* v___f_1084_; lean_object* v___x_1085_; lean_object* v___f_1086_; lean_object* v___f_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___x_1083_ = lean_box(v_useSplitter_1059_);
lean_inc_n(v_toBind_1063_, 3);
lean_inc_ref_n(v_resTy_1060_, 2);
lean_inc(v_onAlt_1062_);
lean_inc_n(v_inst_1064_, 2);
v___f_1084_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_1084_, 0, v___x_1068_);
lean_closure_set(v___f_1084_, 1, v___x_1083_);
lean_closure_set(v___f_1084_, 2, v_inst_1064_);
lean_closure_set(v___f_1084_, 3, v_onAlt_1062_);
lean_closure_set(v___f_1084_, 4, v_resTy_1060_);
lean_closure_set(v___f_1084_, 5, v_toBind_1063_);
v___x_1085_ = lean_box(v_useSplitter_1059_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__5___boxed), 7, 6);
lean_closure_set(v___f_1086_, 0, v___x_1068_);
lean_closure_set(v___f_1086_, 1, v___x_1085_);
lean_closure_set(v___f_1086_, 2, v_inst_1064_);
lean_closure_set(v___f_1086_, 3, v_onAlt_1062_);
lean_closure_set(v___f_1086_, 4, v_resTy_1060_);
lean_closure_set(v___f_1086_, 5, v_toBind_1063_);
v___f_1087_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1087_, 0, v_u_1067_);
lean_closure_set(v___f_1087_, 1, v_resTy_1060_);
lean_closure_set(v___f_1087_, 2, v_c_1072_);
lean_closure_set(v___f_1087_, 3, v_h_1076_);
lean_closure_set(v___f_1087_, 4, v_toPure_1061_);
lean_closure_set(v___f_1087_, 5, v_inst_1065_);
lean_closure_set(v___f_1087_, 6, v_inst_1066_);
lean_closure_set(v___f_1087_, 7, v___f_1086_);
lean_closure_set(v___f_1087_, 8, v_toBind_1063_);
lean_closure_set(v___f_1087_, 9, v___f_1084_);
v___f_1088_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1089_ = lean_apply_2(v_inst_1064_, lean_box(0), v___f_1088_);
v___x_1090_ = lean_apply_4(v_toBind_1063_, lean_box(0), lean_box(0), v___x_1089_, v___f_1087_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed(lean_object* v_e_1091_, lean_object* v_useSplitter_1092_, lean_object* v_resTy_1093_, lean_object* v_toPure_1094_, lean_object* v_onAlt_1095_, lean_object* v_toBind_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_u_1100_){
_start:
{
uint8_t v_useSplitter_boxed_1101_; lean_object* v_res_1102_; 
v_useSplitter_boxed_1101_ = lean_unbox(v_useSplitter_1092_);
v_res_1102_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9(v_e_1091_, v_useSplitter_boxed_1101_, v_resTy_1093_, v_toPure_1094_, v_onAlt_1095_, v_toBind_1096_, v_inst_1097_, v_inst_1098_, v_inst_1099_, v_u_1100_);
lean_dec_ref(v_e_1091_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10(lean_object* v___x_1103_, lean_object* v_inst_1104_, lean_object* v_____do__lift_1105_){
_start:
{
uint8_t v___x_1106_; uint8_t v___x_1107_; uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1106_ = 0;
v___x_1107_ = 1;
v___x_1108_ = 1;
v___x_1109_ = lean_box(v___x_1106_);
v___x_1110_ = lean_box(v___x_1107_);
v___x_1111_ = lean_box(v___x_1106_);
v___x_1112_ = lean_box(v___x_1107_);
v___x_1113_ = lean_box(v___x_1108_);
v___x_1114_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_1114_, 0, v___x_1103_);
lean_closure_set(v___x_1114_, 1, v_____do__lift_1105_);
lean_closure_set(v___x_1114_, 2, v___x_1109_);
lean_closure_set(v___x_1114_, 3, v___x_1110_);
lean_closure_set(v___x_1114_, 4, v___x_1111_);
lean_closure_set(v___x_1114_, 5, v___x_1112_);
lean_closure_set(v___x_1114_, 6, v___x_1113_);
v___x_1115_ = lean_apply_2(v_inst_1104_, lean_box(0), v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11(lean_object* v_inst_1116_, lean_object* v_onAlt_1117_, lean_object* v_resTy_1118_, lean_object* v_toBind_1119_, lean_object* v_h_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1121_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__3___closed__1));
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_unsigned_to_nat(1u);
v___x_1124_ = lean_mk_empty_array_with_capacity(v___x_1123_);
v___x_1125_ = lean_array_push(v___x_1124_, v_h_1120_);
lean_inc_ref_n(v___x_1125_, 2);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1126_, 0, v___x_1125_);
lean_closure_set(v___f_1126_, 1, v_inst_1116_);
v___x_1127_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_1128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1125_);
lean_ctor_set(v___x_1128_, 1, v___x_1125_);
lean_ctor_set(v___x_1128_, 2, v___x_1127_);
lean_ctor_set(v___x_1128_, 3, v___x_1127_);
lean_ctor_set(v___x_1128_, 4, v___x_1127_);
v___x_1129_ = lean_apply_4(v_onAlt_1117_, v___x_1121_, v_resTy_1118_, v___x_1122_, v___x_1128_);
v___x_1130_ = lean_apply_4(v_toBind_1119_, lean_box(0), lean_box(0), v___x_1129_, v___f_1126_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13(lean_object* v___x_1131_, lean_object* v_inst_1132_, lean_object* v_onAlt_1133_, lean_object* v_resTy_1134_, lean_object* v_toBind_1135_, lean_object* v_h_1136_){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1137_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__1___closed__1));
v___x_1138_ = lean_mk_empty_array_with_capacity(v___x_1131_);
v___x_1139_ = lean_array_push(v___x_1138_, v_h_1136_);
lean_inc_ref_n(v___x_1139_, 2);
v___f_1140_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__10), 3, 2);
lean_closure_set(v___f_1140_, 0, v___x_1139_);
lean_closure_set(v___f_1140_, 1, v_inst_1132_);
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__20___closed__0));
v___x_1142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1139_);
lean_ctor_set(v___x_1142_, 1, v___x_1139_);
lean_ctor_set(v___x_1142_, 2, v___x_1141_);
lean_ctor_set(v___x_1142_, 3, v___x_1141_);
lean_ctor_set(v___x_1142_, 4, v___x_1141_);
v___x_1143_ = lean_apply_4(v_onAlt_1133_, v___x_1137_, v_resTy_1134_, v___x_1131_, v___x_1142_);
v___x_1144_ = lean_apply_4(v_toBind_1135_, lean_box(0), lean_box(0), v___x_1143_, v___f_1140_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(lean_object* v_inst_1145_, lean_object* v_onAlt_1146_, lean_object* v_resTy_1147_, lean_object* v_toBind_1148_, lean_object* v_e_1149_, lean_object* v_toPure_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v___f_1153_, lean_object* v_u_1154_){
_start:
{
lean_object* v___x_1155_; lean_object* v___f_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_c_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v_h_1164_; lean_object* v___f_1165_; lean_object* v___f_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1155_ = lean_unsigned_to_nat(1u);
lean_inc_n(v_toBind_1148_, 2);
lean_inc_ref(v_resTy_1147_);
lean_inc(v_inst_1145_);
v___f_1156_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__13), 6, 5);
lean_closure_set(v___f_1156_, 0, v___x_1155_);
lean_closure_set(v___f_1156_, 1, v_inst_1145_);
lean_closure_set(v___f_1156_, 2, v_onAlt_1146_);
lean_closure_set(v___f_1156_, 3, v_resTy_1147_);
lean_closure_set(v___f_1156_, 4, v_toBind_1148_);
v___x_1157_ = l_Lean_Expr_getAppNumArgs(v_e_1149_);
v___x_1158_ = lean_nat_sub(v___x_1157_, v___x_1155_);
v___x_1159_ = lean_nat_sub(v___x_1158_, v___x_1155_);
lean_dec(v___x_1158_);
v_c_1160_ = l_Lean_Expr_getRevArg_x21(v_e_1149_, v___x_1159_);
v___x_1161_ = lean_unsigned_to_nat(2u);
v___x_1162_ = lean_nat_sub(v___x_1157_, v___x_1161_);
lean_dec(v___x_1157_);
v___x_1163_ = lean_nat_sub(v___x_1162_, v___x_1155_);
lean_dec(v___x_1162_);
v_h_1164_ = l_Lean_Expr_getRevArg_x21(v_e_1149_, v___x_1163_);
v___f_1165_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__7), 11, 10);
lean_closure_set(v___f_1165_, 0, v_u_1154_);
lean_closure_set(v___f_1165_, 1, v_resTy_1147_);
lean_closure_set(v___f_1165_, 2, v_c_1160_);
lean_closure_set(v___f_1165_, 3, v_h_1164_);
lean_closure_set(v___f_1165_, 4, v_toPure_1150_);
lean_closure_set(v___f_1165_, 5, v_inst_1151_);
lean_closure_set(v___f_1165_, 6, v_inst_1152_);
lean_closure_set(v___f_1165_, 7, v___f_1156_);
lean_closure_set(v___f_1165_, 8, v_toBind_1148_);
lean_closure_set(v___f_1165_, 9, v___f_1153_);
v___f_1166_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__3));
v___x_1167_ = lean_apply_2(v_inst_1145_, lean_box(0), v___f_1166_);
v___x_1168_ = lean_apply_4(v_toBind_1148_, lean_box(0), lean_box(0), v___x_1167_, v___f_1165_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed(lean_object* v_inst_1169_, lean_object* v_onAlt_1170_, lean_object* v_resTy_1171_, lean_object* v_toBind_1172_, lean_object* v_e_1173_, lean_object* v_toPure_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v___f_1177_, lean_object* v_u_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17(v_inst_1169_, v_onAlt_1170_, v_resTy_1171_, v_toBind_1172_, v_e_1173_, v_toPure_1174_, v_inst_1175_, v_inst_1176_, v___f_1177_, v_u_1178_);
lean_dec_ref(v_e_1173_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(lean_object* v_onAlt_1180_, lean_object* v_idx_1181_, lean_object* v_expAltType_1182_, lean_object* v_altFVars_1183_, lean_object* v___alt_1184_){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1185_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___closed__2));
v___x_1186_ = lean_unsigned_to_nat(1u);
v___x_1187_ = lean_nat_add(v_idx_1181_, v___x_1186_);
v___x_1188_ = lean_name_append_index_after(v___x_1185_, v___x_1187_);
v___x_1189_ = lean_apply_4(v_onAlt_1180_, v___x_1188_, v_expAltType_1182_, v_idx_1181_, v_altFVars_1183_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed(lean_object* v_onAlt_1190_, lean_object* v_idx_1191_, lean_object* v_expAltType_1192_, lean_object* v_altFVars_1193_, lean_object* v___alt_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12(v_onAlt_1190_, v_idx_1191_, v_expAltType_1192_, v_altFVars_1193_, v___alt_1194_);
lean_dec_ref(v___alt_1194_);
return v_res_1195_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(lean_object* v_toMatcherInfo_1196_, lean_object* v_i_1197_, lean_object* v_a_1198_, lean_object* v_x_1199_){
_start:
{
uint8_t v___x_1200_; 
v___x_1200_ = l_Lean_Expr_isFVar(v_a_1198_);
if (v___x_1200_ == 0)
{
return v___x_1200_;
}
else
{
lean_object* v_discrInfos_1201_; lean_object* v___x_1202_; uint8_t v___x_1203_; 
v_discrInfos_1201_ = lean_ctor_get(v_toMatcherInfo_1196_, 4);
v___x_1202_ = lean_array_get_size(v_discrInfos_1201_);
v___x_1203_ = lean_nat_dec_lt(v_i_1197_, v___x_1202_);
if (v___x_1203_ == 0)
{
return v___x_1200_;
}
else
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_array_fget_borrowed(v_discrInfos_1201_, v_i_1197_);
if (lean_obj_tag(v___x_1204_) == 0)
{
return v___x_1200_;
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = 0;
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed(lean_object* v_toMatcherInfo_1206_, lean_object* v_i_1207_, lean_object* v_a_1208_, lean_object* v_x_1209_){
_start:
{
uint8_t v_res_1210_; lean_object* v_r_1211_; 
v_res_1210_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14(v_toMatcherInfo_1206_, v_i_1207_, v_a_1208_, v_x_1209_);
lean_dec_ref(v_a_1208_);
lean_dec(v_i_1207_);
lean_dec_ref(v_toMatcherInfo_1206_);
v_r_1211_ = lean_box(v_res_1210_);
return v_r_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(lean_object* v_mask_1212_, lean_object* v_absMotiveBody_1213_, lean_object* v_toPure_1214_, lean_object* v_xs_1215_, lean_object* v___body_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = l_Lean_Array_mask___redArg(v_mask_1212_, v_xs_1215_);
v___x_1218_ = lean_expr_instantiate_rev(v_absMotiveBody_1213_, v___x_1217_);
lean_dec(v___x_1217_);
v___x_1219_ = lean_apply_2(v_toPure_1214_, lean_box(0), v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed(lean_object* v_mask_1220_, lean_object* v_absMotiveBody_1221_, lean_object* v_toPure_1222_, lean_object* v_xs_1223_, lean_object* v___body_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15(v_mask_1220_, v_absMotiveBody_1221_, v_toPure_1222_, v_xs_1223_, v___body_1224_);
lean_dec_ref(v___body_1224_);
lean_dec_ref(v_absMotiveBody_1221_);
lean_dec_ref(v_mask_1220_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16(lean_object* v_toFunctor_1226_, lean_object* v_mask_1227_, lean_object* v_toPure_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_inst_1233_, lean_object* v_matcherApp_1234_, uint8_t v_useSplitter_1235_, lean_object* v___f_1236_, lean_object* v___f_1237_, lean_object* v_absMotiveBody_1238_){
_start:
{
lean_object* v_map_1239_; lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v_map_1239_ = lean_ctor_get(v_toFunctor_1226_, 0);
lean_inc(v_map_1239_);
lean_dec_ref(v_toFunctor_1226_);
lean_inc(v_toPure_1228_);
v___f_1240_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__15___boxed), 5, 3);
lean_closure_set(v___f_1240_, 0, v_mask_1227_);
lean_closure_set(v___f_1240_, 1, v_absMotiveBody_1238_);
lean_closure_set(v___f_1240_, 2, v_toPure_1228_);
v___x_1241_ = lean_apply_1(v_toPure_1228_, lean_box(0));
lean_inc(v___x_1241_);
v___x_1242_ = l_Lean_Meta_MatcherApp_transform___redArg(v_inst_1229_, v_inst_1230_, v_inst_1231_, v_inst_1232_, v_inst_1233_, v_matcherApp_1234_, v_useSplitter_1235_, v_useSplitter_1235_, v___x_1241_, v___f_1240_, v___f_1236_, v___x_1241_);
v___x_1243_ = lean_apply_4(v_map_1239_, lean_box(0), lean_box(0), v___f_1237_, v___x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16___boxed(lean_object* v_toFunctor_1244_, lean_object* v_mask_1245_, lean_object* v_toPure_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_inst_1250_, lean_object* v_inst_1251_, lean_object* v_matcherApp_1252_, lean_object* v_useSplitter_1253_, lean_object* v___f_1254_, lean_object* v___f_1255_, lean_object* v_absMotiveBody_1256_){
_start:
{
uint8_t v_useSplitter_boxed_1257_; lean_object* v_res_1258_; 
v_useSplitter_boxed_1257_ = lean_unbox(v_useSplitter_1253_);
v_res_1258_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16(v_toFunctor_1244_, v_mask_1245_, v_toPure_1246_, v_inst_1247_, v_inst_1248_, v_inst_1249_, v_inst_1250_, v_inst_1251_, v_matcherApp_1252_, v_useSplitter_boxed_1257_, v___f_1254_, v___f_1255_, v_absMotiveBody_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_inst_1263_, lean_object* v_inst_1264_, lean_object* v_info_1265_, lean_object* v_resTy_1266_, lean_object* v_onAlt_1267_, uint8_t v_useSplitter_1268_){
_start:
{
switch(lean_obj_tag(v_info_1265_))
{
case 0:
{
lean_object* v_toApplicative_1269_; lean_object* v_toBind_1270_; lean_object* v_toPure_1271_; lean_object* v_e_1272_; lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_toApplicative_1269_ = lean_ctor_get(v_inst_1262_, 0);
lean_dec_ref(v_inst_1264_);
lean_dec_ref(v_inst_1263_);
v_toBind_1270_ = lean_ctor_get(v_inst_1262_, 1);
lean_inc_n(v_toBind_1270_, 2);
v_toPure_1271_ = lean_ctor_get(v_toApplicative_1269_, 1);
lean_inc(v_toPure_1271_);
v_e_1272_ = lean_ctor_get(v_info_1265_, 0);
lean_inc_ref(v_e_1272_);
lean_dec_ref_known(v_info_1265_, 1);
v___x_1273_ = lean_box(v_useSplitter_1268_);
lean_inc(v_inst_1260_);
lean_inc_ref(v_resTy_1266_);
v___f_1274_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__9___boxed), 10, 9);
lean_closure_set(v___f_1274_, 0, v_e_1272_);
lean_closure_set(v___f_1274_, 1, v___x_1273_);
lean_closure_set(v___f_1274_, 2, v_resTy_1266_);
lean_closure_set(v___f_1274_, 3, v_toPure_1271_);
lean_closure_set(v___f_1274_, 4, v_onAlt_1267_);
lean_closure_set(v___f_1274_, 5, v_toBind_1270_);
lean_closure_set(v___f_1274_, 6, v_inst_1260_);
lean_closure_set(v___f_1274_, 7, v_inst_1261_);
lean_closure_set(v___f_1274_, 8, v_inst_1262_);
v___x_1275_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1275_, 0, v_resTy_1266_);
v___x_1276_ = lean_apply_2(v_inst_1260_, lean_box(0), v___x_1275_);
v___x_1277_ = lean_apply_4(v_toBind_1270_, lean_box(0), lean_box(0), v___x_1276_, v___f_1274_);
return v___x_1277_;
}
case 1:
{
lean_object* v_toApplicative_1278_; lean_object* v_toBind_1279_; lean_object* v_toPure_1280_; lean_object* v_e_1281_; lean_object* v___f_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_toApplicative_1278_ = lean_ctor_get(v_inst_1262_, 0);
lean_dec_ref(v_inst_1264_);
lean_dec_ref(v_inst_1263_);
v_toBind_1279_ = lean_ctor_get(v_inst_1262_, 1);
lean_inc_n(v_toBind_1279_, 3);
v_toPure_1280_ = lean_ctor_get(v_toApplicative_1278_, 1);
lean_inc(v_toPure_1280_);
v_e_1281_ = lean_ctor_get(v_info_1265_, 0);
lean_inc_ref(v_e_1281_);
lean_dec_ref_known(v_info_1265_, 1);
lean_inc_ref_n(v_resTy_1266_, 2);
lean_inc(v_onAlt_1267_);
lean_inc_n(v_inst_1260_, 2);
v___f_1282_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__11), 5, 4);
lean_closure_set(v___f_1282_, 0, v_inst_1260_);
lean_closure_set(v___f_1282_, 1, v_onAlt_1267_);
lean_closure_set(v___f_1282_, 2, v_resTy_1266_);
lean_closure_set(v___f_1282_, 3, v_toBind_1279_);
v___f_1283_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__17___boxed), 10, 9);
lean_closure_set(v___f_1283_, 0, v_inst_1260_);
lean_closure_set(v___f_1283_, 1, v_onAlt_1267_);
lean_closure_set(v___f_1283_, 2, v_resTy_1266_);
lean_closure_set(v___f_1283_, 3, v_toBind_1279_);
lean_closure_set(v___f_1283_, 4, v_e_1281_);
lean_closure_set(v___f_1283_, 5, v_toPure_1280_);
lean_closure_set(v___f_1283_, 6, v_inst_1261_);
lean_closure_set(v___f_1283_, 7, v_inst_1262_);
lean_closure_set(v___f_1283_, 8, v___f_1282_);
v___x_1284_ = lean_alloc_closure((void*)(l_Lean_Meta_getLevel___boxed), 6, 1);
lean_closure_set(v___x_1284_, 0, v_resTy_1266_);
v___x_1285_ = lean_apply_2(v_inst_1260_, lean_box(0), v___x_1284_);
v___x_1286_ = lean_apply_4(v_toBind_1279_, lean_box(0), lean_box(0), v___x_1285_, v___f_1283_);
return v___x_1286_;
}
default: 
{
lean_object* v_toApplicative_1287_; lean_object* v_matcherApp_1288_; lean_object* v_toBind_1289_; lean_object* v_toFunctor_1290_; lean_object* v_toPure_1291_; lean_object* v_toMatcherInfo_1292_; lean_object* v_discrs_1293_; lean_object* v___f_1294_; lean_object* v___f_1295_; lean_object* v___f_1296_; lean_object* v___x_1297_; size_t v_sz_1298_; size_t v___x_1299_; lean_object* v_mask_1300_; lean_object* v___x_1301_; lean_object* v___f_1302_; lean_object* v_maskedDiscrs_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_toApplicative_1287_ = lean_ctor_get(v_inst_1262_, 0);
v_matcherApp_1288_ = lean_ctor_get(v_info_1265_, 0);
lean_inc_ref(v_matcherApp_1288_);
lean_dec_ref_known(v_info_1265_, 1);
v_toBind_1289_ = lean_ctor_get(v_inst_1262_, 1);
lean_inc(v_toBind_1289_);
v_toFunctor_1290_ = lean_ctor_get(v_toApplicative_1287_, 0);
lean_inc_ref(v_toFunctor_1290_);
v_toPure_1291_ = lean_ctor_get(v_toApplicative_1287_, 1);
lean_inc(v_toPure_1291_);
v_toMatcherInfo_1292_ = lean_ctor_get(v_matcherApp_1288_, 0);
v_discrs_1293_ = lean_ctor_get(v_matcherApp_1288_, 5);
lean_inc_ref_n(v_discrs_1293_, 2);
v___f_1294_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___closed__0));
v___f_1295_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__12___boxed), 5, 1);
lean_closure_set(v___f_1295_, 0, v_onAlt_1267_);
lean_inc_ref(v_toMatcherInfo_1292_);
v___f_1296_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__14___boxed), 4, 1);
lean_closure_set(v___f_1296_, 0, v_toMatcherInfo_1292_);
v___x_1297_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__22___closed__9));
v_sz_1298_ = lean_array_size(v_discrs_1293_);
v___x_1299_ = ((size_t)0ULL);
v_mask_1300_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map(lean_box(0), lean_box(0), lean_box(0), v___x_1297_, v_discrs_1293_, v___f_1296_, v_sz_1298_, v___x_1299_, v_discrs_1293_);
v___x_1301_ = lean_box(v_useSplitter_1268_);
lean_inc(v_inst_1260_);
lean_inc(v_mask_1300_);
v___f_1302_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___lam__16___boxed), 13, 12);
lean_closure_set(v___f_1302_, 0, v_toFunctor_1290_);
lean_closure_set(v___f_1302_, 1, v_mask_1300_);
lean_closure_set(v___f_1302_, 2, v_toPure_1291_);
lean_closure_set(v___f_1302_, 3, v_inst_1260_);
lean_closure_set(v___f_1302_, 4, v_inst_1261_);
lean_closure_set(v___f_1302_, 5, v_inst_1262_);
lean_closure_set(v___f_1302_, 6, v_inst_1263_);
lean_closure_set(v___f_1302_, 7, v_inst_1264_);
lean_closure_set(v___f_1302_, 8, v_matcherApp_1288_);
lean_closure_set(v___f_1302_, 9, v___x_1301_);
lean_closure_set(v___f_1302_, 10, v___f_1295_);
lean_closure_set(v___f_1302_, 11, v___f_1294_);
v_maskedDiscrs_1303_ = l_Lean_Array_mask___redArg(v_mask_1300_, v_discrs_1293_);
lean_dec(v_mask_1300_);
v___x_1304_ = lean_alloc_closure((void*)(l_Lean_Expr_abstractM___boxed), 7, 2);
lean_closure_set(v___x_1304_, 0, v_resTy_1266_);
lean_closure_set(v___x_1304_, 1, v_maskedDiscrs_1303_);
v___x_1305_ = lean_apply_2(v_inst_1260_, lean_box(0), v___x_1304_);
v___x_1306_ = lean_apply_4(v_toBind_1289_, lean_box(0), lean_box(0), v___x_1305_, v___f_1302_);
return v___x_1306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg___boxed(lean_object* v_inst_1307_, lean_object* v_inst_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_info_1312_, lean_object* v_resTy_1313_, lean_object* v_onAlt_1314_, lean_object* v_useSplitter_1315_){
_start:
{
uint8_t v_useSplitter_boxed_1316_; lean_object* v_res_1317_; 
v_useSplitter_boxed_1316_ = lean_unbox(v_useSplitter_1315_);
v_res_1317_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1307_, v_inst_1308_, v_inst_1309_, v_inst_1310_, v_inst_1311_, v_info_1312_, v_resTy_1313_, v_onAlt_1314_, v_useSplitter_boxed_1316_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(lean_object* v_n_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_info_1327_, lean_object* v_resTy_1328_, lean_object* v_onAlt_1329_, uint8_t v_useSplitter_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___redArg(v_inst_1319_, v_inst_1320_, v_inst_1321_, v_inst_1322_, v_inst_1323_, v_info_1327_, v_resTy_1328_, v_onAlt_1329_, v_useSplitter_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_splitWith___boxed(lean_object* v_n_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_inst_1339_, lean_object* v_inst_1340_, lean_object* v_info_1341_, lean_object* v_resTy_1342_, lean_object* v_onAlt_1343_, lean_object* v_useSplitter_1344_){
_start:
{
uint8_t v_useSplitter_boxed_1345_; lean_object* v_res_1346_; 
v_useSplitter_boxed_1345_ = lean_unbox(v_useSplitter_1344_);
v_res_1346_ = l_Lean_Elab_Tactic_Do_SplitInfo_splitWith(v_n_1332_, v_inst_1333_, v_inst_1334_, v_inst_1335_, v_inst_1336_, v_inst_1337_, v_inst_1338_, v_inst_1339_, v_inst_1340_, v_info_1341_, v_resTy_1342_, v_onAlt_1343_, v_useSplitter_boxed_1345_);
lean_dec(v_inst_1340_);
lean_dec(v_inst_1339_);
lean_dec_ref(v_inst_1338_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(lean_object* v_info_1347_, lean_object* v_e_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_){
_start:
{
if (lean_obj_tag(v_info_1347_) == 2)
{
lean_object* v_matcherApp_1357_; lean_object* v_toMatcherInfo_1358_; lean_object* v___x_1359_; 
v_matcherApp_1357_ = lean_ctor_get(v_info_1347_, 0);
lean_inc_ref(v_matcherApp_1357_);
lean_dec_ref_known(v_info_1347_, 1);
v_toMatcherInfo_1358_ = lean_ctor_get(v_matcherApp_1357_, 0);
lean_inc_ref(v_toMatcherInfo_1358_);
lean_dec_ref(v_matcherApp_1357_);
v___x_1359_ = l_Lean_Meta_Simp_simpMatchDiscrs_x3f(v_toMatcherInfo_1358_, v_e_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec_ref(v_e_1348_);
lean_dec_ref(v_info_1347_);
v___x_1360_ = lean_box(0);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f___boxed(lean_object* v_info_1362_, lean_object* v_e_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_Elab_Tactic_Do_SplitInfo_simpDiscrs_x3f(v_info_1362_, v_e_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(lean_object* v_declName_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v_env_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1376_ = lean_st_ref_get(v___y_1374_);
v_env_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc_ref(v_env_1377_);
lean_dec(v___x_1376_);
v___x_1378_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_1377_, v_declName_1373_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg___boxed(lean_object* v_declName_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1380_, v___y_1381_);
lean_dec(v___y_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(lean_object* v_msgData_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v___x_1390_; lean_object* v_env_1391_; lean_object* v___x_1392_; lean_object* v_mctx_1393_; lean_object* v_lctx_1394_; lean_object* v_options_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1390_ = lean_st_ref_get(v___y_1388_);
v_env_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc_ref(v_env_1391_);
lean_dec(v___x_1390_);
v___x_1392_ = lean_st_ref_get(v___y_1386_);
v_mctx_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc_ref(v_mctx_1393_);
lean_dec(v___x_1392_);
v_lctx_1394_ = lean_ctor_get(v___y_1385_, 2);
v_options_1395_ = lean_ctor_get(v___y_1387_, 2);
lean_inc_ref(v_options_1395_);
lean_inc_ref(v_lctx_1394_);
v___x_1396_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1396_, 0, v_env_1391_);
lean_ctor_set(v___x_1396_, 1, v_mctx_1393_);
lean_ctor_set(v___x_1396_, 2, v_lctx_1394_);
lean_ctor_set(v___x_1396_, 3, v_options_1395_);
v___x_1397_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
lean_ctor_set(v___x_1397_, 1, v_msgData_1384_);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11___boxed(lean_object* v_msgData_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msgData_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(lean_object* v_msg_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_ref_1412_; lean_object* v___x_1413_; lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1422_; 
v_ref_1412_ = lean_ctor_get(v___y_1409_, 5);
v___x_1413_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10_spec__11(v_msg_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1422_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1418_; lean_object* v___x_1420_; 
lean_inc(v_ref_1412_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v_ref_1412_);
lean_ctor_set(v___x_1418_, 1, v_a_1414_);
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 1);
lean_ctor_set(v___x_1416_, 0, v___x_1418_);
v___x_1420_ = v___x_1416_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1418_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg___boxed(lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(lean_object* v_ref_1430_, lean_object* v_msg_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_fileName_1437_; lean_object* v_fileMap_1438_; lean_object* v_options_1439_; lean_object* v_currRecDepth_1440_; lean_object* v_maxRecDepth_1441_; lean_object* v_ref_1442_; lean_object* v_currNamespace_1443_; lean_object* v_openDecls_1444_; lean_object* v_initHeartbeats_1445_; lean_object* v_maxHeartbeats_1446_; lean_object* v_quotContext_1447_; lean_object* v_currMacroScope_1448_; uint8_t v_diag_1449_; lean_object* v_cancelTk_x3f_1450_; uint8_t v_suppressElabErrors_1451_; lean_object* v_inheritedTraceOptions_1452_; lean_object* v_ref_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v_fileName_1437_ = lean_ctor_get(v___y_1434_, 0);
v_fileMap_1438_ = lean_ctor_get(v___y_1434_, 1);
v_options_1439_ = lean_ctor_get(v___y_1434_, 2);
v_currRecDepth_1440_ = lean_ctor_get(v___y_1434_, 3);
v_maxRecDepth_1441_ = lean_ctor_get(v___y_1434_, 4);
v_ref_1442_ = lean_ctor_get(v___y_1434_, 5);
v_currNamespace_1443_ = lean_ctor_get(v___y_1434_, 6);
v_openDecls_1444_ = lean_ctor_get(v___y_1434_, 7);
v_initHeartbeats_1445_ = lean_ctor_get(v___y_1434_, 8);
v_maxHeartbeats_1446_ = lean_ctor_get(v___y_1434_, 9);
v_quotContext_1447_ = lean_ctor_get(v___y_1434_, 10);
v_currMacroScope_1448_ = lean_ctor_get(v___y_1434_, 11);
v_diag_1449_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*14);
v_cancelTk_x3f_1450_ = lean_ctor_get(v___y_1434_, 12);
v_suppressElabErrors_1451_ = lean_ctor_get_uint8(v___y_1434_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1452_ = lean_ctor_get(v___y_1434_, 13);
v_ref_1453_ = l_Lean_replaceRef(v_ref_1430_, v_ref_1442_);
lean_inc_ref(v_inheritedTraceOptions_1452_);
lean_inc(v_cancelTk_x3f_1450_);
lean_inc(v_currMacroScope_1448_);
lean_inc(v_quotContext_1447_);
lean_inc(v_maxHeartbeats_1446_);
lean_inc(v_initHeartbeats_1445_);
lean_inc(v_openDecls_1444_);
lean_inc(v_currNamespace_1443_);
lean_inc(v_maxRecDepth_1441_);
lean_inc(v_currRecDepth_1440_);
lean_inc_ref(v_options_1439_);
lean_inc_ref(v_fileMap_1438_);
lean_inc_ref(v_fileName_1437_);
v___x_1454_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1454_, 0, v_fileName_1437_);
lean_ctor_set(v___x_1454_, 1, v_fileMap_1438_);
lean_ctor_set(v___x_1454_, 2, v_options_1439_);
lean_ctor_set(v___x_1454_, 3, v_currRecDepth_1440_);
lean_ctor_set(v___x_1454_, 4, v_maxRecDepth_1441_);
lean_ctor_set(v___x_1454_, 5, v_ref_1453_);
lean_ctor_set(v___x_1454_, 6, v_currNamespace_1443_);
lean_ctor_set(v___x_1454_, 7, v_openDecls_1444_);
lean_ctor_set(v___x_1454_, 8, v_initHeartbeats_1445_);
lean_ctor_set(v___x_1454_, 9, v_maxHeartbeats_1446_);
lean_ctor_set(v___x_1454_, 10, v_quotContext_1447_);
lean_ctor_set(v___x_1454_, 11, v_currMacroScope_1448_);
lean_ctor_set(v___x_1454_, 12, v_cancelTk_x3f_1450_);
lean_ctor_set(v___x_1454_, 13, v_inheritedTraceOptions_1452_);
lean_ctor_set_uint8(v___x_1454_, sizeof(void*)*14, v_diag_1449_);
lean_ctor_set_uint8(v___x_1454_, sizeof(void*)*14 + 1, v_suppressElabErrors_1451_);
v___x_1455_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_1431_, v___y_1432_, v___y_1433_, v___x_1454_, v___y_1435_);
lean_dec_ref_known(v___x_1454_, 14);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg___boxed(lean_object* v_ref_1456_, lean_object* v_msg_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1456_, v_msg_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v_ref_1456_);
return v_res_1463_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1464_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__0);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1468_ = lean_unsigned_to_nat(0u);
v___x_1469_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
lean_ctor_set(v___x_1469_, 2, v___x_1468_);
lean_ctor_set(v___x_1469_, 3, v___x_1468_);
lean_ctor_set(v___x_1469_, 4, v___x_1467_);
lean_ctor_set(v___x_1469_, 5, v___x_1467_);
lean_ctor_set(v___x_1469_, 6, v___x_1467_);
lean_ctor_set(v___x_1469_, 7, v___x_1467_);
lean_ctor_set(v___x_1469_, 8, v___x_1467_);
lean_ctor_set(v___x_1469_, 9, v___x_1467_);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = lean_unsigned_to_nat(32u);
v___x_1471_ = lean_mk_empty_array_with_capacity(v___x_1470_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4(void){
_start:
{
size_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1473_ = ((size_t)5ULL);
v___x_1474_ = lean_unsigned_to_nat(0u);
v___x_1475_ = lean_unsigned_to_nat(32u);
v___x_1476_ = lean_mk_empty_array_with_capacity(v___x_1475_);
v___x_1477_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__3);
v___x_1478_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
lean_ctor_set(v___x_1478_, 1, v___x_1476_);
lean_ctor_set(v___x_1478_, 2, v___x_1474_);
lean_ctor_set(v___x_1478_, 3, v___x_1474_);
lean_ctor_set_usize(v___x_1478_, 4, v___x_1473_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5(void){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1479_ = lean_box(1);
v___x_1480_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__4);
v___x_1481_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__1);
v___x_1482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v___x_1480_);
lean_ctor_set(v___x_1482_, 2, v___x_1479_);
return v___x_1482_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7(void){
_start:
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1484_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__6));
v___x_1485_ = l_Lean_stringToMessageData(v___x_1484_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1487_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__8));
v___x_1488_ = l_Lean_stringToMessageData(v___x_1487_);
return v___x_1488_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__10));
v___x_1491_ = l_Lean_stringToMessageData(v___x_1490_);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13(void){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__12));
v___x_1494_ = l_Lean_stringToMessageData(v___x_1493_);
return v___x_1494_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15(void){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__14));
v___x_1497_ = l_Lean_stringToMessageData(v___x_1496_);
return v___x_1497_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17(void){
_start:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1499_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__16));
v___x_1500_ = l_Lean_stringToMessageData(v___x_1499_);
return v___x_1500_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__18));
v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_msg_1504_, lean_object* v_declHint_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v_env_1509_; uint8_t v___x_1510_; 
v___x_1508_ = lean_st_ref_get(v___y_1506_);
v_env_1509_ = lean_ctor_get(v___x_1508_, 0);
lean_inc_ref(v_env_1509_);
lean_dec(v___x_1508_);
v___x_1510_ = l_Lean_Name_isAnonymous(v_declHint_1505_);
if (v___x_1510_ == 0)
{
uint8_t v_isExporting_1511_; 
v_isExporting_1511_ = lean_ctor_get_uint8(v_env_1509_, sizeof(void*)*8);
if (v_isExporting_1511_ == 0)
{
lean_object* v___x_1512_; 
lean_dec_ref(v_env_1509_);
lean_dec(v_declHint_1505_);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v_msg_1504_);
return v___x_1512_;
}
else
{
lean_object* v___x_1513_; uint8_t v___x_1514_; 
lean_inc_ref(v_env_1509_);
v___x_1513_ = l_Lean_Environment_setExporting(v_env_1509_, v___x_1510_);
lean_inc(v_declHint_1505_);
lean_inc_ref(v___x_1513_);
v___x_1514_ = l_Lean_Environment_contains(v___x_1513_, v_declHint_1505_, v_isExporting_1511_);
if (v___x_1514_ == 0)
{
lean_object* v___x_1515_; 
lean_dec_ref(v___x_1513_);
lean_dec_ref(v_env_1509_);
lean_dec(v_declHint_1505_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v_msg_1504_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v_c_1521_; lean_object* v___x_1522_; 
v___x_1516_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__2);
v___x_1517_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__5);
v___x_1518_ = l_Lean_Options_empty;
v___x_1519_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1513_);
lean_ctor_set(v___x_1519_, 1, v___x_1516_);
lean_ctor_set(v___x_1519_, 2, v___x_1517_);
lean_ctor_set(v___x_1519_, 3, v___x_1518_);
lean_inc(v_declHint_1505_);
v___x_1520_ = l_Lean_MessageData_ofConstName(v_declHint_1505_, v___x_1510_);
v_c_1521_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1521_, 0, v___x_1519_);
lean_ctor_set(v_c_1521_, 1, v___x_1520_);
v___x_1522_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1509_, v_declHint_1505_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
lean_dec_ref(v_env_1509_);
lean_dec(v_declHint_1505_);
v___x_1523_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v_c_1521_);
v___x_1525_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__9);
v___x_1526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1524_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
v___x_1527_ = l_Lean_MessageData_note(v___x_1526_);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v_msg_1504_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
else
{
lean_object* v_val_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1565_; 
v_val_1530_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1532_ = v___x_1522_;
v_isShared_1533_ = v_isSharedCheck_1565_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_val_1530_);
lean_dec(v___x_1522_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1565_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v_mod_1537_; uint8_t v___x_1538_; 
v___x_1534_ = lean_box(0);
v___x_1535_ = l_Lean_Environment_header(v_env_1509_);
lean_dec_ref(v_env_1509_);
v___x_1536_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1535_);
v_mod_1537_ = lean_array_get(v___x_1534_, v___x_1536_, v_val_1530_);
lean_dec(v_val_1530_);
lean_dec_ref(v___x_1536_);
v___x_1538_ = l_Lean_isPrivateName(v_declHint_1505_);
lean_dec(v_declHint_1505_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
v___x_1539_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__11);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v_c_1521_);
v___x_1541_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__13);
v___x_1542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1540_);
lean_ctor_set(v___x_1542_, 1, v___x_1541_);
v___x_1543_ = l_Lean_MessageData_ofName(v_mod_1537_);
v___x_1544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1544_, 0, v___x_1542_);
lean_ctor_set(v___x_1544_, 1, v___x_1543_);
v___x_1545_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__15);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1544_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = l_Lean_MessageData_note(v___x_1546_);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_msg_1504_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1548_);
v___x_1550_ = v___x_1532_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1552_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__7);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
lean_ctor_set(v___x_1553_, 1, v_c_1521_);
v___x_1554_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__17);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1553_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = l_Lean_MessageData_ofName(v_mod_1537_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___closed__19);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_MessageData_note(v___x_1559_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v_msg_1504_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1561_);
v___x_1563_ = v___x_1532_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1566_; 
lean_dec_ref(v_env_1509_);
lean_dec(v_declHint_1505_);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v_msg_1504_);
return v___x_1566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_msg_1567_, lean_object* v_declHint_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1567_, v_declHint_1568_, v___y_1569_);
lean_dec(v___y_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(lean_object* v_msg_1572_, lean_object* v_declHint_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1589_; 
v___x_1579_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_1572_, v_declHint_1573_, v___y_1577_);
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1579_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1582_ = v___x_1579_;
v_isShared_1583_ = v_isSharedCheck_1589_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1579_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1589_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1584_ = l_Lean_unknownIdentifierMessageTag;
v___x_1585_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v_a_1580_);
if (v_isShared_1583_ == 0)
{
lean_ctor_set(v___x_1582_, 0, v___x_1585_);
v___x_1587_ = v___x_1582_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7___boxed(lean_object* v_msg_1590_, lean_object* v_declHint_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1590_, v_declHint_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(lean_object* v_ref_1598_, lean_object* v_msg_1599_, lean_object* v_declHint_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1606_; lean_object* v_a_1607_; lean_object* v___x_1608_; 
v___x_1606_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7(v_msg_1599_, v_declHint_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
v_a_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_a_1607_);
lean_dec_ref(v___x_1606_);
v___x_1608_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_1598_, v_a_1607_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1609_, lean_object* v_msg_1610_, lean_object* v_declHint_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1609_, v_msg_1610_, v_declHint_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
lean_dec(v___y_1615_);
lean_dec_ref(v___y_1614_);
lean_dec(v___y_1613_);
lean_dec_ref(v___y_1612_);
lean_dec(v_ref_1609_);
return v_res_1617_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__2));
v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_ref_1624_, lean_object* v_constName_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1631_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_1632_ = 0;
lean_inc(v_constName_1625_);
v___x_1633_ = l_Lean_MessageData_ofConstName(v_constName_1625_, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1631_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___closed__3);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1624_, v___x_1636_, v_constName_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_ref_1638_, lean_object* v_constName_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1638_, v_constName_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v_ref_1638_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_constName_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v_ref_1652_; lean_object* v___x_1653_; 
v_ref_1652_ = lean_ctor_get(v___y_1649_, 5);
v___x_1653_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1652_, v_constName_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_constName_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(lean_object* v_constName_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v_env_1668_; uint8_t v___x_1669_; lean_object* v___x_1670_; 
v___x_1667_ = lean_st_ref_get(v___y_1665_);
v_env_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc_ref(v_env_1668_);
lean_dec(v___x_1667_);
v___x_1669_ = 0;
lean_inc(v_constName_1661_);
v___x_1670_ = l_Lean_Environment_find_x3f(v_env_1668_, v_constName_1661_, v___x_1669_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_);
return v___x_1671_;
}
else
{
lean_object* v_val_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_dec(v_constName_1661_);
v_val_1672_ = lean_ctor_get(v___x_1670_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1670_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1670_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_val_1672_);
lean_dec(v___x_1670_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set_tag(v___x_1674_, 0);
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_val_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0___boxed(lean_object* v_constName_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_constName_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(lean_object* v_msg_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v___x_1693_; lean_object* v_toApplicative_1694_; lean_object* v_toFunctor_1695_; lean_object* v_toSeq_1696_; lean_object* v_toSeqLeft_1697_; lean_object* v_toSeqRight_1698_; lean_object* v___f_1699_; lean_object* v___f_1700_; lean_object* v___f_1701_; lean_object* v___f_1702_; lean_object* v___x_1703_; lean_object* v___f_1704_; lean_object* v___f_1705_; lean_object* v___f_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v_toApplicative_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1741_; 
v___x_1693_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1, &l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__1);
v_toApplicative_1694_ = lean_ctor_get(v___x_1693_, 0);
v_toFunctor_1695_ = lean_ctor_get(v_toApplicative_1694_, 0);
v_toSeq_1696_ = lean_ctor_get(v_toApplicative_1694_, 2);
v_toSeqLeft_1697_ = lean_ctor_get(v_toApplicative_1694_, 3);
v_toSeqRight_1698_ = lean_ctor_get(v_toApplicative_1694_, 4);
v___f_1699_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__2));
v___f_1700_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_1695_, 2);
v___f_1701_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1701_, 0, v_toFunctor_1695_);
v___f_1702_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1702_, 0, v_toFunctor_1695_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___f_1701_);
lean_ctor_set(v___x_1703_, 1, v___f_1702_);
lean_inc(v_toSeqRight_1698_);
v___f_1704_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1704_, 0, v_toSeqRight_1698_);
lean_inc(v_toSeqLeft_1697_);
v___f_1705_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1705_, 0, v_toSeqLeft_1697_);
lean_inc(v_toSeq_1696_);
v___f_1706_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1706_, 0, v_toSeq_1696_);
v___x_1707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1703_);
lean_ctor_set(v___x_1707_, 1, v___f_1699_);
lean_ctor_set(v___x_1707_, 2, v___f_1706_);
lean_ctor_set(v___x_1707_, 3, v___f_1705_);
lean_ctor_set(v___x_1707_, 4, v___f_1704_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___f_1700_);
v___x_1709_ = l_StateRefT_x27_instMonad___redArg(v___x_1708_);
v_toApplicative_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v___x_1709_, 1);
lean_dec(v_unused_1742_);
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1741_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_toApplicative_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1741_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v_toFunctor_1714_; lean_object* v_toSeq_1715_; lean_object* v_toSeqLeft_1716_; lean_object* v_toSeqRight_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1739_; 
v_toFunctor_1714_ = lean_ctor_get(v_toApplicative_1710_, 0);
v_toSeq_1715_ = lean_ctor_get(v_toApplicative_1710_, 2);
v_toSeqLeft_1716_ = lean_ctor_get(v_toApplicative_1710_, 3);
v_toSeqRight_1717_ = lean_ctor_get(v_toApplicative_1710_, 4);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_toApplicative_1710_);
if (v_isSharedCheck_1739_ == 0)
{
lean_object* v_unused_1740_; 
v_unused_1740_ = lean_ctor_get(v_toApplicative_1710_, 1);
lean_dec(v_unused_1740_);
v___x_1719_ = v_toApplicative_1710_;
v_isShared_1720_ = v_isSharedCheck_1739_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_toSeqRight_1717_);
lean_inc(v_toSeqLeft_1716_);
lean_inc(v_toSeq_1715_);
lean_inc(v_toFunctor_1714_);
lean_dec(v_toApplicative_1710_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1739_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___f_1721_; lean_object* v___f_1722_; lean_object* v___f_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___f_1726_; lean_object* v___f_1727_; lean_object* v___f_1728_; lean_object* v___x_1730_; 
v___f_1721_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__4));
v___f_1722_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___closed__5));
lean_inc_ref(v_toFunctor_1714_);
v___f_1723_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1723_, 0, v_toFunctor_1714_);
v___f_1724_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1724_, 0, v_toFunctor_1714_);
v___x_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1725_, 0, v___f_1723_);
lean_ctor_set(v___x_1725_, 1, v___f_1724_);
v___f_1726_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1726_, 0, v_toSeqRight_1717_);
v___f_1727_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1727_, 0, v_toSeqLeft_1716_);
v___f_1728_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1728_, 0, v_toSeq_1715_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 4, v___f_1726_);
lean_ctor_set(v___x_1719_, 3, v___f_1727_);
lean_ctor_set(v___x_1719_, 2, v___f_1728_);
lean_ctor_set(v___x_1719_, 1, v___f_1721_);
lean_ctor_set(v___x_1719_, 0, v___x_1725_);
v___x_1730_ = v___x_1719_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___f_1721_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v___f_1728_);
lean_ctor_set(v_reuseFailAlloc_1738_, 3, v___f_1727_);
lean_ctor_set(v_reuseFailAlloc_1738_, 4, v___f_1726_);
v___x_1730_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1732_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v___f_1722_);
lean_ctor_set(v___x_1712_, 0, v___x_1730_);
v___x_1732_ = v___x_1712_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___f_1722_);
v___x_1732_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_2921__overap_1735_; lean_object* v___x_1736_; 
v___x_1733_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
v___x_1734_ = l_instInhabitedOfMonad___redArg(v___x_1732_, v___x_1733_);
v___x_2921__overap_1735_ = lean_panic_fn_borrowed(v___x_1734_, v_msg_1687_);
lean_dec(v___x_1734_);
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
lean_inc_ref(v___y_1688_);
v___x_1736_ = lean_apply_5(v___x_2921__overap_1735_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, lean_box(0));
return v___x_1736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1___boxed(lean_object* v_msg_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v_msg_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1749_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3(void){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1753_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__2));
v___x_1754_ = lean_unsigned_to_nat(53u);
v___x_1755_ = lean_unsigned_to_nat(62u);
v___x_1756_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__1));
v___x_1757_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__0));
v___x_1758_ = l_mkPanicMessageWithDecl(v___x_1757_, v___x_1756_, v___x_1755_, v___x_1754_, v___x_1753_);
return v___x_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(size_t v_sz_1759_, size_t v_i_1760_, lean_object* v_bs_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_usize_dec_lt(v_i_1760_, v_sz_1759_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_bs_1761_);
return v___x_1768_;
}
else
{
lean_object* v_v_1769_; lean_object* v___x_1770_; 
v_v_1769_ = lean_array_uget_borrowed(v_bs_1761_, v_i_1760_);
lean_inc(v_v_1769_);
v___x_1770_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_v_1769_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; lean_object* v_bs_x27_1773_; lean_object* v_a_1775_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = lean_unsigned_to_nat(0u);
v_bs_x27_1773_ = lean_array_uset(v_bs_1761_, v_i_1760_, v___x_1772_);
if (lean_obj_tag(v_a_1771_) == 6)
{
lean_object* v_val_1780_; lean_object* v_numFields_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; 
v_val_1780_ = lean_ctor_get(v_a_1771_, 0);
lean_inc_ref(v_val_1780_);
lean_dec_ref_known(v_a_1771_, 1);
v_numFields_1781_ = lean_ctor_get(v_val_1780_, 4);
lean_inc(v_numFields_1781_);
lean_dec_ref(v_val_1780_);
v___x_1782_ = 0;
v___x_1783_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1783_, 0, v_numFields_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1772_);
lean_ctor_set_uint8(v___x_1783_, sizeof(void*)*2, v___x_1782_);
v_a_1775_ = v___x_1783_;
goto v___jp_1774_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec(v_a_1771_);
v___x_1784_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___closed__3);
v___x_1785_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__1(v___x_1784_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v_a_1775_ = v_a_1786_;
goto v___jp_1774_;
}
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec_ref(v_bs_x27_1773_);
v_a_1787_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1785_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1785_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
v___jp_1774_:
{
size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = ((size_t)1ULL);
v___x_1777_ = lean_usize_add(v_i_1760_, v___x_1776_);
v___x_1778_ = lean_array_uset(v_bs_x27_1773_, v_i_1760_, v_a_1775_);
v_i_1760_ = v___x_1777_;
v_bs_1761_ = v___x_1778_;
goto _start;
}
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec_ref(v_bs_1761_);
v_a_1795_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1770_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1770_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3___boxed(lean_object* v_sz_1803_, lean_object* v_i_1804_, lean_object* v_bs_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
size_t v_sz_boxed_1811_; size_t v_i_boxed_1812_; lean_object* v_res_1813_; 
v_sz_boxed_1811_ = lean_unbox_usize(v_sz_1803_);
lean_dec(v_sz_1803_);
v_i_boxed_1812_ = lean_unbox_usize(v_i_1804_);
lean_dec(v_i_1804_);
v_res_1813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_boxed_1811_, v_i_boxed_1812_, v_bs_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_);
lean_dec(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec(v___y_1807_);
lean_dec_ref(v___y_1806_);
return v_res_1813_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1814_; lean_object* v_dummy_1815_; 
v___x_1814_ = lean_box(0);
v_dummy_1815_ = l_Lean_Expr_sort___override(v___x_1814_);
return v_dummy_1815_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_box(0);
v___x_1817_ = lean_unsigned_to_nat(16u);
v___x_1818_ = lean_mk_array(v___x_1817_, v___x_1816_);
return v___x_1818_;
}
}
static lean_object* _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__1);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v___x_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(lean_object* v_e_1824_, uint8_t v_alsoCasesOn_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
uint8_t v___x_1834_; 
v___x_1834_ = l_Lean_Expr_isApp(v_e_1824_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
lean_dec_ref(v_e_1824_);
v___x_1835_ = lean_box(0);
v___x_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
return v___x_1836_;
}
else
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lean_Expr_getAppFn(v_e_1824_);
if (lean_obj_tag(v___x_1837_) == 4)
{
lean_object* v_declName_1838_; lean_object* v_us_1839_; lean_object* v___x_1840_; lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1995_; 
v_declName_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc_n(v_declName_1838_, 2);
v_us_1839_ = lean_ctor_get(v___x_1837_, 1);
lean_inc(v_us_1839_);
lean_dec_ref_known(v___x_1837_, 2);
v___x_1840_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_1838_, v___y_1829_);
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1995_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1995_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
if (lean_obj_tag(v_a_1841_) == 1)
{
lean_object* v_val_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1887_; 
v_val_1845_ = lean_ctor_get(v_a_1841_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_a_1841_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1847_ = v_a_1841_;
v_isShared_1848_ = v_isSharedCheck_1887_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_val_1845_);
lean_dec(v_a_1841_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1887_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_dummy_1849_; lean_object* v_nargs_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v_args_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; 
v_dummy_1849_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
v_nargs_1850_ = l_Lean_Expr_getAppNumArgs(v_e_1824_);
lean_inc(v_nargs_1850_);
v___x_1851_ = lean_mk_array(v_nargs_1850_, v_dummy_1849_);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_sub(v_nargs_1850_, v___x_1852_);
lean_dec(v_nargs_1850_);
v_args_1854_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1824_, v___x_1851_, v___x_1853_);
v___x_1855_ = lean_array_get_size(v_args_1854_);
v___x_1856_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_1845_);
v___x_1857_ = lean_nat_dec_lt(v___x_1855_, v___x_1856_);
lean_dec(v___x_1856_);
if (v___x_1857_ == 0)
{
lean_object* v_numParams_1858_; lean_object* v_numDiscrs_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v_numParams_1858_ = lean_ctor_get(v_val_1845_, 0);
v_numDiscrs_1859_ = lean_ctor_get(v_val_1845_, 1);
v___x_1860_ = lean_array_mk(v_us_1839_);
v___x_1861_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1858_);
v___x_1862_ = l_Array_extract___redArg(v_args_1854_, v___x_1861_, v_numParams_1858_);
v___x_1863_ = l_Lean_instInhabitedExpr;
v___x_1864_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_1845_);
v___x_1865_ = lean_array_get(v___x_1863_, v_args_1854_, v___x_1864_);
lean_dec(v___x_1864_);
v___x_1866_ = lean_nat_add(v_numParams_1858_, v___x_1852_);
v___x_1867_ = lean_nat_add(v___x_1866_, v_numDiscrs_1859_);
lean_inc(v___x_1867_);
lean_inc_ref_n(v_args_1854_, 2);
v___x_1868_ = l_Array_toSubarray___redArg(v_args_1854_, v___x_1866_, v___x_1867_);
v___x_1869_ = l_Subarray_copy___redArg(v___x_1868_);
v___x_1870_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_1845_);
v___x_1871_ = lean_nat_add(v___x_1867_, v___x_1870_);
lean_dec(v___x_1870_);
lean_inc(v___x_1871_);
v___x_1872_ = l_Array_toSubarray___redArg(v_args_1854_, v___x_1867_, v___x_1871_);
v___x_1873_ = l_Subarray_copy___redArg(v___x_1872_);
v___x_1874_ = l_Array_toSubarray___redArg(v_args_1854_, v___x_1871_, v___x_1855_);
v___x_1875_ = l_Subarray_copy___redArg(v___x_1874_);
v___x_1876_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1876_, 0, v_val_1845_);
lean_ctor_set(v___x_1876_, 1, v_declName_1838_);
lean_ctor_set(v___x_1876_, 2, v___x_1860_);
lean_ctor_set(v___x_1876_, 3, v___x_1862_);
lean_ctor_set(v___x_1876_, 4, v___x_1865_);
lean_ctor_set(v___x_1876_, 5, v___x_1869_);
lean_ctor_set(v___x_1876_, 6, v___x_1873_);
lean_ctor_set(v___x_1876_, 7, v___x_1875_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 0, v___x_1876_);
v___x_1878_ = v___x_1847_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1880_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1878_);
v___x_1880_ = v___x_1843_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1885_; 
lean_dec_ref(v_args_1854_);
lean_del_object(v___x_1847_);
lean_dec(v_val_1845_);
lean_dec(v_us_1839_);
lean_dec(v_declName_1838_);
v___x_1883_ = lean_box(0);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 0, v___x_1883_);
v___x_1885_ = v___x_1843_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
else
{
lean_object* v___x_1888_; 
lean_del_object(v___x_1843_);
lean_dec(v_a_1841_);
v___x_1888_ = lean_st_ref_get(v___y_1829_);
if (v_alsoCasesOn_1825_ == 0)
{
lean_dec(v___x_1888_);
lean_dec(v_us_1839_);
lean_dec(v_declName_1838_);
lean_dec_ref(v_e_1824_);
goto v___jp_1831_;
}
else
{
lean_object* v_env_1889_; uint8_t v___x_1890_; 
v_env_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc_ref(v_env_1889_);
lean_dec(v___x_1888_);
lean_inc(v_declName_1838_);
v___x_1890_ = l_Lean_isCasesOnRecursor(v_env_1889_, v_declName_1838_);
if (v___x_1890_ == 0)
{
lean_dec(v_us_1839_);
lean_dec(v_declName_1838_);
lean_dec_ref(v_e_1824_);
goto v___jp_1831_;
}
else
{
lean_object* v_indName_1891_; lean_object* v___x_1892_; 
v_indName_1891_ = l_Lean_Name_getPrefix(v_declName_1838_);
v___x_1892_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0(v_indName_1891_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1986_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1895_ = v___x_1892_;
v_isShared_1896_ = v_isSharedCheck_1986_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1892_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1986_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
if (lean_obj_tag(v_a_1893_) == 5)
{
lean_object* v_val_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1981_; 
v_val_1897_ = lean_ctor_get(v_a_1893_, 0);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_a_1893_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1899_ = v_a_1893_;
v_isShared_1900_ = v_isSharedCheck_1981_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_val_1897_);
lean_dec(v_a_1893_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1981_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_toConstantVal_1901_; lean_object* v_numParams_1902_; lean_object* v_numIndices_1903_; lean_object* v_ctors_1904_; lean_object* v_nargs_1905_; lean_object* v_dummy_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v_args_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v_toConstantVal_1901_ = lean_ctor_get(v_val_1897_, 0);
lean_inc_ref(v_toConstantVal_1901_);
v_numParams_1902_ = lean_ctor_get(v_val_1897_, 1);
lean_inc(v_numParams_1902_);
v_numIndices_1903_ = lean_ctor_get(v_val_1897_, 2);
lean_inc(v_numIndices_1903_);
v_ctors_1904_ = lean_ctor_get(v_val_1897_, 4);
lean_inc(v_ctors_1904_);
v_nargs_1905_ = l_Lean_Expr_getAppNumArgs(v_e_1824_);
v_dummy_1906_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__0);
lean_inc(v_nargs_1905_);
v___x_1907_ = lean_mk_array(v_nargs_1905_, v_dummy_1906_);
v___x_1908_ = lean_unsigned_to_nat(1u);
v___x_1909_ = lean_nat_sub(v_nargs_1905_, v___x_1908_);
lean_dec(v_nargs_1905_);
v_args_1910_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1824_, v___x_1907_, v___x_1909_);
v___x_1911_ = lean_nat_add(v_numParams_1902_, v___x_1908_);
v___x_1912_ = lean_nat_add(v___x_1911_, v_numIndices_1903_);
v___x_1913_ = lean_nat_add(v___x_1912_, v___x_1908_);
lean_dec(v___x_1912_);
v___x_1914_ = l_Lean_InductiveVal_numCtors(v_val_1897_);
lean_dec_ref(v_val_1897_);
v___x_1915_ = lean_nat_add(v___x_1913_, v___x_1914_);
lean_dec(v___x_1914_);
v___x_1916_ = lean_array_get_size(v_args_1910_);
v___x_1917_ = lean_nat_dec_le(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1920_; 
lean_dec(v___x_1915_);
lean_dec(v___x_1913_);
lean_dec(v___x_1911_);
lean_dec_ref(v_args_1910_);
lean_dec(v_ctors_1904_);
lean_dec(v_numIndices_1903_);
lean_dec(v_numParams_1902_);
lean_dec_ref(v_toConstantVal_1901_);
lean_del_object(v___x_1899_);
lean_dec(v_us_1839_);
lean_dec(v_declName_1838_);
v___x_1918_ = lean_box(0);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1918_);
v___x_1920_ = v___x_1895_;
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
else
{
lean_object* v___x_1922_; lean_object* v_params_1923_; lean_object* v___x_1924_; lean_object* v_motive_1925_; lean_object* v_discrs_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v_discrInfos_1929_; lean_object* v_alts_1930_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v_lower_1972_; lean_object* v_upper_1973_; uint8_t v___x_1980_; 
lean_del_object(v___x_1895_);
v___x_1922_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1902_);
lean_inc_ref_n(v_args_1910_, 3);
v_params_1923_ = l_Array_toSubarray___redArg(v_args_1910_, v___x_1922_, v_numParams_1902_);
v___x_1924_ = l_Lean_instInhabitedExpr;
v_motive_1925_ = lean_array_get(v___x_1924_, v_args_1910_, v_numParams_1902_);
lean_dec(v_numParams_1902_);
lean_inc(v___x_1913_);
v_discrs_1926_ = l_Array_toSubarray___redArg(v_args_1910_, v___x_1911_, v___x_1913_);
v___x_1927_ = lean_nat_add(v_numIndices_1903_, v___x_1908_);
lean_dec(v_numIndices_1903_);
v___x_1928_ = lean_box(0);
v_discrInfos_1929_ = lean_mk_array(v___x_1927_, v___x_1928_);
lean_inc(v___x_1915_);
v_alts_1930_ = l_Array_toSubarray___redArg(v_args_1910_, v___x_1913_, v___x_1915_);
v___x_1980_ = lean_nat_dec_le(v___x_1915_, v___x_1922_);
if (v___x_1980_ == 0)
{
v_lower_1972_ = v___x_1915_;
v_upper_1973_ = v___x_1916_;
goto v___jp_1971_;
}
else
{
lean_dec(v___x_1915_);
v_lower_1972_ = v___x_1922_;
v_upper_1973_ = v___x_1916_;
goto v___jp_1971_;
}
v___jp_1931_:
{
lean_object* v___x_1934_; size_t v_sz_1935_; size_t v___x_1936_; lean_object* v___x_1937_; 
v___x_1934_ = lean_array_mk(v_ctors_1904_);
v_sz_1935_ = lean_array_size(v___x_1934_);
v___x_1936_ = ((size_t)0ULL);
v___x_1937_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__3(v_sz_1935_, v___x_1936_, v___x_1934_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1962_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1962_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1962_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_start_1942_; lean_object* v_stop_1943_; lean_object* v_start_1944_; lean_object* v_stop_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v_start_1942_ = lean_ctor_get(v_params_1923_, 1);
lean_inc(v_start_1942_);
v_stop_1943_ = lean_ctor_get(v_params_1923_, 2);
lean_inc(v_stop_1943_);
v_start_1944_ = lean_ctor_get(v_discrs_1926_, 1);
lean_inc(v_start_1944_);
v_stop_1945_ = lean_ctor_get(v_discrs_1926_, 2);
lean_inc(v_stop_1945_);
v___x_1946_ = lean_nat_sub(v_stop_1943_, v_start_1942_);
lean_dec(v_start_1942_);
lean_dec(v_stop_1943_);
v___x_1947_ = lean_nat_sub(v_stop_1945_, v_start_1944_);
lean_dec(v_start_1944_);
lean_dec(v_stop_1945_);
v___x_1948_ = lean_obj_once(&l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2, &l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2_once, _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__2);
v___x_1949_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1946_);
lean_ctor_set(v___x_1949_, 1, v___x_1947_);
lean_ctor_set(v___x_1949_, 2, v_a_1938_);
lean_ctor_set(v___x_1949_, 3, v___y_1933_);
lean_ctor_set(v___x_1949_, 4, v_discrInfos_1929_);
lean_ctor_set(v___x_1949_, 5, v___x_1948_);
v___x_1950_ = lean_array_mk(v_us_1839_);
v___x_1951_ = l_Subarray_copy___redArg(v_params_1923_);
v___x_1952_ = l_Subarray_copy___redArg(v_discrs_1926_);
v___x_1953_ = l_Subarray_copy___redArg(v_alts_1930_);
v___x_1954_ = l_Subarray_copy___redArg(v___y_1932_);
v___x_1955_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1949_);
lean_ctor_set(v___x_1955_, 1, v_declName_1838_);
lean_ctor_set(v___x_1955_, 2, v___x_1950_);
lean_ctor_set(v___x_1955_, 3, v___x_1951_);
lean_ctor_set(v___x_1955_, 4, v_motive_1925_);
lean_ctor_set(v___x_1955_, 5, v___x_1952_);
lean_ctor_set(v___x_1955_, 6, v___x_1953_);
lean_ctor_set(v___x_1955_, 7, v___x_1954_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set_tag(v___x_1899_, 1);
lean_ctor_set(v___x_1899_, 0, v___x_1955_);
v___x_1957_ = v___x_1899_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
lean_object* v___x_1959_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 0, v___x_1957_);
v___x_1959_ = v___x_1940_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v___y_1933_);
lean_dec_ref(v___y_1932_);
lean_dec_ref(v_alts_1930_);
lean_dec_ref(v_discrInfos_1929_);
lean_dec_ref(v_discrs_1926_);
lean_dec(v_motive_1925_);
lean_dec_ref(v_params_1923_);
lean_del_object(v___x_1899_);
lean_dec(v_us_1839_);
lean_dec(v_declName_1838_);
v_a_1963_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1937_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1937_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
v___jp_1971_:
{
lean_object* v_levelParams_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_levelParams_1974_ = lean_ctor_get(v_toConstantVal_1901_, 1);
lean_inc(v_levelParams_1974_);
lean_dec_ref(v_toConstantVal_1901_);
v___x_1975_ = l_Array_toSubarray___redArg(v_args_1910_, v_lower_1972_, v_upper_1973_);
v___x_1976_ = l_List_lengthTR___redArg(v_levelParams_1974_);
lean_dec(v_levelParams_1974_);
v___x_1977_ = l_List_lengthTR___redArg(v_us_1839_);
v___x_1978_ = lean_nat_dec_eq(v___x_1976_, v___x_1977_);
lean_dec(v___x_1977_);
lean_dec(v___x_1976_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
v___x_1979_ = ((lean_object*)(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___closed__3));
v___y_1932_ = v___x_1975_;
v___y_1933_ = v___x_1979_;
goto v___jp_1931_;
}
else
{
v___y_1932_ = v___x_1975_;
v___y_1933_ = v___x_1928_;
goto v___jp_1931_;
}
}
}
}
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1984_; 
lean_dec(v_a_1893_);
lean_dec(v_us_1839_);
lean_dec(v_declName_1838_);
lean_dec_ref(v_e_1824_);
v___x_1982_ = lean_box(0);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 0, v___x_1982_);
v___x_1984_ = v___x_1895_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec(v_us_1839_);
lean_dec(v_declName_1838_);
lean_dec_ref(v_e_1824_);
v_a_1987_ = lean_ctor_get(v___x_1892_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1892_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1892_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
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
lean_dec_ref(v___x_1837_);
lean_dec_ref(v_e_1824_);
goto v___jp_1831_;
}
}
v___jp_1831_:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0___boxed(lean_object* v_e_1996_, lean_object* v_alsoCasesOn_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
uint8_t v_alsoCasesOn_boxed_2003_; lean_object* v_res_2004_; 
v_alsoCasesOn_boxed_2003_ = lean_unbox(v_alsoCasesOn_1997_);
v_res_2004_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_1996_, v_alsoCasesOn_boxed_2003_, v___y_1998_, v___y_1999_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(lean_object* v_e_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2011_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2012_ = l_Lean_Expr_isAppOf(v_e_2005_, v___x_2011_);
if (v___x_2012_ == 0)
{
lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2013_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2014_ = l_Lean_Expr_isAppOf(v_e_2005_, v___x_2013_);
if (v___x_2014_ == 0)
{
uint8_t v___x_2015_; lean_object* v___x_2016_; 
v___x_2015_ = 1;
v___x_2016_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0(v_e_2005_, v___x_2015_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2037_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2037_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2037_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
if (lean_obj_tag(v_a_2017_) == 1)
{
lean_object* v_val_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2032_; 
v_val_2021_ = lean_ctor_get(v_a_2017_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_a_2017_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2023_ = v_a_2017_;
v_isShared_2024_ = v_isSharedCheck_2032_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_val_2021_);
lean_dec(v_a_2017_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2032_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2025_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2025_, 0, v_val_2021_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2025_);
v___x_2027_ = v___x_2023_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2027_);
v___x_2029_ = v___x_2019_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
lean_dec(v_a_2017_);
v___x_2033_ = lean_box(0);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2033_);
v___x_2035_ = v___x_2019_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
v_a_2038_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_2016_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2016_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_e_2005_);
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
v___x_2048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2047_);
return v___x_2048_;
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2049_, 0, v_e_2005_);
v___x_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2050_, 0, v___x_2049_);
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
return v___x_2051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_getSplitInfo_x3f___boxed(lean_object* v_e_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Lean_Elab_Tactic_Do_getSplitInfo_x3f(v_e_2052_, v_a_2053_, v_a_2054_, v_a_2055_, v_a_2056_);
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(lean_object* v_declName_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___redArg(v_declName_2059_, v___y_2063_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2___boxed(lean_object* v_declName_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__2(v_declName_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2073_, lean_object* v_constName_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___redArg(v_constName_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2081_, lean_object* v_constName_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1(v_00_u03b1_2081_, v_constName_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
lean_dec(v___y_2086_);
lean_dec_ref(v___y_2085_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b1_2089_, lean_object* v_ref_2090_, lean_object* v_constName_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_2090_, v_constName_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b1_2098_, lean_object* v_ref_2099_, lean_object* v_constName_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_2098_, v_ref_2099_, v_constName_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v_ref_2099_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(lean_object* v_00_u03b1_2107_, lean_object* v_ref_2108_, lean_object* v_msg_2109_, lean_object* v_declHint_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_2108_, v_msg_2109_, v_declHint_2110_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b1_2117_, lean_object* v_ref_2118_, lean_object* v_msg_2119_, lean_object* v_declHint_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_2117_, v_ref_2118_, v_msg_2119_, v_declHint_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v_ref_2118_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(lean_object* v_msg_2127_, lean_object* v_declHint_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___redArg(v_msg_2127_, v_declHint_2128_, v___y_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_msg_2135_, lean_object* v_declHint_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__7_spec__8(v_msg_2135_, v_declHint_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(lean_object* v_00_u03b1_2143_, lean_object* v_ref_2144_, lean_object* v_msg_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___redArg(v_ref_2144_, v_msg_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8___boxed(lean_object* v_00_u03b1_2152_, lean_object* v_ref_2153_, lean_object* v_msg_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8(v_00_u03b1_2152_, v_ref_2153_, v_msg_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v_ref_2153_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(lean_object* v_00_u03b1_2161_, lean_object* v_msg_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v_msg_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___boxed(lean_object* v_00_u03b1_2169_, lean_object* v_msg_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10(v_00_u03b1_2169_, v_msg_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec(v___y_2172_);
lean_dec_ref(v___y_2171_);
return v_res_2176_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2178_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__0));
v___x_2179_ = l_Lean_stringToMessageData(v___x_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher(lean_object* v_idx_2180_, lean_object* v_e_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v___y_2188_; uint8_t v___y_2207_; lean_object* v___x_2217_; uint8_t v___x_2218_; 
v___x_2217_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__0___closed__1));
v___x_2218_ = l_Lean_Expr_isAppOf(v_e_2181_, v___x_2217_);
if (v___x_2218_ == 0)
{
lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2219_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_SplitInfo_withAbstract___redArg___lam__6___closed__1));
v___x_2220_ = l_Lean_Expr_isAppOf(v_e_2181_, v___x_2219_);
v___y_2207_ = v___x_2220_;
goto v___jp_2206_;
}
else
{
v___y_2207_ = v___x_2218_;
goto v___jp_2206_;
}
v___jp_2187_:
{
lean_object* v___x_2189_; 
lean_inc_ref(v___y_2188_);
v___x_2189_ = l_Lean_Meta_findLocalDeclWithType_x3f(v___y_2188_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref_known(v___x_2189_, 1);
if (lean_obj_tag(v_a_2190_) == 1)
{
lean_object* v_val_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec_ref(v___y_2188_);
v_val_2191_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_val_2191_);
lean_dec_ref_known(v_a_2190_, 1);
v___x_2192_ = l_Lean_mkFVar(v_val_2191_);
v___x_2193_ = l_Lean_Meta_rwIfWith(v___x_2192_, v_e_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_dec(v_a_2190_);
lean_dec_ref(v_e_2181_);
v___x_2194_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1, &l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1_once, _init_l_Lean_Elab_Tactic_Do_rwIfOrMatcher___closed__1);
v___x_2195_ = l_Lean_MessageData_ofExpr(v___y_2188_);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___x_2197_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Elab_Tactic_Do_getSplitInfo_x3f_spec__0_spec__0_spec__1_spec__4_spec__6_spec__8_spec__10___redArg(v___x_2196_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2197_;
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec_ref(v___y_2188_);
lean_dec_ref(v_e_2181_);
v_a_2198_ = lean_ctor_get(v___x_2189_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2189_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2189_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2189_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
v___jp_2206_:
{
if (v___y_2207_ == 0)
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Meta_rwMatcher(v_idx_2180_, v_e_2181_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2208_;
}
else
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v_c_2213_; lean_object* v___x_2214_; uint8_t v___x_2215_; 
v___x_2209_ = lean_unsigned_to_nat(1u);
v___x_2210_ = l_Lean_Expr_getAppNumArgs(v_e_2181_);
v___x_2211_ = lean_nat_sub(v___x_2210_, v___x_2209_);
lean_dec(v___x_2210_);
v___x_2212_ = lean_nat_sub(v___x_2211_, v___x_2209_);
lean_dec(v___x_2211_);
v_c_2213_ = l_Lean_Expr_getRevArg_x21(v_e_2181_, v___x_2212_);
v___x_2214_ = lean_unsigned_to_nat(0u);
v___x_2215_ = lean_nat_dec_eq(v_idx_2180_, v___x_2214_);
lean_dec(v_idx_2180_);
if (v___x_2215_ == 0)
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_mkNot(v_c_2213_);
v___y_2188_ = v___x_2216_;
goto v___jp_2187_;
}
else
{
v___y_2188_ = v_c_2213_;
goto v___jp_2187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_rwIfOrMatcher___boxed(lean_object* v_idx_2221_, lean_object* v_e_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
lean_object* v_res_2228_; 
v_res_2228_ = l_Lean_Elab_Tactic_Do_rwIfOrMatcher(v_idx_2221_, v_e_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_);
lean_dec(v_a_2226_);
lean_dec_ref(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec_ref(v_a_2223_);
return v_res_2228_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherApp_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Array(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Split(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
